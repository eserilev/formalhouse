import Lean

/-!
# `ForkReplay`: write a proof once, elaborate it for every fork

Etheorem inherits a declaration by re-elaborating its raw syntax in each fork namespace. So
`EthCLSpecs.Fulu.f` and `EthCLSpecs.Gloas.f` are distinct constants, and a proof about one says
nothing about the other. A proof that reads the same for both forks, up to the fork name, still
has to exist once per fork. This module writes it once and elaborates it once per fork.

Two commands do the work.

* `fork_family F where | Gloas => A | Fulu => B` registers the family `F`. Each row names a fork
  token and the namespace where that fork's proofs live. The first row is the *template* fork: the
  shared text is written in its names.
* `forkproof F … end forkproof` takes the commands between the two keywords. For each fork of `F`,
  it opens the fork's namespace, elaborates a renamed copy of the commands, and closes the
  namespace.

Inside a `forkproof` block, `forkonly T … end forkonly` holds a part that only the fork `T` has, or
that reads differently for `T`. Its commands run only in `T`'s copy. They are renamed like the rest
of the block, which leaves a text written in `T`'s own names as it is. So a Fulu-only lemma is
written in Fulu's names, and a Gloas-only lemma in Gloas's.

The rename acts on identifiers only. In every name component that starts with the template token,
it replaces that prefix with the fork's token. With the template `Gloas` and the fork `Fulu`,
`EthCLSpecs.Gloas.getTotalActiveBalance` becomes `EthCLSpecs.Fulu.getTotalActiveBalance` and
`GloasRun` becomes `FuluRun`. A component that only contains the token later, such as
`churnLimitQuotientGloas`, keeps its name. Docstrings, strings, and numbers stay as written, so
shared docstrings should not name a fork.

Unqualified names resolve by ordinary name resolution in the fork's namespace. A shared lemma that
cites `foo` gets `Gloas`'s `foo` in the template namespace and `Fulu`'s `foo` in the Fulu
namespace, because Lean tries the innermost namespace first. This is late binding, as in
Etheorem's own `inherit`. So a shared proof that cites a lemma from a `forkonly` block gets each
fork's own version of it.

## Usage

The registry is data. A proof folder declares its family once, in a small module that its files
import:

```
import ForkReplay

fork_family EpochEtheorem where
  | Gloas => EpochProofs.Etheorem
  | Fulu => EpochProofs.Etheorem.Fulu
```

A file then writes its shared part once:

```
import EpochProofs.Etheorem.Forks

forkproof EpochEtheorem
open EthCLSpecs.Proofs.Gloas
variable [EthCLSpecs.Gloas.Preset]

theorem foo_run (s : EthCLSpecs.Gloas.State) : … := by …

forkonly Gloas
theorem ptc_run (s : EthCLSpecs.Gloas.State) : … := by …
end forkonly
end forkproof
```

This emits `EpochProofs.Etheorem.foo_run` about `EthCLSpecs.Gloas` and
`EpochProofs.Etheorem.Fulu.foo_run` about `EthCLSpecs.Fulu`, plus the Gloas-only
`EpochProofs.Etheorem.ptc_run`.

A new proof folder, for example block processing or fork choice, imports `ForkReplay` and
declares its own family with its own namespaces, such as
`| Gloas => BlockProofs.Etheorem | Fulu => BlockProofs.Etheorem.Fulu`. A new fork, such as Heze,
is one more row in each family. Neither needs a change to this module. Another Lake package
reaches the module by requiring this package and depending on the `ForkReplay` library.

## Rules for a shared block

* Use `forkproof` outside any `namespace`, since it opens each fork's namespace relative to the
  current one.
* The block parses as one command, before any command in it runs. So a `macro`, `syntax` or
  `notation` that the block uses goes above the block, and so does an `open` that brings scoped
  notation into view. An `open` of a fork namespace stays inside the block, where the rename
  applies to it. A tactic macro that names fork constants takes them as arguments, and
  `set_option hygiene false` lets its other names resolve where it runs. `finish_weigh` in
  `EpochProofs/Etheorem/Justification.lean` is an example.
* `section … end` pairs inside the block must balance. `end forkproof` closes the block. Each fork's
  copy runs in its own namespace scope, so `variable` and `open` lines inside the block end with
  it.
* A heading docstring (`/-! … -/`) inside the block appears once, with the template fork's copy.
* An error in a fork's copy points at the shared text, since the copy keeps the source positions.
  The message names the fork's constants, such as `EthCLSpecs.Fulu.State`.

## Lean idioms used here

* `registerSimplePersistentEnvExtension` builds an environment extension whose entries go into the
  `.olean`, so a family declared in one module is visible in every module that imports it.
  `initialize` creates the extension once, when the module loads.
* `Syntax.rewriteBottomUp` applies a function to every node of a syntax tree, children first.
* `!p` in a `syntax` rule is `notFollowedBy p`: the repetition of commands stops at `end forkproof`
  without consuming it. A plain `end` or `end Name` still parses as a command of the block.
-/

set_option autoImplicit false

namespace ForkReplay

open Lean Elab Command

/-- One fork of a family: its token, an atomic name such as `Gloas`, and the namespace that holds
that fork's copy of each shared proof. -/
structure Fork where
  token : Name
  ns : Name
  deriving Inhabited, Repr

/-- A family of forks. The first fork is the template: shared text is written in its names. -/
structure Family where
  name : Name
  forks : Array Fork
  deriving Inhabited

/-- The registry of families, by name. It persists in the `.olean`. -/
initialize familyExt : SimplePersistentEnvExtension Family (NameMap (Array Fork)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m f => m.insert f.name f.forks
    addImportedFn := fun ess =>
      ess.foldl (fun m es => es.foldl (fun m f => m.insert f.name f.forks) m) {}
  }

/-- Replace the prefix `tmpl` of one name component with `fork`. Other components stay. -/
def renameComponent (tmpl fork : String) (s : String) : String :=
  if s.startsWith tmpl then fork ++ String.ofList (s.toList.drop tmpl.length) else s

/-- Apply `renameComponent` to every component of a name. -/
def renameName (tmpl fork : String) : Name → Name
  | .str p s => .str (renameName tmpl fork p) (renameComponent tmpl fork s)
  | .num p n => .num (renameName tmpl fork p) n
  | .anonymous => .anonymous

/-- Rename every identifier in a command from the template fork to `fork`. The source positions
stay, so an error in a fork's copy points at the shared text. -/
def renameSyntax (tmpl fork : Name) (stx : Syntax) : Syntax :=
  if tmpl == fork then stx else
  let t := tmpl.toString
  let f := fork.toString
  stx.rewriteBottomUp fun
    | .ident info raw val pre => .ident info raw (renameName t f val) pre
    | s => s

/-- `fork_family F where | T₁ => N₁ | T₂ => N₂ …` registers the family `F`. Each row is a fork
token and the namespace for that fork's proofs. The first row is the template fork. -/
syntax (name := forkFamilyCmd)
  "fork_family " ident " where" (ppLine "| " ident " => " ident)+ : command

/-- `forkproof F … end forkproof` elaborates its commands once per fork of the family `F`, each copy
renamed to the fork's names and placed in the fork's namespace. -/
syntax (name := forkproofCmd)
  "forkproof " ident (ppLine !("end " "forkproof") command)* ppLine "end " "forkproof" : command

/-- `forkonly T₁ T₂ … end forkonly`, inside a `forkproof` block, elaborates its commands only in
the copies for the forks `T₁ T₂ …`. It holds the part of a proof that differs between forks. -/
syntax (name := forkonlyCmd)
  "forkonly " ident+ (ppLine !("end " "forkonly") command)* ppLine "end " "forkonly" : command

@[command_elab forkFamilyCmd]
def elabForkFamily : CommandElab
  | `(fork_family $name:ident where $[| $tokens:ident => $namespaces:ident]*) => do
    let forks ← (tokens.zip namespaces).mapM fun (tok, ns) => do
      unless tok.getId.isAtomic do
        throwErrorAt tok "a fork token must be one name component, such as `Gloas`"
      pure { token := tok.getId, ns := ns.getId : Fork }
    if (familyExt.getState (← getEnv)).contains name.getId then
      throwErrorAt name "the fork family `{name.getId}` is already declared"
    modifyEnv (familyExt.addEntry · { name := name.getId, forks })
  | _ => throwUnsupportedSyntax

/-- The commands of a `forkproof` or `forkonly` repetition. Each repetition can arrive wrapped in a
`group` node, with the command as its last child. -/
def blockCommands (rep : Syntax) : Array Syntax :=
  rep.getArgs.map fun a => if a.isOfKind groupKind then a.getArgs.back! else a

/-- Elaborate the commands of a block for one fork. A `forkonly` block runs only for the forks it
names. It recurses through nested `forkonly` blocks, which Lean cannot see as structural, so the
definition is `partial`. -/
partial def elabForFork (forks : Array Fork) (template fork : Fork) (cmds : Array Syntax) :
    CommandElabM Unit := do
  for cmd in cmds do
    if cmd.isOfKind ``forkonlyCmd then
      -- Read the fork tokens before any rename, so `forkonly Gloas` keeps its meaning.
      let tokens := cmd[1].getArgs
      for tok in tokens do
        unless forks.any (·.token == tok.getId) do
          throwErrorAt tok "`{tok.getId}` is not a fork of this family"
      if tokens.any (·.getId == fork.token) then
        elabForFork forks template fork (blockCommands cmd[2])
    else if fork.token != template.token && cmd.isOfKind ``Lean.Parser.Command.moduleDoc then
      -- A heading docstring would repeat in the module docs, so only the template emits it.
      continue
    else
      elabCommand (renameSyntax template.token fork.token cmd)

@[command_elab forkproofCmd]
def elabForkproof : CommandElab := fun stx => do
  -- `stx[1]` is the family name, `stx[2]` the repetition of commands.
  let famId := stx[1]
  let some forks := (familyExt.getState (← getEnv)).find? famId.getId
    | throwErrorAt famId "unknown fork family `{famId.getId}`; declare it with `fork_family`"
  let some template := forks[0]?
    | throwErrorAt famId "the fork family `{famId.getId}` has no forks"
  for fork in forks do
    let nsId := mkIdent fork.ns
    elabCommand (← `(namespace $nsId))
    elabForFork forks template fork (blockCommands stx[2])
    elabCommand (← `(end $nsId))

@[command_elab forkonlyCmd]
def elabForkonly : CommandElab := fun stx =>
  throwErrorAt stx "`forkonly` belongs inside a `forkproof` block"

end ForkReplay
