#!/usr/bin/env bash
# Regenerate CacheProofs/Generated.lean from the pure functions of the BeaconState caches.
#
# Needs Charon and Aeneas built at the pinned revisions. See README.md for the build steps
# and .github/workflows/lean-proofs.yml for the pins. Point CHARON and AENEAS at the binaries if
# they are not on PATH. The Aeneas binary is src/_build/default/main.exe in its checkout.
set -euo pipefail

CHARON=${CHARON:-charon}
AENEAS=${AENEAS:-aeneas}

proofs_dir=$(cd "$(dirname "$0")" && pwd)
crate_dir=$(dirname "$proofs_dir")
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

# `--include`: translate the bodies of these dependencies. Without it they become axioms.
# `-- --lib`: without it Charon translates the crate's binaries into opaque bodies.
(cd "$crate_dir" && "$CHARON" cargo --preset=aeneas \
  --start-from types::state::exit_queue \
  --start-from types::validator::activation_eligibility \
  --start-from types::state::total_active_balance \
  --start-from types::state::base_rewards \
  --start-from types::state::balance \
  --start-from types::state::participation_totals \
  --start-from types::state::committee_assignment \
  --start-from types::state::pubkey_index \
  --include safe_arith \
  --include swap_or_not_shuffle \
  --dest-file "$out/pure.llbc" -- --lib)

# Aeneas names the output after the llbc file.
"$AENEAS" -backend lean "$out/pure.llbc" -dest "$out"

# The lakefile turns off the Aeneas `do` notation. `Buf.new` does not compile with the standard
# `do`, so turn the Aeneas notation on for this function only.
buf_new='/-- [swap_or_not_shuffle::shuffle_list::{swap_or_not_shuffle::shuffle_list::Buf}::new]:'
if [ "$(grep -cFx -- "$buf_new" "$out/Pure.lean")" != 1 ]; then
  echo "error: expected the function Buf.new one time in the Aeneas output" >&2
  exit 1
fi
awk -v line="$buf_new" '$0 == line { print "set_option Aeneas.customDoElab true in" } { print }' \
  "$out/Pure.lean" > "$out/Pure.patched.lean"

mv "$out/Pure.patched.lean" "$proofs_dir/CacheProofs/Generated.lean"
echo "wrote $proofs_dir/CacheProofs/Generated.lean"
