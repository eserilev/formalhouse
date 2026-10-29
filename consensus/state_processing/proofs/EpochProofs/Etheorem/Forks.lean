import ForkReplay

/-!
# The forks of the Etheorem epoch proofs

The epoch proofs in `EpochProofs/Etheorem/` hold for Gloas and for Fulu. A shared proof is written
once, in Gloas's names, inside `forkproof EpochEtheorem … end forkproof`. `ForkReplay` then
elaborates it for each fork below. The Gloas copy lives in `EpochProofs.Etheorem`, and the Fulu
copy in `EpochProofs.Etheorem.Fulu`.
-/

fork_family EpochEtheorem where
  | Gloas => EpochProofs.Etheorem
  | Fulu => EpochProofs.Etheorem.Fulu
