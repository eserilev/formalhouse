import CacheProofs
import EpochProofs.Etheorem.Final

/-!
# The cache proofs in the epoch proofs

`CacheProofs` (`consensus/types/proofs`) proves the BeaconState caches equal to its own spec
model. The epoch theorems take cache facts as hypotheses: the progressive balances totals, the
committee cache contents, the base reward and total active balance, the exit and activation
churn. The bridge lemmas from the cache theorems to these values are in `EpochProofs/CacheBridge/`.

This file imports both libraries, so the build checks that they load together.
-/
