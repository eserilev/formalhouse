import CacheProofs
import EpochProofs.Equiv.EpochContexts

/-!
# `PreEpochCache::into_epoch_cache` cannot fail on mainnet

`into_epoch_cache` at the end of `process_epoch_single_pass` returns the error of
`base_rewards` and nothing else. `base_rewards_spec` (`CacheProofs.Equiv.EpochCache`) shows that
`base_rewards` returns `Ok` when the constants fit. `base_rewards_ok_mainnet` checks these
conditions for the mainnet constants after Electra: increment 1 ETH, maximum effective balance
2048 ETH, base reward factor 64 and 4 base rewards per epoch. The total active balance is any
value, because `base_rewards` floors it first.
-/

namespace EpochProofs.CacheBridge

open Aeneas Aeneas.Std Result

theorem base_rewards_ok_mainnet (total : U64) (phase0 : Bool) :
    ∃ tbl, types.state.base_rewards.base_rewards total 1000000000#u64 2048000000000#u64 64#u64
        4#u64 phase0 = ok (.Ok tbl) := by
  obtain ⟨tbl, h, _⟩ := CacheProofs.EpochCache.base_rewards_spec total 1000000000#u64 2048000000000#u64
    64#u64 4#u64 phase0 (by decide) (by decide) (by simp [U64.max_eq]) (by simp [U64.max_eq]) (by decide)
  exact ⟨tbl, h⟩

end EpochProofs.CacheBridge
