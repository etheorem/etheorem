import EthCLSpecs.Gloas
import EthCLSpecs.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Seeds.Gloas`: the Gloas author seeds

Author-written input terms (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4, §4.2), `[Preset]`-generic
so one definition serves every preset a named line lists: the command
elaborates each `with` term inside the theorem's telescope, where the
theorem's own instances fill the seed's instance binders. A seed that
fails the check is a build error, because the author claimed it works.

Two seeds serve the window theorems:

- `windowZero` / `windowEpoch` pin the window index to the smallest entry
  of the region the theorem's hypothesis names, where `default`'s `0`
  fails `_ge`'s bound.
- `activeState` replaces `default`'s empty, all-inactive validator set
  with 64 max-balance active validators. The default state drives
  `computePtcFromFulu`'s balance-weighted selection into its 10,000,000
  iteration fuel bound per empty committee (a valid state fills the
  selection within the bound, so the loop never spins), which makes the
  base source's default candidate unevaluatable for the window theorems;
  an active committee fills in a few dozen iterations.
-/

set_option autoImplicit false

open EthCLSpecs.Gloas (Preset)
open scoped EthCLSpecs.Gloas.Downgrade

namespace EthCLSpecs.TheoremVectors.Seeds.Gloas

/-- The smallest offset of `initializePtcWindow`'s first region: the window
index whose value is `0`, which `initializePtcWindow_lt`'s hypothesis
accepts. -/
def windowZero [Preset] : Fin (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  ⟨0, by
    have hp := EthCLSpecs.Gloas.Const.slotsPerEpochPos
    omega⟩

/-- The first offset of `initializePtcWindow`'s second region: the window
index whose value is `SLOTS_PER_EPOCH`, the smallest index the
`slotsPerEpoch ≤ i.val` hypothesis accepts. -/
def windowEpoch [Preset] : Fin (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  ⟨EthCLSpecs.Gloas.Const.slotsPerEpoch,
    by
      have hp := EthCLSpecs.Gloas.Const.slotsPerEpochPos
      omega⟩

/-- One active validator at the maximum effective balance: every draw of
the balance-weighted selection accepts it, so a committee of these fills
its target size in `size` iterations. The pubkey and credential are the
zero vectors, which the verify-off backend accepts. -/
def activeValidator [Preset] : EthCLSpecs.Fulu.Validator :=
  { pubkey := Vector.replicate 48 0
    withdrawalCredentials := Vector.replicate 32 0
    effectiveBalance := 32000000000
    slashed := false
    activationEligibilityEpoch := 0
    activationEpoch := 0
    exitEpoch := EthCLSpecs.Gloas.Const.farFutureEpoch
    withdrawableEpoch := EthCLSpecs.Gloas.Const.farFutureEpoch }

/-- The seed state for the window theorems: `default` with 64 active
validators and matching balances. A small active committee keeps the
spec's balance-weighted selection inside its fuel, which the default
state's empty validator set cannot. -/
def activeState [Preset] : EthCLSpecs.Fulu.BeaconState :=
  let v := activeValidator
  let vs : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Validator EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
    (Array.range 64).foldl (fun xs _ => xs.push v) default
  let bs : SizzLean.Repr.SSZList EthCLSpecs.Gloas.Gwei EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
    (Array.range 64).foldl (fun xs _ => xs.push 32000000000) default
  ({ (default : EthCLSpecs.Fulu.BeaconState) with validators := vs, balances := bs } :
    EthCLSpecs.Fulu.BeaconState)

end EthCLSpecs.TheoremVectors.Seeds.Gloas
