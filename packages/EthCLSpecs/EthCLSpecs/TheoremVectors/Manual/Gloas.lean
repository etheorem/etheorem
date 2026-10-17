import EthCLLib.Spec
import EthCLSpecs.Gloas
import EthCLSpecs.Fulu
import EthCLSpecs.TheoremVectors.Builders.Gloas

/-!
# `EthCLSpecs.TheoremVectors.Manual.Gloas`: the Gloas manual terms

Author-written input terms (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4, §4.2), `[Preset]`-generic
so one definition serves every preset a named line lists: the command
elaborates each `with` term inside the theorem's telescope, where the
theorem's own instances fill the term's instance binders. A term that
fails the check is a build error, because the author claimed it works.

Two manual terms serve the window theorems:

- `windowZero` / `windowEpoch` pin the window index to the smallest entry
  of the region the theorem's hypothesis names, where `default`'s `0`
  fails `_ge`'s bound.
- `activeState` replaces `default`'s empty, all-inactive validator set
  with 64 max-balance active validators. The default state drives
  `computePtcFromFulu`'s balance-weighted selection into its 10,000,000
  iteration fuel bound per empty committee (a valid state fills the
  selection within the bound, so the loop never spins), which makes the
  base searcher's default candidate unevaluatable for the window theorems;
  an active committee fills in a few dozen iterations.

Two manual terms serve
`isValidIndexedPayloadAttestation_eq_true_iff_checks`:

- `iPacState` and `iPacAttestation` carry 64 validators and two in-range
  increasing attesting indices, so `isValidIndexedPayloadAttestation`'s
  true-side conjunction holds at the manual terms. The false-side
  disjuncts need containers the manual terms do not vary; the random
  searcher draws them (§9.2). `canBuilderCoverBid_iff` runs with no
  manual terms; the random searcher draws its state (§9.4).

One manual term serves `initiateBuilderExit_run_eq`:

- `builderState` is the `built` searcher's `withQueue` grid step (16
  validators, slot 40, four queued deposits, two builders onboarded by
  the spec's own onboarding step), so the theorem's in-range hypothesis
  holds at a registry the spec itself put there. The automatic search
  cannot witness the theorem: the hypothesis reads the builder index
  through `UInt64.toNat`, the one spelling the coupled walk and the
  solver's `UInt64`-comparison fragment do not bridge, so the search can
  neither couple the index to the built registry nor solve for it. The
  named line fixes the state and the index (`0`), and a complete
  assignment goes straight to the check.
-/

set_option autoImplicit false

open EthCLLib.Spec (CryptoBackend)
open EthCLSpecs.Gloas (Preset Config)
open scoped EthCLSpecs.Gloas.Downgrade

namespace EthCLSpecs.TheoremVectors.Manual.Gloas

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

/-- The manual state for the window theorems: `default` with 64 active
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

/-! ## The builder-registry manual state -/

/-- The manual state for `initiateBuilderExit_run_eq`: the `built`
searcher's `withQueue` grid step (16 validators, slot 40, queue 4), whose four queued
deposits drain through `onboardBuildersFromPendingDeposits` into a
two-builder registry. The theorem's in-range hypothesis holds at the
registry the spec's own onboarding step put there, and the named line
fixes the builder index `0` beside it. The crypto backend is the
binding's verify-off one, pinned locally the way the builders pin the
hasher, so the manual state carries only `[Preset] [Config]`, the binders
the theorem's telescope fills. -/
def builderState [Preset] [Config] : EthCLSpecs.Gloas.BeaconState :=
  letI : CryptoBackend := CryptoBackend.verifyOff
  EthCLSpecs.TheoremVectors.Builders.Gloas.withQueue
    { validators := 16, slot := 40, balance := 32000000000, queue := 4 }

/-! ## The payload-attestation manual terms -/

/-- A Gloas validator at the maximum effective balance, the registry entry
`iPacState` holds 64 of. The window theorems' `activeValidator` is the
Fulu one; Gloas re-declares its containers, so the manual attestation
carries its own. -/
def iPacValidator [Preset] : EthCLSpecs.Gloas.Validator :=
  { pubkey := Vector.replicate 48 0
    withdrawalCredentials := Vector.replicate 32 0
    effectiveBalance := 32000000000
    slashed := false
    activationEligibilityEpoch := 0
    activationEpoch := 0
    exitEpoch := EthCLSpecs.Gloas.Const.farFutureEpoch
    withdrawableEpoch := EthCLSpecs.Gloas.Const.farFutureEpoch }

/-- The manual state for `isValidIndexedPayloadAttestation_eq_true_iff_checks`:
64 registered validators, so indices `5` and `9` are in range. -/
def iPacState [Preset] : EthCLSpecs.Gloas.BeaconState :=
  let v := iPacValidator
  let vs : SizzLean.Repr.SSZList EthCLSpecs.Gloas.Validator
      EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
    (Array.range 64).foldl (fun xs _ => xs.push v) default
  { (default : EthCLSpecs.Gloas.BeaconState) with validators := vs }

/-- The manual attestation for `isValidIndexedPayloadAttestation_eq_true_iff_checks`:
two in-range increasing indices, so every gate holds and the true-side
conjunction is satisfiable at the manual terms. The signature is the zero
value, which the verify-off backend accepts. -/
def iPacAttestation [Preset] : EthCLSpecs.Gloas.IndexedPayloadAttestation :=
  let idx : SizzLean.Repr.SSZList EthCLSpecs.Gloas.ValidatorIndex
      EthCLSpecs.Gloas.Const.ptcSize :=
    ((default : SizzLean.Repr.SSZList EthCLSpecs.Gloas.ValidatorIndex
        EthCLSpecs.Gloas.Const.ptcSize).push 5).push 9
  { attestingIndices := idx, data := default, signature := default }

end EthCLSpecs.TheoremVectors.Manual.Gloas
