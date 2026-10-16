import EthCLLib.Spec
import EthCLSpecs.Gloas
import EthCLSpecs.Fulu
import EthCLSpecs.TheoremVectors.Builders.Gloas

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

Two seeds serve `isValidIndexedPayloadAttestation_eq_true_iff_checks`:

- `iPacState` and `iPacAttestation` carry 64 validators and two in-range
  increasing attesting indices, so `isValidIndexedPayloadAttestation`'s
  true-side conjunction holds at the seed. The false-side cases need
  containers the seed does not vary; the random source draws them
  (§9.2). `canBuilderCoverBid_iff` runs seedless; the random source
  draws its state (§9.4).

One seed serves `initiateBuilderExit_run_eq`:

- `builderState` is the `built` source's `withQueue` grid step (16
  validators, slot 40, four queued deposits, two builders onboarded by
  the spec's own onboarding step), so the theorem's in-range hypothesis
  holds at a registry the spec itself put there. The automatic search
  cannot witness the theorem: the hypothesis reads the builder index
  through `UInt64.toNat`, the one spelling the coupled walk and the
  solver's `UInt64`-comparison fragment do not bridge, so the search can
  neither couple the index to the built registry nor solve for it. The
  named line seeds the state and the index (`0`), and a complete
  assignment goes straight to the check.
-/

set_option autoImplicit false

open EthCLLib.Spec (CryptoBackend)
open EthCLSpecs.Gloas (Preset Config)
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

/-! ## The builder-registry seed -/

/-- The seed state for `initiateBuilderExit_run_eq`: the `built` source's
`withQueue` grid step (16 validators, slot 40, queue 4), whose four queued
deposits drain through `onboardBuildersFromPendingDeposits` into a
two-builder registry. The theorem's in-range hypothesis holds at the
registry the spec's own onboarding step put there, and the named line
seeds the builder index `0` beside it. The crypto backend is the
binding's verify-off one, pinned locally the way the builders pin the
hasher, so the seed carries only `[Preset] [Config]`, the binders the
theorem's telescope fills. -/
def builderState [Preset] [Config] : EthCLSpecs.Gloas.BeaconState :=
  letI : CryptoBackend := CryptoBackend.verifyOff
  EthCLSpecs.TheoremVectors.Builders.Gloas.withQueue
    { validators := 16, slot := 40, balance := 32000000000, queue := 4 }

/-! ## The payload-attestation seeds -/

/-- A Gloas validator at the maximum effective balance, the registry entry
`iPacState` holds 64 of. The window theorems' `activeValidator` is the
Fulu one; Gloas re-declares its containers, so the attestation seed
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

/-- The seed state for `isValidIndexedPayloadAttestation_eq_true_iff_checks`:
64 registered validators, so indices `5` and `9` are in range. -/
def iPacState [Preset] : EthCLSpecs.Gloas.BeaconState :=
  let v := iPacValidator
  let vs : SizzLean.Repr.SSZList EthCLSpecs.Gloas.Validator
      EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
    (Array.range 64).foldl (fun xs _ => xs.push v) default
  { (default : EthCLSpecs.Gloas.BeaconState) with validators := vs }

/-- The seed attestation for `isValidIndexedPayloadAttestation_eq_true_iff_checks`:
two in-range increasing indices, so every gate holds and the true-side
conjunction is satisfiable at the seed. The signature is the zero value,
which the verify-off backend accepts. -/
def iPacAttestation [Preset] : EthCLSpecs.Gloas.IndexedPayloadAttestation :=
  let idx : SizzLean.Repr.SSZList EthCLSpecs.Gloas.ValidatorIndex
      EthCLSpecs.Gloas.Const.ptcSize :=
    ((default : SizzLean.Repr.SSZList EthCLSpecs.Gloas.ValidatorIndex
        EthCLSpecs.Gloas.Const.ptcSize).push 5).push 9
  { attestingIndices := idx, data := default, signature := default }

end EthCLSpecs.TheoremVectors.Seeds.Gloas
