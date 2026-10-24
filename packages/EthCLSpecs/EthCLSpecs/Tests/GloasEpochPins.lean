import EthCLSpecs.Gloas.EpochProcessing
import EthCLLib.Proofs.StoreRun

/-!
# `EthCLSpecs.Tests.GloasEpochPins`: the builder-payment quorum product

`get_builder_payment_quorum_threshold` (`gloas/beacon-chain.md:891-897`) forms
`get_total_active_balance(state) // SLOTS_PER_EPOCH * BUILDER_PAYMENT_THRESHOLD_NUMERATOR` in
`uint64`. pyspec raises `ValueError` when the product overflows. The pins replay the two probe
rows of site j in `specs/2026-10-24-batchfaith-probes.md` (local, not committed): the pinned
pyspec with `SLOTS_PER_EPOCH = 1`, and the same `Preset` field here.

The model inlines the quorum at the start of `processBuilderPendingPayments`, before the
loop, so the pins run that substep. The minimal preset fixes `SLOTS_PER_EPOCH = 8`, so the
patch also restates the two `slotsPerEpoch` bound fields of the `Preset`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasEpochPins

open EthCLSpecs.Gloas
open EthCLLib.Proofs (pureState)

/-- The minimal preset with `SLOTS_PER_EPOCH = 1`. -/
@[reducible] private def oneSlot : Preset :=
  { minimal with slotsPerEpoch := 1, slotsPerEpochPos := by decide, slotsPerEpochLt := by decide }

/-- The SSZ list of `a`. The pin arrays are far below the list limit, so the empty-list branch
never runs. The branch exists because `runAt` takes its array as a variable. -/
private def listOf {α : Type} {cap : Nat} (a : Array α) : SSZList α cap :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], Nat.zero_le _⟩

/-- `process_builder_pending_payments` over a minimal Gloas state with one active validator per
entry of `effs`, at `SLOTS_PER_EPOCH = 1`, run in the proving monad (`StateT` over
`Except`). -/
private def runAt (effs : Array Gwei) :
    Except StateTransitionError (Unit × @State oneSlot fastHasherTag) :=
  letI : Preset := oneSlot
  letI : HasherTag := fastHasherTag
  let validators : Array Validator := effs.map fun e =>
    { (default : Validator) with
      effectiveBalance := e, exitEpoch := Const.farFutureEpoch,
      withdrawableEpoch := Const.farFutureEpoch }
  (processBuilderPendingPayments (StateTransition := StateT State (Except StateTransitionError))).run
    (pureState { (default : BeaconState) with
      validators := listOf validators
      balances := listOf (effs.map fun _ => (32000000000 : Gwei)) })

private def quorumDescr : String :=
  "get_builder_payment_quorum_threshold: per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR"

-- Overflow: a total of `2 ^ 62` over one slot, times 6, raises `ValueError`.
example : (match runAt #[4611686018427387904] with
    | .error (.arithmetic d) => d == quorumDescr
    | _ => false) = true := by native_decide

-- Order: two balances of `2 ^ 63` make the `get_total_balance` sum raise first.
example : (match runAt #[9223372036854775808, 9223372036854775808] with
    | .error (.arithmetic d) => d == "get_total_balance: sum of effective balances"
    | _ => false) = true := by native_decide

end EthCLSpecs.Tests.GloasEpochPins
