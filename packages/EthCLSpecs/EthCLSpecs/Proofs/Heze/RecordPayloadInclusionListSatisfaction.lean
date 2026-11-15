import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun

/-!
# Recording a payload's inclusion-list result

Heze records whether an execution payload contains the transactions required by
FOCIL. `recordPayloadInclusionListSatisfaction`:

1. reads the block at `root` and takes the slot before it, through the checked
   `Slot` subtract;
2. finds the shuffling dependent root that `root`'s chain fixes for that slot's epoch;
3. collects the timely inclusion-list transactions stored under that `(slot, dependent_root)`
   key, checks whether the payload satisfies them, and records the Boolean at `root`.

This module proves the complete `.run` equation of that function at
`ForkChoiceStoreRun (Store map)`.

There are two stores in the theorems:

- `store` is the explicit argument that the function updates and returns;
- `runnerStore` is the internal runner state used while the function runs.

`recordPayloadInclusionListSatisfaction_run` is the principal equation. A block missing from
`store.blocks` is the `missingKey root` error, and a slot-zero block underflows the checked
subtract, whose fault the run surfaces as the `.arithmetic` fault carrying the repr of the
exact `ArithFault`. Otherwise the result matches on the dependent-root walk: a walk error is
returned unchanged, and a successful walk returns `store` with
`payloadInclusionListSatisfaction[root]` set to `isInclusionListSatisfied payload ilTxs`,
paired with the walk's `postRunnerStore`. Here `ilTxs` is the pure
`getInclusionListTransactions` of the key, whose contents
`mem_getInclusionListTransactions_iff` describes.

At v1.7.0-beta.4 the function takes no `state`, and collecting the transactions cannot throw.
alpha.12 recomputed the committee from a state and could raise an empty-committee or a
missing-timeliness error; the corollaries that named those errors went with them.

The theorems do not prove that a subsequent lookup returns the recorded
value, because the generic `FcMap` interface does not provide an insert/lookup
law.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure run_liftM_error run_liftM_ok
  except_bind_error except_bind_ok run_throw)
open EthCLLib.Spec (HasherTag MapKind FcMap Checked ArithFault ExecutionEngine
  StoreTransitionError)
open EthCLSpecs.Heze (Preset Store Root Slot ExecutionPayload ExecutionRequests Transaction
  BeaconBlock recordPayloadInclusionListSatisfaction getShufflingDependentRoot
  getInclusionListTransactions isInclusionListSatisfied computeEpochAtSlot)

/-- Complete `.run` equation of `recordPayloadInclusionListSatisfaction`. A missing block is
`missingKey root`, and the previous-slot subtract is the checked `Slot` subtract the unit
flip produced: its fault surfaces as the `.arithmetic` fault carrying the repr of the exact
`ArithFault` (a slot-zero block underflows). Otherwise the result matches on the
dependent-root walk at the previous slot's epoch: an error is returned unchanged, and a
successful walk records `isInclusionListSatisfied payload ilTxs` at `root`, for the timely
transactions `ilTxs` stored under the walk's key, and keeps the walk's runner state. -/
@[characterizes EthCLSpecs.Heze.recordPayloadInclusionListSatisfaction]
theorem recordPayloadInclusionListSatisfaction_run
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload),
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root payload).run runnerStore =
        match FcMap.lookup store.blocks root with
        | none => .error (.missingKey root)
        | some block =>
          match (block.slot - 1 : Checked Slot) with
          | .error f => .error (.transition (.arithmetic (reprStr f)))
          | .ok slot =>
            match (getShufflingDependentRoot
                (StoreTransition := ForkChoiceStoreRun (Store map))
                store root (computeEpochAtSlot slot)).run runnerStore with
            | .error err => .error err
            | .ok (dependentRoot, postRunnerStore) =>
              .ok (
                { store with
                  payloadInclusionListSatisfaction :=
                    FcMap.insert store.payloadInclusionListSatisfaction root
                      (isInclusionListSatisfied payload
                        (getInclusionListTransactions store.inclusionListStore
                          slot dependentRoot (onlyTimely := true))) },
                postRunnerStore) := by
  intro store runnerStore root payload
  simp only [recordPayloadInclusionListSatisfaction, FcMap.getOrThrow, FcMap.getOrThrowKey]
  cases hblock : FcMap.lookup store.blocks root with
  | none =>
    simp [run_throw, except_bind_error]
  | some block =>
    -- `simp only []` beta-iota-reduces the get-or-throw match on `some block`.
    simp only []
    rw [run_bind, run_pure, except_bind_ok]
    rw [run_bind]
    cases hsub : (block.slot - 1 : Checked Slot) with
    | error f => rw [run_liftM_error, except_bind_error]; rfl
    | ok slot =>
      rw [run_liftM_ok, except_bind_ok]
      simp only []
      rw [run_bind]
      cases hdep : (getShufflingDependentRoot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root (computeEpochAtSlot slot)).run runnerStore with
      | error err => rw [except_bind_error]
      | ok p => rfl

/-- The successful branch of the principal equation. The block is present at a slot whose
checked predecessor binds, and the dependent-root walk has returned `dependentRoot` with
runner state `postRunnerStore`. Derived by rewriting with
`recordPayloadInclusionListSatisfaction_run`.

The recorded result may be either `true` or `false`. -/
theorem recordPayloadInclusionListSatisfaction_run_eq
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore postRunnerStore : Store map) (root : Root)
      (payload : ExecutionPayload) (block : BeaconBlock) (slot : Slot) (dependentRoot : Root),
      FcMap.lookup store.blocks root = some block →
      (block.slot - 1 : Checked Slot) = .ok slot →
      (getShufflingDependentRoot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root (computeEpochAtSlot slot)).run runnerStore
        = .ok (dependentRoot, postRunnerStore) →
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root payload).run runnerStore
        = .ok (
            { store with
              payloadInclusionListSatisfaction :=
                FcMap.insert store.payloadInclusionListSatisfaction root
                  (isInclusionListSatisfied payload
                    (getInclusionListTransactions store.inclusionListStore
                      slot dependentRoot (onlyTimely := true))) },
            postRunnerStore) := by
  intro store runnerStore postRunnerStore root payload block slot dependentRoot
    hblock hsub hdep
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hsub, hdep]

/-- A block missing from `store.blocks` is the `missingKey root` error: the spec's bare
`store.blocks[root]` read. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_missing_block
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload)
    (hblock : FcMap.lookup store.blocks root = none) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root payload).run runnerStore
      = .error (.missingKey root) := by
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock]

/-- Slot-zero checked-sub error: `store.blocks[root].slot - 1` underflows. Both `Sub`
routes the `Slot` type admits compute the same `ArithFault.range` fault for `0 - 1`, and
the run surfaces it as the `.arithmetic` fault carrying the repr of the exact fault. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_slot_zero
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload)
    (block : BeaconBlock)
    (hblock : FcMap.lookup store.blocks root = some block) (hslot : block.slot = 0) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root payload).run runnerStore
      = .error (.transition (.arithmetic
          (reprStr (ArithFault.range "-" 0 1)))) := by
  rw [recordPayloadInclusionListSatisfaction_run, hblock]
  simp only []
  have hsub : ((0 : Slot) - 1 : Checked Slot)
      = .error (ArithFault.range "-" 0 1) := by
    rfl
  rw [hslot, hsub]

/-- An error of the dependent-root walk is the recorder's error. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_dependent_root
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload)
    (block : BeaconBlock) (slot : Slot) (err : StoreTransitionError)
    (hblock : FcMap.lookup store.blocks root = some block)
    (hsub : (block.slot - 1 : Checked Slot) = .ok slot)
    (herr : (getShufflingDependentRoot
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root (computeEpochAtSlot slot)).run runnerStore
      = .error err) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root payload).run runnerStore
      = .error err := by
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hsub, herr]

end EthCLSpecs.Proofs.Heze
