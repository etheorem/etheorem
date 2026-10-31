import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun

/-!
# Recording a payload's inclusion-list result

Heze records whether an execution payload contains the transactions required by
FOCIL. `recordPayloadInclusionListSatisfaction`:

1. reads the block at `root` and takes the slot before it;
2. finds the shuffling dependent root that `root`'s chain fixes for that slot's epoch;
3. collects the timely inclusion-list transactions stored under that `(slot, dependent_root)`
   key, checks whether the payload satisfies them, and records the Boolean at `root`.

This module proves the complete `.run` equation of that function at
`ForkChoiceStoreRun (Store map)`.

There are two stores in the theorems:

- `store` is the explicit argument that the function updates and returns;
- `runnerStore` is the internal runner state used while the function runs.

`recordPayloadInclusionListSatisfaction_run` is the principal equation. A block missing from
`store.blocks` is the `missingKey root` error, and a slot-zero block is the checked-sub
arithmetic error. Otherwise the result matches on the dependent-root walk: a walk error is
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

open EthCLLib.Proofs (ForkChoiceStoreRun except_bind_error run_throw)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedSub ExecutionEngine
  StoreTransitionError)
open EthCLSpecs.Heze (Preset Store Root ExecutionPayload ExecutionRequests Transaction
  recordPayloadInclusionListSatisfaction getShufflingDependentRoot getInclusionListTransactions
  isInclusionListSatisfied computeEpochAtSlot)

/-- Complete `.run` equation of `recordPayloadInclusionListSatisfaction`. A missing block is
`missingKey root`, and a slot-zero block is the checked-sub arithmetic error. Otherwise the
result matches on the dependent-root walk at the previous slot's epoch: an error is returned
unchanged, and a successful walk records `isInclusionListSatisfied payload ilTxs` at `root`,
for the timely transactions `ilTxs` stored under the walk's key, and keeps the walk's runner
state. -/
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
          if block.slot = 0 then
            .error (.transition (.arithmetic
              "record_payload_inclusion_list_satisfaction: store.blocks[root].slot - 1"))
          else
            match (getShufflingDependentRoot
                (StoreTransition := ForkChoiceStoreRun (Store map))
                store root (computeEpochAtSlot (block.slot - 1))).run runnerStore with
            | .error err => .error err
            | .ok (dependentRoot, postRunnerStore) =>
              .ok (
                { store with
                  payloadInclusionListSatisfaction :=
                    FcMap.insert store.payloadInclusionListSatisfaction root
                      (isInclusionListSatisfied payload
                        (getInclusionListTransactions store.inclusionListStore
                          (block.slot - 1) dependentRoot (onlyTimely := true))) },
                postRunnerStore) := by
  intro store runnerStore root payload
  simp only [recordPayloadInclusionListSatisfaction, FcMap.getOrThrow, FcMap.getOrThrowKey]
  cases hblock : FcMap.lookup store.blocks root with
  | none =>
    simp [run_throw, except_bind_error]
  | some block =>
    by_cases hslot : block.slot = 0
    · simp [checkedSub, hslot, ForkChoiceStoreRun.throwArithmetic_run, except_bind_error]
    · simp [checkedSub, hslot]
      cases hdep : (getShufflingDependentRoot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root (computeEpochAtSlot (block.slot - 1))).run runnerStore with
      | error err =>
        rfl
      | ok p =>
        obtain ⟨dependentRoot, postRunnerStore⟩ := p
        rfl

/-- The successful branch of the principal equation. The block is present at a nonzero slot,
and the dependent-root walk has returned `dependentRoot` with runner state `postRunnerStore`.
Derived by rewriting with `recordPayloadInclusionListSatisfaction_run`.

The recorded result may be either `true` or `false`. -/
theorem recordPayloadInclusionListSatisfaction_run_eq
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore postRunnerStore : Store map) (root : Root)
      (payload : ExecutionPayload) (block : EthCLSpecs.Heze.BeaconBlock) (dependentRoot : Root),
      FcMap.lookup store.blocks root = some block →
      block.slot ≠ 0 →
      (getShufflingDependentRoot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root (computeEpochAtSlot (block.slot - 1))).run runnerStore
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
                      (block.slot - 1) dependentRoot (onlyTimely := true))) },
            postRunnerStore) := by
  intro store runnerStore postRunnerStore root payload block dependentRoot hblock hslot hdep
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hslot, hdep]

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

/-- Slot-zero checked-sub error: `store.blocks[root].slot - 1` underflows. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_slot_zero
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload)
    (block : EthCLSpecs.Heze.BeaconBlock)
    (hblock : FcMap.lookup store.blocks root = some block) (hslot : block.slot = 0) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root payload).run runnerStore
      = .error (.transition (.arithmetic
          "record_payload_inclusion_list_satisfaction: store.blocks[root].slot - 1")) := by
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hslot]

/-- An error of the dependent-root walk is the recorder's error. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_dependent_root
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload)
    (block : EthCLSpecs.Heze.BeaconBlock) (err : StoreTransitionError)
    (hblock : FcMap.lookup store.blocks root = some block) (hslot : block.slot ≠ 0)
    (herr : (getShufflingDependentRoot
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root (computeEpochAtSlot (block.slot - 1))).run runnerStore
      = .error err) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root payload).run runnerStore
      = .error err := by
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hslot, herr]

end EthCLSpecs.Proofs.Heze
