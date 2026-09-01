import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLSpecs.Proofs.StoreRun

/-!
# Recording a payload's inclusion-list result

Heze records whether an execution payload contains the transactions required by
FOCIL. `recordPayloadInclusionListSatisfaction`:

1. collects the timely inclusion-list transactions for the previous slot;
2. checks whether the payload satisfies that list; and
3. records the resulting Boolean at the payload's block root.

This module proves the complete `.run` equation of that function at
`ForkChoiceStoreRun (Store map)`.

There are two stores in the theorems:

- `store` is the explicit argument that the function updates and returns;
- `runnerStore` is the internal runner state used while the function runs.

`recordPayloadInclusionListSatisfaction_run` is the principal equation. Slot
zero returns the checked-sub arithmetic error. Otherwise the result matches on
`getInclusionListTransactions` at the previous slot with `onlyTimely := true`.
A collector error is returned unchanged. A successful collection returns
`store` with `payloadInclusionListSatisfaction[root]` set to
`isInclusionListSatisfied payload ilTxs`, paired with the collector's
`postRunnerStore`.

The public corollaries name the error branches: slot zero, an arbitrary
collector error, an empty committee, and a missing timeliness key. The last
two follow from the collector theorems in
`Proofs/Heze/GetInclusionListTransactions.lean`.
`recordPayloadInclusionListSatisfaction_run_eq` restates the successful branch
with an arbitrary `postRunnerStore`.

The theorems do not prove that a subsequent lookup returns the recorded
value, because the generic `FcMap` interface does not provide an insert/lookup
law.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLSpecs.Proofs.Gloas (GloasRun)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedSub ExecutionEngine throwArithmetic
  StoreTransitionError htr)
open EthCLSpecs.Heze (Preset Store State Root ValidatorIndex
  ExecutionPayload ExecutionRequests Transaction recordPayloadInclusionListSatisfaction
  getInclusionListTransactions getInclusionListCommittee
  isInclusionListSatisfied getBeaconCommittee getCommitteeCountPerSlot computeEpochAtSlot)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)

/--
Suppose `state.slot` is nonzero and collecting the timely inclusion-list
transactions succeeds, returning `ilTxs` and runner state `postRunnerStore`.

Then `recordPayloadInclusionListSatisfaction`:

- returns `store` with the result of
  `isInclusionListSatisfied payload ilTxs` recorded at `root`; and
- leaves the runner state at `postRunnerStore`.

The recorded result may be either `true` or `false`.
-/
theorem recordPayloadInclusionListSatisfaction_run_eq
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore postRunnerStore : Store map)
      (state : State) (root : Root)
      (payload : ExecutionPayload) (ilTxs : Array Transaction),
      sszGet state slot ≠ 0 →
      (getInclusionListTransactions
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store.inclusionListStore state (sszGet state slot - 1)
          (onlyTimely := true)).run runnerStore
        = .ok (ilTxs, postRunnerStore) →
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store state root payload).run runnerStore
        = .ok (
            { store with
              payloadInclusionListSatisfaction :=
                FcMap.insert store.payloadInclusionListSatisfaction root
                  (isInclusionListSatisfied payload ilTxs) },
            postRunnerStore) := by
  intro store runnerStore postRunnerStore state root payload ilTxs hslot htxs
  -- Unfold the recorder, then apply `hslot` and `htxs`.
  simp [recordPayloadInclusionListSatisfaction, checkedSub, hslot, htxs]
  rfl

/-- `.run` of `throwArithmetic` at the fork-choice store runner. Closes by `rfl`
without unfolding `liftErr`. -/
private theorem throwArithmetic_run {σ α : Type} (descr : String) (s : σ) :
    (throwArithmetic (m := ForkChoiceStoreRun σ) (E := StoreTransitionError) descr
        : ForkChoiceStoreRun σ α).run s
      = .error (.transition (.arithmetic descr)) :=
  rfl

/-- Complete `.run` equation of `recordPayloadInclusionListSatisfaction`. Slot
zero is the checked-sub arithmetic error. Otherwise the result matches on
transaction collection: an error is returned unchanged, and a successful
collection records `isInclusionListSatisfied payload ilTxs` at `root` and
keeps the collector's runner state. -/
@[characterizes EthCLSpecs.Heze.recordPayloadInclusionListSatisfaction]
theorem recordPayloadInclusionListSatisfaction_run
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore : Store map) (state : State) (root : Root)
      (payload : ExecutionPayload),
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store state root payload).run runnerStore =
        if sszGet state slot = 0 then
          .error (.transition (.arithmetic
            "record_payload_inclusion_list_satisfaction: Slot(state.slot - 1)"))
        else
          match (getInclusionListTransactions
              (StoreTransition := ForkChoiceStoreRun (Store map))
              store.inclusionListStore state (sszGet state slot - 1)
              (onlyTimely := true)).run runnerStore with
          | .error err => .error err
          | .ok (ilTxs, postRunnerStore) =>
            .ok (
              { store with
                payloadInclusionListSatisfaction :=
                  FcMap.insert store.payloadInclusionListSatisfaction root
                    (isInclusionListSatisfied payload ilTxs) },
              postRunnerStore) := by
  intro store runnerStore state root payload
  by_cases hslot : sszGet state slot = 0
  · simp [recordPayloadInclusionListSatisfaction, checkedSub, hslot]
    have hthrow := throwArithmetic_run (α := UInt64)
      "record_payload_inclusion_list_satisfaction: Slot(state.slot - 1)" runnerStore
    rw [hthrow]
    exact GloasRun.except_bind_error _ _
  · simp [recordPayloadInclusionListSatisfaction, checkedSub, hslot]
    cases htxs : (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store.inclusionListStore state (sszGet state slot - 1)).run runnerStore with
    | error err =>
      rfl
    | ok p =>
      obtain ⟨ilTxs, postRunnerStore⟩ := p
      rfl

/-- Slot-zero checked-sub error. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_slot_zero
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (state : State) (root : Root)
    (payload : ExecutionPayload)
    (hslot : sszGet state slot = 0) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store state root payload).run runnerStore
      = .error (.transition (.arithmetic
          "record_payload_inclusion_list_satisfaction: Slot(state.slot - 1)")) := by
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hslot]

/-- An arbitrary transaction-collection error is the recorder's error. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_collect
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (state : State) (root : Root)
    (payload : ExecutionPayload) (err : StoreTransitionError)
    (hslot : sszGet state slot ≠ 0)
    (herr : (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store.inclusionListStore state (sszGet state slot - 1)
        (onlyTimely := true)).run runnerStore
      = .error err) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store state root payload).run runnerStore
      = .error err := by
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hslot, herr]

/-- Empty-committee arithmetic error, derived from the collector theorems. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_empty_committee
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (state : State) (root : Root)
    (payload : ExecutionPayload)
    (hslot : sszGet state slot ≠ 0)
    (hempty : ((Array.range (getCommitteeCountPerSlot state
        (computeEpochAtSlot (sszGet state slot - 1)))).foldl
        (fun acc i => acc ++ getBeaconCommittee state (sszGet state slot - 1) i)
        (#[] : Array ValidatorIndex)).size = 0) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store state root payload).run runnerStore
      = .error (.transition (.arithmetic
          "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee")) := by
  have hcomm :=
    getInclusionListCommittee_run_error_of_empty (σ := Store map) state (sszGet state slot - 1)
      runnerStore hempty
  have htxs :=
    getInclusionListTransactions_run_error_of_committee (map := map) store.inclusionListStore
      state (sszGet state slot - 1) true runnerStore _ hcomm
  exact recordPayloadInclusionListSatisfaction_run_error_of_collect
    store runnerStore state root payload _ hslot htxs

/-- Missing-timeliness collector error, derived from the collector theorems. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_missing_timeliness
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore postCommitteeStore : Store map) (state : State) (root : Root)
    (payload : ExecutionPayload)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (ilRoot : Root)
    (hslot : sszGet state slot ≠ 0)
    (hok : (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun (Store map))
        state (sszGet state slot - 1)).run runnerStore
      = .ok (committee, postCommitteeStore))
    (hfirst : FirstReachableMissingTimeliness
        (FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[]
          ((FcMap.lookup store.inclusionListStore.inclusionLists (htr committee)).getD FcMap.empty))
        (FcMap.lookupD store.inclusionListStore.equivocators (htr committee))
        store.inclusionListStore.inclusionListTimeliness ilRoot) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store state root payload).run runnerStore
      = .error (.missingKey ilRoot) := by
  have hcol :=
    collectInclusionListTransactions_run_error_of_first_missing (map := map) (σ := Store map)
      ((FcMap.lookup store.inclusionListStore.inclusionLists (htr committee)).getD FcMap.empty)
      (FcMap.lookupD store.inclusionListStore.equivocators (htr committee))
      store.inclusionListStore.inclusionListTimeliness true ilRoot postCommitteeStore rfl hfirst
  have htxs :=
    getInclusionListTransactions_run_error_of_collect (map := map) store.inclusionListStore
      state (sszGet state slot - 1) true runnerStore postCommitteeStore committee
      (.missingKey ilRoot) hok hcol
  exact recordPayloadInclusionListSatisfaction_run_error_of_collect
    store runnerStore state root payload _ hslot htxs

end EthCLSpecs.Proofs.Heze
