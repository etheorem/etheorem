import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.StoreRun

/-!
# Recording a payload's inclusion-list result

Heze records whether an execution payload contains the transactions required by
FOCIL. `recordPayloadInclusionListSatisfaction`:

1. collects the timely inclusion-list transactions for the previous slot;
2. checks whether the payload satisfies that list; and
3. records the resulting Boolean at the payload's block root.

This module proves what the function returns when transaction collection
succeeds.

The theorem has two stores:

- `store` is the explicit argument that the function updates and returns;
- `runnerStore` is the internal runner state used while the function runs.

If transaction collection changes the runner state from `runnerStore` to
`postRunnerStore`, the recorder leaves `postRunnerStore` unchanged. Separately,
it returns `store` with `payloadInclusionListSatisfaction[root]` updated to
`isInclusionListSatisfied payload ilTxs`.

The theorem covers both possible results of the satisfaction check. Slot zero
and transaction-collection failures remain open.

The theorem does not prove that a subsequent lookup returns the recorded
value, because the generic `FcMap` interface does not provide an insert/lookup
law.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedSub ExecutionEngine)
open EthCLSpecs.Heze (Preset Store State Root ExecutionPayload ExecutionRequests Transaction
  recordPayloadInclusionListSatisfaction getInclusionListTransactions isInclusionListSatisfied)

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

end EthCLSpecs.Proofs.Heze
