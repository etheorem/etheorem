import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.CLUint

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
`store.blocks` is the `missingKey root` error. The checked `Slot` subtraction
`store.blocks[root].slot - 1` appears as a decision on the plain slot
(`EthCLLib.Proofs.hsub_un_eq`): a slot-zero block is the `.arithmetic "-"` reject, and any
other block gives the previous slot as `CLUint64.ofNatLT`. The result then matches on the
dependent-root walk: a walk error is returned unchanged, and a successful walk returns `store` with
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

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok except_bind_error
  run_throw hsub_un_eq)
open EthCLLib.Spec (HasherTag MapKind FcMap CLUint64 ExecutionEngine)
open EthCLSpecs.Heze (Preset Store Root Slot ExecutionPayload ExecutionRequests Transaction
  recordPayloadInclusionListSatisfaction getShufflingDependentRoot getInclusionListTransactions
  isInclusionListSatisfied computeEpochAtSlot)

/-- The previous slot of a nonzero slot `a`, the success value of the checked `a - 1`. The
difference is at most `a`, so it stays below `2^64`. -/
private theorem prev_slot_lt (a : Slot) : a.toPlainNat - 1 < UInt64.size :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) (UInt64.toNat_lt_size a.val)

/-- The checked `a - 1` returns `slot` exactly when `slot` is one below `a`. -/
private theorem prev_slot_eq {a slot : Slot} (h : slot.toPlainNat + 1 = a.toPlainNat)
    (hlt : a.toPlainNat - 1 < UInt64.size) :
    CLUint64.ofNatLT (a.toPlainNat - 1) hlt = slot := by
  apply CLUint64.val_inj
  apply UInt64.toNat_inj.1
  show (CLUint64.ofNatLT (a.toPlainNat - 1) hlt).toPlainNat = slot.toPlainNat
  rw [CLUint64.ofNatLT_toPlainNat]
  omega

/-- Complete `.run` equation of `recordPayloadInclusionListSatisfaction`. A missing block is
`missingKey root`. The checked `store.blocks[root].slot - 1` is the decision on the plain
slot: a slot-zero block is the `.arithmetic "-"` reject, the range fault's machine reject,
and a nonzero slot gives the previous slot. The result then matches on the dependent-root walk
at the previous slot's epoch: an error is returned unchanged, and a successful walk records
`isInclusionListSatisfied payload ilTxs` at `root`, for the timely transactions `ilTxs`
stored under the walk's key, and keeps the walk's runner state. -/
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
          if 1 ≤ block.slot.toPlainNat then
            match (getShufflingDependentRoot
                (StoreTransition := ForkChoiceStoreRun (Store map))
                store root (computeEpochAtSlot
                  (CLUint64.ofNatLT _ (prev_slot_lt block.slot)))).run runnerStore with
            | .error err => .error err
            | .ok (dependentRoot, s1) =>
              .ok (
                { store with
                  payloadInclusionListSatisfaction :=
                    FcMap.insert store.payloadInclusionListSatisfaction root
                      (isInclusionListSatisfied payload
                        (getInclusionListTransactions store.inclusionListStore
                          (CLUint64.ofNatLT _ (prev_slot_lt block.slot)) dependentRoot
                          (onlyTimely := true))) },
                s1)
          else
            .error (.transition (.arithmetic "-")) := by
  intro store runnerStore root payload
  simp only [recordPayloadInclusionListSatisfaction, FcMap.getOrThrow, FcMap.getOrThrowKey,
    run_bind]
  cases hblock : FcMap.lookup store.blocks root with
  | none => rfl
  | some block =>
    rw [run_pure, except_bind_ok]
    -- Reduce the statement's outer match, then state the checked subtraction as its plain
    -- range decision (`hsub_un_eq`).
    dsimp only
    rw [hsub_un_eq]
    by_cases hpos : 1 ≤ block.slot.toPlainNat
    · rw [ite_eq_left hpos, ite_eq_left hpos, ForkChoiceStoreRun.liftChecked_ok_run,
        except_bind_ok]
      dsimp only
      cases hdep : (getShufflingDependentRoot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root (computeEpochAtSlot
            (CLUint64.ofNatLT _ (prev_slot_lt block.slot)))).run runnerStore with
      | error err => rfl
      | ok q =>
        obtain ⟨dependentRoot, s1⟩ := q
        rfl
    · rw [ite_eq_right hpos, ite_eq_right hpos, ForkChoiceStoreRun.liftChecked_error_run,
        except_bind_error]
      rfl

/-- The successful branch of the principal equation. The block is present, `slot` is the
slot before it, and the dependent-root walk has returned `dependentRoot` with runner state
`postRunnerStore`. Derived by rewriting with `recordPayloadInclusionListSatisfaction_run`.

The recorded result may be either `true` or `false`. -/
theorem recordPayloadInclusionListSatisfaction_run_eq
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore postRunnerStore : Store map) (root : Root)
      (payload : ExecutionPayload) (block : EthCLSpecs.Heze.BeaconBlock) (slot : Slot)
      (dependentRoot : Root),
      FcMap.lookup store.blocks root = some block →
      slot.toPlainNat + 1 = block.slot.toPlainNat →
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
    hblock hprev hdep
  have hpos : 1 ≤ block.slot.toPlainNat := by omega
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hpos, prev_slot_eq hprev, hdep]

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

/-- Slot-zero checked-sub error: `store.blocks[root].slot - 1` underflows, and the range
fault lands as the `.arithmetic` reject (the operator's payload, `-`). -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_slot_zero
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload)
    (block : EthCLSpecs.Heze.BeaconBlock)
    (hblock : FcMap.lookup store.blocks root = some block) (hslot : block.slot = 0) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root payload).run runnerStore
      = .error (.transition (.arithmetic "-")) := by
  have hzero : ¬ 1 ≤ block.slot.toPlainNat := by
    rw [hslot]
    decide
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hzero]

/-- An error of the dependent-root walk at the previous slot `slot` is the recorder's error. -/
theorem recordPayloadInclusionListSatisfaction_run_error_of_dependent_root
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    (store runnerStore : Store map) (root : Root) (payload : ExecutionPayload)
    (block : EthCLSpecs.Heze.BeaconBlock) (slot : Slot)
    (err : EthCLLib.Spec.StoreTransitionError)
    (hblock : FcMap.lookup store.blocks root = some block)
    (hprev : slot.toPlainNat + 1 = block.slot.toPlainNat)
    (herr : (getShufflingDependentRoot
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root (computeEpochAtSlot slot)).run runnerStore
      = .error err) :
    (recordPayloadInclusionListSatisfaction
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store root payload).run runnerStore
      = .error err := by
  have hpos : 1 ≤ block.slot.toPlainNat := by omega
  rw [recordPayloadInclusionListSatisfaction_run]
  simp [hblock, hpos, prev_slot_eq hprev, herr]

end EthCLSpecs.Proofs.Heze
