import EthCLSpecs.Heze.ForkChoice
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.Arith

/-!
# Collecting inclusion-list transactions

`getInclusionListCommittee` derives the inclusion-list committee for a slot from a state, and
`getInclusionListTransactions` gathers the transactions of the stored lists for one
`(slot, dependent_root)` key.

At v1.7.0-beta.4 the store is keyed by `(slot, dependent_root)` and each stored entry carries
its own timeliness, so `getInclusionListTransactions` is pure: it filters the key's items
(`inclusionListItems`, the spec's `inclusion_lists[key].items()`) to the counted ones and
deduplicates their transactions.

This module proves the committee run equation and its empty-committee error, then the
transactions contract: a transaction is in the result exactly when some counted item's list
carries it, and the result holds no duplicate. `FcMap` gives no law relating `fold` to the
map's contents, so the contract is stated over `inclusionListItems`, the fold's output, which
is what the spec's loop iterates.

Statements bind plain `BeaconState` values. The Heze `State` is the plain record, so the
committee reader receives `state` itself.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok except_bind_error
  run_liftErr_of_ok run_liftErr_of_error mem_arrayUnion_iff nodup_arrayUnion)
open EthCLLib.Spec (HasherTag MapKind FcMap htr StoreTransitionError arrayUnion liftErr)
open EthCLSpecs.Heze (Preset Store State BeaconState Root Slot ValidatorIndex InclusionList
  Transaction InclusionListStore InclusionListEntry getInclusionListCommittee
  getInclusionListTransactions inclusionListItems isCountedInclusionList countedInclusionLists
  getBeaconCommittee getCommitteeCountPerSlot computeEpochAtSlot cyclicSample)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)

section CommitteeRun
variable {σ : Type} [Preset]
section
variable [HasherTag]

omit [Preset] [HasherTag] in
/-- `cyclicSample` over an empty source raises the zero-divisor fault at its first
position: `index % len(indices)` with `len(indices) = 0` (a bare `ZeroDivisionError` at the
pin, its own `ArithCause` class). Any positive size reaches that position. -/
theorem cyclicSample_empty {α : Type} (n : Nat) (hn : 0 < n) :
    cyclicSample (#[] : Array α) n = .error (.zeroDivision "%") := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold cyclicSample
  rw [Vector.ofFnM_succ']
  rfl

/-- Complete `.run` equation of `getInclusionListCommittee`. The committee count
binds first: its active-set `ValidatorIndex` casts are checked, so a fault there
ends the run. The concatenated indices expression is the one in the source: the
monadic fold over the slot's committees, each `get_beacon_committee` bound as it
forms (its checked seed walk and the shuffled-index assert of `compute_committee`
can reject, and that fault propagates through the fold). The fold runs over the
plain positions below the checked count. The result is `cyclicSample` of the
concatenation: its fault (the zero-divisor fault of an empty concatenation)
becomes the wrapped store reject, and its value returns with the runner state
unchanged. The committee accessor does not read
the runner state, so the equation holds for an arbitrary `σ`. -/
@[characterizes EthCLSpecs.Heze.getInclusionListCommittee]
theorem getInclusionListCommittee_run_eq :
    ∀ (state : BeaconState) (slot : Slot) (runnerStore : σ),
      (getInclusionListCommittee
          (StoreTransition := ForkChoiceStoreRun σ) state slot).run runnerStore =
        match ((liftM (getCommitteeCountPerSlot state (computeEpochAtSlot slot)) :
            ForkChoiceStoreRun σ EthCLLib.Spec.CLUint64).run runnerStore) with
        | .error e =>
          (Except.error e :
            Except StoreTransitionError
              (Vector ValidatorIndex inclusionListCommitteeSize × σ))
        | .ok (count, s₀) =>
        match ((Array.foldlM
            (fun acc i => do
              let committeeIndex ← liftM (EthCLLib.Spec.CLUint64.ofNat? i)
              let committee ← liftErr (getBeaconCommittee state slot committeeIndex)
              pure (acc ++ committee))
            (#[] : Array ValidatorIndex)
            (Array.range count.toPlainNat) :
          ForkChoiceStoreRun σ (Array ValidatorIndex)).run s₀) with
        | .error e =>
          (Except.error e :
            Except StoreTransitionError
              (Vector ValidatorIndex inclusionListCommitteeSize × σ))
        | .ok (indices, s') =>
          match cyclicSample indices inclusionListCommitteeSize with
          | .error e =>
            (Except.error (.transition e) :
              Except StoreTransitionError
                (Vector ValidatorIndex inclusionListCommitteeSize × σ))
          | .ok committee =>
            (Except.ok (committee, s') :
              Except StoreTransitionError
                (Vector ValidatorIndex inclusionListCommitteeSize × σ)) := by
  intro state slot runnerStore
  simp only [getInclusionListCommittee]
  rw [run_bind]
  cases hc : ((liftM (getCommitteeCountPerSlot state (computeEpochAtSlot slot)) :
      ForkChoiceStoreRun σ EthCLLib.Spec.CLUint64).run runnerStore) with
  | error e => rfl
  | ok q =>
    obtain ⟨count, s₀⟩ := q
    simp only [except_bind_ok]
    rw [run_bind]
    cases hf : ((Array.foldlM
        (fun acc i => do
          let committeeIndex ← liftM (EthCLLib.Spec.CLUint64.ofNat? i)
          let committee ← liftErr (getBeaconCommittee state slot committeeIndex)
          pure (acc ++ committee))
        (#[] : Array ValidatorIndex)
        (Array.range count.toPlainNat) :
      ForkChoiceStoreRun σ (Array ValidatorIndex)).run s₀) with
    | error e => rfl
    | ok p =>
      obtain ⟨indices, s'⟩ := p
      simp only [except_bind_ok]
      cases hs : cyclicSample indices inclusionListCommitteeSize with
      | error e => exact run_liftErr_of_error _ s' rfl
      | ok committee => exact run_liftErr_of_ok _ s' rfl

/-- Exact empty-committee error of `getInclusionListCommittee`, on the
successful count and fold: when the count binds, every committee read succeeds,
the concatenation is empty, and the committee size is positive, the accessor
throws the zero-division fault of the first position's `index % len(indices)`.
With a zero committee size the comprehension forms no position and nothing
raises, so the positivity premise is the condition under which the pinned body
raises. -/
theorem getInclusionListCommittee_run_error_of_empty
    (state : BeaconState) (slot : Slot) (runnerStore : σ) (count : EthCLLib.Spec.CLUint64)
    (hn : 0 < inclusionListCommitteeSize)
    (hc : ((liftM (getCommitteeCountPerSlot state (computeEpochAtSlot slot)) :
        ForkChoiceStoreRun σ EthCLLib.Spec.CLUint64).run runnerStore) = .ok (count, runnerStore))
    (h : ((Array.foldlM
        (fun acc i => do
          let committeeIndex ← liftM (EthCLLib.Spec.CLUint64.ofNat? i)
          let committee ← liftErr (getBeaconCommittee state slot committeeIndex)
          pure (acc ++ committee))
        (#[] : Array ValidatorIndex)
        (Array.range count.toPlainNat) :
      ForkChoiceStoreRun σ (Array ValidatorIndex)).run runnerStore)
      = .ok (#[], runnerStore)) :
    (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun σ) state slot).run runnerStore
      = .error (.transition (.zeroDivision "%")) := by
  rw [getInclusionListCommittee_run_eq state slot runnerStore, hc]
  simp only []
  rw [h]
  simp only []
  rw [cyclicSample_empty _ hn]

end
end CommitteeRun

section Transactions
variable {map : MapKind} [Preset] [FcMap map]

/-- Which items count. An item is in `countedInclusionLists` exactly when it is one of the
key's items, its validator is not an equivocator for the key, and, when only timely lists
count, its list was timely: the two `continue`s of the spec's loop. -/
theorem mem_countedInclusionLists_iff (store : InclusionListStore map) (slot : Slot)
    (dependentRoot : Root) (onlyTimely : Bool) (item : ValidatorIndex × InclusionListEntry) :
    item ∈ countedInclusionLists store slot dependentRoot onlyTimely ↔
      item ∈ inclusionListItems store slot dependentRoot
        ∧ (FcMap.lookupD store.equivocators (slot, dependentRoot)).contains item.1 = false
        ∧ (onlyTimely = true → item.2.timely = true) := by
  unfold countedInclusionLists isCountedInclusionList
  rw [Array.mem_filter]
  cases onlyTimely <;> simp

/-- **The transactions contract.** A transaction is in
`get_inclusion_list_transactions(store, slot, dependent_root, only_timely)` exactly when the
list of some counted item for the key carries it: an equivocator's list contributes nothing,
and with `onlyTimely` an untimely list contributes nothing. With `getInclusionListTransactions_nodup`
it says the result is the set of those transactions, the spec's `list(set(transactions))`. -/
@[characterizes EthCLSpecs.Heze.getInclusionListTransactions]
theorem mem_getInclusionListTransactions_iff (store : InclusionListStore map) (slot : Slot)
    (dependentRoot : Root) (onlyTimely : Bool) (tx : Transaction) :
    tx ∈ getInclusionListTransactions store slot dependentRoot onlyTimely ↔
      ∃ item ∈ inclusionListItems store slot dependentRoot,
        (FcMap.lookupD store.equivocators (slot, dependentRoot)).contains item.1 = false
          ∧ (onlyTimely = true → item.2.timely = true)
          ∧ tx ∈ item.2.signedInclusionList.message.transactions.toArray := by
  unfold getInclusionListTransactions
  rw [mem_arrayUnion_iff]
  simp only [Array.not_mem_empty, false_or, Array.mem_flatMap]
  constructor
  · rintro ⟨item, hitem, htx⟩
    obtain ⟨hmem, hequiv, htimely⟩ :=
      (mem_countedInclusionLists_iff store slot dependentRoot onlyTimely item).mp hitem
    exact ⟨item, hmem, hequiv, htimely, htx⟩
  · rintro ⟨item, hmem, hequiv, htimely, htx⟩
    exact ⟨item, (mem_countedInclusionLists_iff store slot dependentRoot onlyTimely item).mpr
      ⟨hmem, hequiv, htimely⟩, htx⟩

/-- **No duplicates.** The result holds each transaction once, whatever the counted lists
repeat: the dedup the spec's `set` performs. -/
theorem getInclusionListTransactions_nodup (store : InclusionListStore map) (slot : Slot)
    (dependentRoot : Root) (onlyTimely : Bool) :
    (getInclusionListTransactions store slot dependentRoot onlyTimely).toList.Nodup :=
  nodup_arrayUnion _ _ (by simp)

/-- An equivocator's list contributes nothing. The corollary of the contract the spec's
first `continue` states: if every item that carries `tx` comes from an equivocator for the
key, `tx` is not in the result. -/
theorem not_mem_getInclusionListTransactions_of_equivocators (store : InclusionListStore map)
    (slot : Slot) (dependentRoot : Root) (onlyTimely : Bool) (tx : Transaction)
    (h : ∀ item ∈ inclusionListItems store slot dependentRoot,
      tx ∈ item.2.signedInclusionList.message.transactions.toArray →
      (FcMap.lookupD store.equivocators (slot, dependentRoot)).contains item.1 = true) :
    tx ∉ getInclusionListTransactions store slot dependentRoot onlyTimely := by
  rw [mem_getInclusionListTransactions_iff]
  rintro ⟨item, hmem, hequiv, _, htx⟩
  rw [h item hmem htx] at hequiv
  exact Bool.noConfusion hequiv

end Transactions

end EthCLSpecs.Proofs.Heze
