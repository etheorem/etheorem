import EthCLSpecs.Heze.ForkChoice
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.Arith
import EthCLLib.Proofs.LawfulFcMap
import SizzLean.Proofs.UncachedBox

/-!
# Collecting inclusion-list transactions

`getInclusionListCommittee` derives the inclusion-list committee for a slot from a state, and
`getInclusionListTransactions` gathers the transactions of the stored lists for one
`(slot, dependent_root)` key.

At v1.7.0-beta.4 the store is keyed by `(slot, dependent_root)` and each stored entry carries
its own timeliness, so `getInclusionListTransactions` is pure: it filters the key's items
(`inclusionListItems`, the spec's `inclusion_lists[key].items()`) to the counted ones and
deduplicates their transactions. alpha.12 derived the committee from a state inside the
accessor and raised on a missing timeliness record; both are gone, and the throwing theorems
that described them went with them.

This module proves the committee run equation and its empty-committee error, then the
transactions contract: a transaction is in the result exactly when some counted item's list
carries it, and the result holds no duplicate. `FcMap` gives no law relating `fold` to the
map's contents, so the contract is stated over `inclusionListItems`, the fold's output, which
is what the spec's loop iterates.

Under the `LawfulFcMap` laws at `ValidatorIndex` keys, the items are exactly the stored
entries (`mem_inclusionListItems_iff`). So the module also proves what an honest list
contributes. `mem_getInclusionListTransactions_of_stored`: take an entry stored for the
key and a validator, timely, from a validator that is not an equivocator for the key.
Each transaction of its list is in the result.

Statements bind plain `BeaconState` values; the committee reader receives `pureState state`,
the uncached box, and never a boxed `State` of its own.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok except_bind_error
  mem_arrayUnion_iff nodup_arrayUnion run_liftErr_of_ok run_liftErr_of_error)
open EthCLLib.Spec (HasherTag MapKind FcMap htr StoreTransitionError StateTransitionError
  arrayUnion)
open EthCLSpecs.Heze (Preset Store State BeaconState Root Slot ValidatorIndex InclusionList
  Transaction InclusionListStore InclusionListEntry getInclusionListCommittee
  getInclusionListTransactions inclusionListItems isCountedInclusionList countedInclusionLists
  getBeaconCommittee getCommitteeCountPerSlot computeEpochAtSlot cyclicSample)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)
open EthCLLib.Proofs (pureState LawfulFcMap)

section CommitteeRun
variable {σ : Type} [Preset]
section
variable [HasherTag]

/-- The slot's committees laid end to end, the `indices` that
`get_inclusion_list_committee` samples. Each `getBeaconCommittee` call can fault, so the
concatenation is an `Except`. -/
def slotCommitteeIndices (state : BeaconState) (slot : Slot) :
    Except StateTransitionError (Array ValidatorIndex) :=
  (Array.range (getCommitteeCountPerSlot (pureState state) (computeEpochAtSlot slot))).foldlM
    (fun acc i => do pure (acc ++ (← getBeaconCommittee (pureState state) slot i)))
    (#[] : Array ValidatorIndex)

/-- Complete `.run` equation of `getInclusionListCommittee`. A committee fault surfaces as
the store's `.transition` reject. An empty concatenation throws the empty-committee
arithmetic error. A nonempty one returns `cyclicSample` of it and leaves the runner state
unchanged. The committee accessor does not read the runner state, so the equation holds for
an arbitrary `σ`. -/
@[characterizes EthCLSpecs.Heze.getInclusionListCommittee]
theorem getInclusionListCommittee_run_eq :
    ∀ (state : BeaconState) (slot : Slot) (runnerStore : σ),
      (getInclusionListCommittee
          (StoreTransition := ForkChoiceStoreRun σ) (pureState state) slot).run runnerStore =
        match slotCommitteeIndices state slot with
        | .error e => .error (.transition e)
        | .ok indices =>
          if indices.size == 0 then
            .error (.transition (.arithmetic
              "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee"))
          else
            .ok (cyclicSample indices inclusionListCommitteeSize, runnerStore) := by
  intro state slot runnerStore
  simp only [getInclusionListCommittee]
  rw [run_bind]
  cases hidx : slotCommitteeIndices state slot with
  | error e =>
    rw [run_liftErr_of_error _ _ (by simp only [slotCommitteeIndices] at hidx; rw [hidx]; rfl),
      except_bind_error]
    rfl
  | ok indices =>
    rw [run_liftErr_of_ok _ _ (by simp only [slotCommitteeIndices] at hidx; rw [hidx]; rfl),
      except_bind_ok]
    simp only
    split
    · rw [run_bind, ForkChoiceStoreRun.throwArithmetic_run]
      exact except_bind_error _ _
    · rw [run_pure]

/-- Exact empty-committee error of `getInclusionListCommittee`. -/
theorem getInclusionListCommittee_run_error_of_empty
    (state : BeaconState) (slot : Slot) (runnerStore : σ)
    (indices : Array ValidatorIndex)
    (hok : slotCommitteeIndices state slot = .ok indices) (h : indices.size = 0) :
    (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun σ) (pureState state) slot).run runnerStore
      = .error (.transition (.arithmetic
          "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee")) := by
  simp only [getInclusionListCommittee_run_eq, hok, h, beq_iff_eq, ite_true]

end
end CommitteeRun

section Transactions
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

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

/-- The entries stored under the key `(slot, dependent_root)`, or the empty map when the key
has none: the spec's `defaultdict` read of `inclusion_lists[key]`. The `ILStore` namespace
continues in `OnInclusionList.lean`, which imports this module. -/
def ILStore.entriesAt (s : InclusionListStore map) (key : Slot × Root) :
    map ValidatorIndex InclusionListEntry :=
  (FcMap.lookup s.inclusionLists key).getD FcMap.empty

/-- The entry stored under the key `key` for the validator `vi`. -/
def ILStore.entryAt (s : InclusionListStore map) (key : Slot × Root) (vi : ValidatorIndex) :
    Option InclusionListEntry :=
  FcMap.lookup (ILStore.entriesAt s key) vi

section
variable [LawfulFcMap map ValidatorIndex]

/-- The items of a key are exactly its stored entries. `inclusionListItems` folds the
entries of the key into an array, and the fold law of `LawfulFcMap` says that the fold
lists each entry. -/
theorem mem_inclusionListItems_iff (s : InclusionListStore map) (slot : Slot)
    (dependentRoot : Root) (vi : ValidatorIndex) (e : InclusionListEntry) :
    (vi, e) ∈ inclusionListItems s slot dependentRoot ↔
      ILStore.entryAt s (slot, dependentRoot) vi = some e := by
  unfold inclusionListItems ILStore.entryAt ILStore.entriesAt
  rw [← Array.mem_toList_iff]
  exact LawfulFcMap.mem_fold_push _ vi e

/-- The timely inclusion-list transactions for a key contain each transaction of an honest
list. The hypotheses are:

1. the entry `e` is stored under `(slot, dependentRoot)` for the validator `vi`;
2. the entry is timely;
3. `vi` is not an equivocator for the key. -/
theorem mem_getInclusionListTransactions_of_stored (s : InclusionListStore map) (slot : Slot)
    (dependentRoot : Root) (vi : ValidatorIndex) (e : InclusionListEntry)
    (hstored : ILStore.entryAt s (slot, dependentRoot) vi = some e)
    (htimely : e.timely = true)
    (hhonest : (FcMap.lookupD s.equivocators (slot, dependentRoot)).contains vi = false) :
    ∀ tx ∈ e.signedInclusionList.message.transactions.toArray,
      tx ∈ getInclusionListTransactions s slot dependentRoot (onlyTimely := true) := by
  intro tx htx
  rw [mem_getInclusionListTransactions_iff]
  exact ⟨(vi, e), (mem_inclusionListItems_iff s slot dependentRoot vi e).mpr hstored, hhonest,
    fun _ => htimely, htx⟩

end

end Transactions

end EthCLSpecs.Proofs.Heze
