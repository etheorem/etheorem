import EthCLSpecs.Heze.ForkChoice
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.Arith
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

Statements bind plain `BeaconState` values; the committee reader receives `pureState state`,
the uncached box, and never a boxed `State` of its own.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok except_bind_error
  mem_arrayUnion_iff nodup_arrayUnion)
open EthCLLib.Spec (HasherTag MapKind FcMap htr StoreTransitionError arrayUnion)
open EthCLSpecs.Heze (Preset Store State BeaconState Root Slot ValidatorIndex InclusionList
  Transaction InclusionListStore InclusionListEntry getInclusionListCommittee
  getInclusionListTransactions inclusionListItems isCountedInclusionList countedInclusionLists
  getBeaconCommittee getCommitteeCountPerSlot computeEpochAtSlot cyclicSample)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)
open EthCLLib.Proofs (pureState)

section CommitteeRun
variable {σ : Type} [Preset]
section
variable [HasherTag]

/-- Complete `.run` equation of `getInclusionListCommittee`. The concatenated
indices expression is the one in the source. An empty array throws the
empty-committee arithmetic error. A nonempty array returns `cyclicSample` of
that array and leaves the runner state unchanged. The committee accessor does
not read the runner state, so the equation holds for an arbitrary `σ`. -/
@[characterizes EthCLSpecs.Heze.getInclusionListCommittee]
theorem getInclusionListCommittee_run_eq :
    ∀ (state : BeaconState) (slot : Slot) (runnerStore : σ),
      let indices :=
        (Array.range (getCommitteeCountPerSlot (pureState state) (computeEpochAtSlot slot))).foldl
          (fun acc i => acc ++ getBeaconCommittee (pureState state) slot i)
          (#[] : Array ValidatorIndex)
      (getInclusionListCommittee
          (StoreTransition := ForkChoiceStoreRun σ) (pureState state) slot).run runnerStore =
        if indices.size == 0 then
          .error (.transition (.arithmetic
            "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee"))
        else
          .ok (cyclicSample indices inclusionListCommitteeSize, runnerStore) := by
  intro state slot runnerStore
  simp only [getInclusionListCommittee]
  split
  · rw [run_bind, ForkChoiceStoreRun.throwArithmetic_run]
    exact except_bind_error _ _
  · rw [run_pure]

/-- Exact empty-committee error of `getInclusionListCommittee`. -/
theorem getInclusionListCommittee_run_error_of_empty
    (state : BeaconState) (slot : Slot) (runnerStore : σ)
    (h : ((Array.range (getCommitteeCountPerSlot (pureState state) (computeEpochAtSlot slot))).foldl
        (fun acc i => acc ++ getBeaconCommittee (pureState state) slot i)
        (#[] : Array ValidatorIndex)).size = 0) :
    (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun σ) (pureState state) slot).run runnerStore
      = .error (.transition (.arithmetic
          "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee")) := by
  simp only [getInclusionListCommittee_run_eq, h, beq_iff_eq, ite_true]

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

end Transactions

end EthCLSpecs.Proofs.Heze
