import EthCLLib.Proofs.ArrayUnion
import EthCLLib.Proofs.LawfulFcMap
import EthCLSpecs.Heze.ForkChoice
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun
import SizzLean.Proofs.UncachedBox

/-!
# Collecting inclusion-list transactions

`getInclusionListTransactions` derives the inclusion-list committee for a slot,
looks up the stored lists for that committee root, and gathers their
transactions. The inner walk is `collectInclusionListTransactions`.

This module proves the committee run equation, the empty-committee arithmetic
error, a predicate for the first reachable missing timeliness key in the
`FcMap.fold` entries array, and how committee-construction and collector errors
propagate through `getInclusionListTransactions`.

`getInclusionListCommittee_run_eq` and `getInclusionListTransactions_run_eq`
are the principal equations.

Statements bind plain `BeaconState` values; the two state readers receive
`pureState state`, the uncached box, and never a boxed `State` of their own. The
collector theorems below never touch a state, so they stay as they are.

Under the `LawfulFcMap` laws, the module also proves what a successful collection
returns. `collectInclusionListTransactions_ok_mem_iff`: when every stored list has a
timeliness entry, collection succeeds. A transaction is in the result exactly when a
stored list carries it (`EntryCollects`). That list has timeliness `true`, and its
validator is not an equivocator. `collectInclusionListTransactions_ok_mem` is the one
direction that the honest-list proofs use. `getInclusionListTransactions_ok_mem_iff` and
`mem_getInclusionListTransactions` state the same through the committee lookup.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok except_bind_error
  run_liftErr_of_ok run_liftErr_of_error)
open EthCLLib.Spec (HasherTag MapKind FcMap htr StoreTransitionError StateTransitionError
  arrayUnion)
open EthCLLib.Proofs (LawfulFcMap mem_arrayUnion)
open EthCLSpecs.Heze (Preset Store State BeaconState Root Slot ValidatorIndex InclusionList
  Transaction InclusionListStore getInclusionListCommittee getInclusionListTransactions
  collectInclusionListTransactions getBeaconCommittee getCommitteeCountPerSlot
  computeEpochAtSlot cyclicSample)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)
open EthCLLib.Proofs (pureState)

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
    · rw [run_bind, run_pure, except_bind_ok]
      rw [run_pure]

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

/-- The committee run does not read the runner state, so a result at one runner is the
result at any runner, of any type. -/
theorem getInclusionListCommittee_run_ok_transfer {τ : Type} (state : BeaconState)
    (slot : Slot) (s : σ) (t : τ) (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (h : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun σ)
        (pureState state) slot).run s = .ok (committee, s)) :
    (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun τ)
        (pureState state) slot).run t = .ok (committee, t) := by
  rw [getInclusionListCommittee_run_eq] at h ⊢
  cases hidx : slotCommitteeIndices state slot with
  | error e =>
    rw [hidx] at h
    cases h
  | ok indices =>
    rw [hidx] at h
    simp only at h ⊢
    split at h
    · cases h
    · rename_i hne
      rw [if_neg hne]
      injection h with h
      injection h with h
      rw [h]

end
end CommitteeRun

section Collector
variable {map : MapKind} [Preset]
section
variable [FcMap map]

/-- `entry` does not fail a timeliness read. An equivocator entry skips the
lookup. A non-equivocator entry whose list root is already in `timeliness`
performs a successful lookup. -/
def TimelinessEntryDoesNotError
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (entry : Root × InclusionList) : Prop :=
  equivocators.contains entry.2.validatorIndex = true
    ∨ (FcMap.lookup timeliness entry.1).isSome = true

/-- The first entry in `entries` whose collection step reads a missing timeliness
key. Prefix entries do not fail that read. This entry is not from an equivocator.
`FcMap.lookup timeliness ilRoot` is `none`.

`entries` is the array produced by
`FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[] inclusionLists`.
The predicate does not assume a generic fold order. -/
def FirstReachableMissingTimeliness
    (entries : Array (Root × InclusionList))
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (ilRoot : Root) : Prop :=
  ∃ (i : Nat) (il : InclusionList) (hi : i < entries.size),
    entries[i]'hi = (ilRoot, il)
      ∧ (∀ (j : Nat) (hj : j < i),
          TimelinessEntryDoesNotError equivocators timeliness
            (entries[j]'(Nat.lt_trans hj hi)))
      ∧ equivocators.contains il.validatorIndex = false
      ∧ FcMap.lookup timeliness ilRoot = none

/-- Every stored list in `lists` has a timeliness entry. Then no entry fails a timeliness
read, whatever the equivocators are. -/
def TimelinessTotal (lists : map Root InclusionList) (timeliness : map Root Bool) : Prop :=
  ∀ r il, FcMap.lookup lists r = some il → (FcMap.lookup timeliness r).isSome

section
variable {σ : Type}

/-- One step of the `collectInclusionListTransactions` `foldlM` body, at the
fork-choice store runner. The step does not read the runner state. -/
private def collectStep
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (onlyTimely : Bool) :
    Array Transaction → Root × InclusionList →
      ForkChoiceStoreRun σ (Array Transaction) :=
  fun acc (ilRoot, il) =>
    if equivocators.contains il.validatorIndex then pure acc
    else if !onlyTimely then pure (acc ++ il.transactions.toArray)
    else do
      let timely ← FcMap.getOrThrow timeliness ilRoot
      if timely then pure (acc ++ il.transactions.toArray) else pure acc

private theorem collectInclusionListTransactions_eq
    (inclusionLists : map Root InclusionList)
    (equivocators : Array ValidatorIndex)
    (timeliness : map Root Bool)
    (onlyTimely : Bool) :
    collectInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun σ)
        inclusionLists equivocators timeliness onlyTimely =
      (FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[] inclusionLists).foldlM
        (collectStep (σ := σ) equivocators timeliness onlyTimely) #[]
      >>= fun collected => pure (arrayUnion #[] collected) :=
  rfl

/-- One step at `onlyTimely := true` on an entry that is not from an equivocator and has
no timeliness entry. The step fails with `.missingKey`. -/
private theorem collectStep_run_error_of_missing
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (acc : Array Transaction) (ilRoot : Root) (il : InclusionList) (s : σ)
    (hnot : equivocators.contains il.validatorIndex = false)
    (hnone : FcMap.lookup timeliness ilRoot = none) :
    (collectStep (σ := σ) equivocators timeliness true acc (ilRoot, il)).run s
      = .error (.missingKey ilRoot) := by
  simp only [collectStep, hnot]
  simp only [FcMap.getOrThrow, FcMap.getOrThrowKey, hnone]
  rfl

/-- The entry `e` adds `tx` to the collection. Three conditions hold:

- The validator of `e` is not an equivocator.
- The timeliness of `e` is `true`.
- `tx` is a transaction of `e`. -/
def EntryCollects (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (e : Root × InclusionList) (tx : Transaction) : Prop :=
  equivocators.contains e.2.validatorIndex = false ∧
    FcMap.lookup timeliness e.1 = some true ∧ tx ∈ e.2.transactions.toArray

/-- One step at `onlyTimely := true` on an entry that does not fail a timeliness read.
The step succeeds without a change to the runner state. A transaction is in the result
exactly when it is in the start value or the entry collects it. -/
private theorem collectStep_run_ok_of_doesNotError
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (acc : Array Transaction) (entry : Root × InclusionList) (s : σ)
    (hok : TimelinessEntryDoesNotError equivocators timeliness entry) :
    ∃ acc', (collectStep (σ := σ) equivocators timeliness true acc entry).run s
        = .ok (acc', s) ∧
      ∀ tx, tx ∈ acc' ↔ tx ∈ acc ∨ EntryCollects equivocators timeliness entry tx := by
  obtain ⟨ilRoot, il⟩ := entry
  cases hcont : equivocators.contains il.validatorIndex
  · -- Not an equivocator, so `hok` gives the timeliness entry `b`.
    obtain ⟨b, hb⟩ : ∃ b, FcMap.lookup timeliness ilRoot = some b := by
      rcases hok with hmem | hsome
      · exact nomatch hcont.symm.trans hmem
      · exact Option.isSome_iff_exists.mp hsome
    refine ⟨if b then acc ++ il.transactions.toArray else acc, ?_, ?_⟩
    · simp only [collectStep, hcont]
      simp only [FcMap.getOrThrow, FcMap.getOrThrowKey, hb]
      cases b <;> rfl
    · intro tx
      cases b <;> simp only [EntryCollects, hcont, hb] <;> simp [Array.mem_append]
  · -- An equivocator: the step skips the entry.
    refine ⟨acc, ?_, fun tx => by simp only [EntryCollects, hcont]; simp⟩
    simp only [collectStep, hcont]
    rfl

/-- The loop at `onlyTimely := true` succeeds on a list of entries when no entry fails a
timeliness read. A transaction is in the result exactly when it is in the start value or
some entry collects it. The runner state does not change. -/
private theorem collectLoop_ok (equivocators : Array ValidatorIndex)
    (timeliness : map Root Bool) (s : σ) :
    ∀ (es : List (Root × InclusionList)) (acc : Array Transaction),
      (∀ e ∈ es, TimelinessEntryDoesNotError equivocators timeliness e) →
      ∃ out, (es.foldlM (collectStep (σ := σ) equivocators timeliness true) acc).run s
          = .ok (out, s) ∧
        ∀ tx, tx ∈ out ↔ tx ∈ acc ∨ ∃ e ∈ es, EntryCollects equivocators timeliness e tx := by
  intro es
  induction es with
  | nil => intro acc _; exact ⟨acc, rfl, by simp⟩
  | cons e es ih =>
    intro acc hall
    obtain ⟨acc', hstep, hacc'⟩ := collectStep_run_ok_of_doesNotError (σ := σ)
      equivocators timeliness acc e s (hall e List.mem_cons_self)
    obtain ⟨out, hrun, hout⟩ := ih acc' (fun e' he' => hall e' (by simp [he']))
    refine ⟨out, ?_, fun tx => ?_⟩
    · rw [List.foldlM_cons, run_bind, hstep, except_bind_ok]
      exact hrun
    · rw [hout tx, hacc' tx]
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, or_assoc]

/-- If `onlyTimely = true` and the first reachable missing timeliness key in the
`FcMap.fold` entries array is `ilRoot`, collection fails with `.missingKey ilRoot`.
The collector does not read the runner state, so the equation holds for an
arbitrary `σ`. -/
theorem collectInclusionListTransactions_run_error_of_first_missing
    (inclusionLists : map Root InclusionList)
    (equivocators : Array ValidatorIndex)
    (timeliness : map Root Bool)
    (onlyTimely : Bool) (ilRoot : Root)
    (runnerStore : σ)
    (honly : onlyTimely = true)
    (hfirst : FirstReachableMissingTimeliness
        (FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[] inclusionLists)
        equivocators timeliness ilRoot) :
    (collectInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun σ)
        inclusionLists equivocators timeliness onlyTimely).run runnerStore
      = .error (.missingKey ilRoot) := by
  subst honly
  rw [collectInclusionListTransactions_eq]
  rw [run_bind]
  let entries := FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[] inclusionLists
  obtain ⟨i, il, hi, hget, hpref, hnot, hnone⟩ := hfirst
  have hfold :
      (entries.foldlM (collectStep (σ := σ) equivocators timeliness true) #[]).run runnerStore
        = .error (.missingKey ilRoot) := by
    rw [← Array.foldlM_toList]
    have hi' : i < entries.toList.length := by simpa [Array.length_toList] using hi
    rw [← List.take_append_drop (l := entries.toList) i, List.drop_eq_getElem_cons hi']
    have hget' : entries.toList[i]'hi' = (ilRoot, il) := by
      rw [Array.getElem_toList]; exact hget
    simp only [hget']
    rw [List.foldlM_append, run_bind]
    obtain ⟨acc', hpre, -⟩ :=
      collectLoop_ok (σ := σ) equivocators timeliness runnerStore (entries.toList.take i) #[]
        (fun x hx => by
          obtain ⟨j, hj, rfl⟩ := (List.mem_take_iff_getElem).1 hx
          have hj_lt_i : j < i := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
          have := hpref j hj_lt_i
          simpa [Array.getElem_toList] using this)
    rw [hpre, except_bind_ok]
    rw [List.foldlM_cons, run_bind,
      collectStep_run_error_of_missing (σ := σ) equivocators timeliness acc' ilRoot il
        runnerStore hnot hnone]
    exact except_bind_error _ _
  rw [hfold]
  exact except_bind_error _ _

section
variable [LawfulFcMap map Root]

/-- `collectInclusionListTransactions` at `onlyTimely := true` succeeds when every stored
list has a timeliness entry. A transaction is in the result exactly when some entry
`(ilRoot, il)` of `lists` collects it (`EntryCollects`). The runner state does not
change. The result order follows the fold order of the map. This statement does not fix
that order. -/
theorem collectInclusionListTransactions_ok_mem_iff (lists : map Root InclusionList)
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool) (s : σ)
    (htotal : TimelinessTotal lists timeliness) :
    ∃ ilTxs, (collectInclusionListTransactions (StoreTransition := ForkChoiceStoreRun σ)
        lists equivocators timeliness true).run s = .ok (ilTxs, s) ∧
      ∀ tx, tx ∈ ilTxs ↔ ∃ (ilRoot : Root) (il : InclusionList),
        FcMap.lookup lists ilRoot = some il ∧
        EntryCollects equivocators timeliness (ilRoot, il) tx := by
  -- The entries of the fold are exactly the stored pairs (`LawfulFcMap.mem_fold_push`).
  let entries : Array (Root × InclusionList) :=
    FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[] lists
  have hentries : ∀ e, e ∈ entries.toList ↔ FcMap.lookup lists e.1 = some e.2 := by
    rintro ⟨r, il⟩
    exact LawfulFcMap.mem_fold_push lists r il
  obtain ⟨out, hrun, hout⟩ := collectLoop_ok equivocators timeliness s entries.toList #[]
    (fun e he => Or.inr (htotal e.1 e.2 ((hentries e).mp he)))
  refine ⟨arrayUnion #[] out, ?_, fun tx => ?_⟩
  · have hloop : (entries.foldlM (collectStep (σ := σ) equivocators timeliness true) #[]).run s
        = .ok (out, s) := by
      rw [← Array.foldlM_toList]
      exact hrun
    rw [collectInclusionListTransactions_eq, run_bind, hloop, except_bind_ok, run_pure]
  · rw [mem_arrayUnion, hout tx]
    constructor
    · rintro (h | h | ⟨e, he, hc⟩)
      · simp at h
      · simp at h
      · exact ⟨e.1, e.2, (hentries e).mp he, hc⟩
    · rintro ⟨ilRoot, il, hl, hc⟩
      exact Or.inr (Or.inr ⟨(ilRoot, il), (hentries _).mpr hl, hc⟩)

/-- `collectInclusionListTransactions` at `onlyTimely := true` succeeds when every stored
list has a timeliness entry. Take a list `il` that is stored at `ilRoot`, has timeliness
`true`, and has a validator that is not in `equivocators`. Then each transaction of `il` is
in the result. The runner state does not change. -/
theorem collectInclusionListTransactions_ok_mem (lists : map Root InclusionList)
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool) (s : σ)
    (htotal : TimelinessTotal lists timeliness) :
    ∃ ilTxs, (collectInclusionListTransactions (StoreTransition := ForkChoiceStoreRun σ)
        lists equivocators timeliness true).run s = .ok (ilTxs, s) ∧
      ∀ (ilRoot : Root) (il : InclusionList), FcMap.lookup lists ilRoot = some il →
        equivocators.contains il.validatorIndex = false →
        FcMap.lookup timeliness ilRoot = some true →
        ∀ tx ∈ il.transactions.toArray, tx ∈ ilTxs := by
  obtain ⟨ilTxs, hrun, hmem⟩ :=
    collectInclusionListTransactions_ok_mem_iff lists equivocators timeliness s htotal
  exact ⟨ilTxs, hrun, fun ilRoot il hl hne htrue tx htx =>
    (hmem tx).mpr ⟨ilRoot, il, hl, hne, htrue, htx⟩⟩

end

end
end

section Wrapper
variable [HasherTag]
section
variable [FcMap map]

/-- `.run` of `getInclusionListTransactions` is the committee run bound to
collection at the committee's stored lists. -/
@[characterizes EthCLSpecs.Heze.getInclusionListTransactions]
theorem getInclusionListTransactions_run_eq
    (store : InclusionListStore map) (state : BeaconState) (slot : Slot)
    (onlyTimely : Bool) (runnerStore : Store map) :
    (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store (pureState state) slot onlyTimely).run runnerStore
      = ((getInclusionListCommittee
            (StoreTransition := ForkChoiceStoreRun (Store map))
            (pureState state) slot).run runnerStore) >>= fun p =>
          (collectInclusionListTransactions
              (StoreTransition := ForkChoiceStoreRun (Store map))
              ((FcMap.lookup store.inclusionLists (htr p.1)).getD FcMap.empty)
              (FcMap.lookupD store.equivocators (htr p.1))
              store.inclusionListTimeliness onlyTimely).run p.2 := by
  simp only [getInclusionListTransactions]
  rw [run_bind]

/-- If committee construction returns `err`,
`getInclusionListTransactions` returns the same error. -/
theorem getInclusionListTransactions_run_error_of_committee
    (store : InclusionListStore map) (state : BeaconState) (slot : Slot)
    (onlyTimely : Bool) (runnerStore : Store map)
    (err : StoreTransitionError)
    (herr : (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun (Store map)) (pureState state) slot).run runnerStore
      = .error err) :
    (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store (pureState state) slot onlyTimely).run runnerStore
      = .error err := by
  rw [getInclusionListTransactions_run_eq, herr, except_bind_error]

/-- If collection returns `err` after committee construction succeeds,
`getInclusionListTransactions` returns the same error. -/
theorem getInclusionListTransactions_run_error_of_collect
    (store : InclusionListStore map) (state : BeaconState) (slot : Slot)
    (onlyTimely : Bool) (runnerStore postCommitteeStore : Store map)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (err : StoreTransitionError)
    (hok : (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun (Store map)) (pureState state) slot).run runnerStore
      = .ok (committee, postCommitteeStore))
    (herr : (collectInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        ((FcMap.lookup store.inclusionLists (htr committee)).getD FcMap.empty)
        (FcMap.lookupD store.equivocators (htr committee))
        store.inclusionListTimeliness onlyTimely).run postCommitteeStore
      = .error err) :
    (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store (pureState state) slot onlyTimely).run runnerStore
      = .error err := by
  rw [getInclusionListTransactions_run_eq, hok, except_bind_ok, herr]

/-- The lists stored under the committee key `k`, or the empty map when the key has none.
`getInclusionListTransactions` reads this map. The `ILStore` namespace continues in
`OnInclusionList.lean`, which imports this module. -/
def ILStore.listsAt (s : InclusionListStore map) (k : Root) : map Root InclusionList :=
  (FcMap.lookup s.inclusionLists k).getD FcMap.empty

/-- The list stored under the committee key `k` at the list root `r`. -/
def ILStore.storedAt (s : InclusionListStore map) (k r : Root) : Option InclusionList :=
  FcMap.lookup (listsAt s k) r

section
variable [LawfulFcMap map Root]

/-- The inclusion-list transactions for `slot` contain each transaction of an honest list.
The hypotheses are:

1. `getInclusionListCommittee (pureState state) slot` returns `committee`.
2. Every list stored under the key `htr committee` has a timeliness entry.
3. `il` is stored under that key at `ilRoot`, with timeliness `true`.
4. The validator of `il` is not an equivocator for that key.

Then the collection succeeds, the runner state does not change, and each transaction of
`il` is in the result. -/
theorem mem_getInclusionListTransactions {σ : Type} (ils : InclusionListStore map)
    (state : BeaconState) (slot : Slot) (s : σ)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (hcommittee : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun σ)
        (pureState state) slot).run s = .ok (committee, s))
    (htotal : TimelinessTotal (ILStore.listsAt ils (htr committee))
        ils.inclusionListTimeliness)
    (ilRoot : Root) (il : InclusionList)
    (hstored : ILStore.storedAt ils (htr committee) ilRoot = some il)
    (htimely : FcMap.lookup ils.inclusionListTimeliness ilRoot = some true)
    (hhonest : (FcMap.lookupD ils.equivocators (htr committee)).contains il.validatorIndex
        = false) :
    ∃ ilTxs, (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun σ)
        ils (pureState state) slot (onlyTimely := true)).run s = .ok (ilTxs, s) ∧
      ∀ tx ∈ il.transactions.toArray, tx ∈ ilTxs := by
  obtain ⟨ilTxs, hrun, hmem⟩ := collectInclusionListTransactions_ok_mem
    (ILStore.listsAt ils (htr committee))
    (FcMap.lookupD ils.equivocators (htr committee)) ils.inclusionListTimeliness s htotal
  refine ⟨ilTxs, ?_, hmem ilRoot il hstored hhonest htimely⟩
  simp only [getInclusionListTransactions]
  rw [run_bind, hcommittee, except_bind_ok]
  exact hrun

/-- The members of the inclusion-list transactions for `slot`. Take a committee run that
returns `committee`. Every list stored under `htr committee` has a timeliness entry. Then
the collection succeeds. A transaction is in the result exactly when a list stored under
that key collects it (`EntryCollects`). -/
theorem getInclusionListTransactions_ok_mem_iff {σ : Type} (ils : InclusionListStore map)
    (state : BeaconState) (slot : Slot) (s : σ)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (hcommittee : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun σ)
        (pureState state) slot).run s = .ok (committee, s))
    (htotal : TimelinessTotal (ILStore.listsAt ils (htr committee))
        ils.inclusionListTimeliness) :
    ∃ ilTxs, (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun σ)
        ils (pureState state) slot (onlyTimely := true)).run s = .ok (ilTxs, s) ∧
      ∀ tx, tx ∈ ilTxs ↔ ∃ (ilRoot : Root) (il : InclusionList),
        ILStore.storedAt ils (htr committee) ilRoot = some il ∧
        EntryCollects (FcMap.lookupD ils.equivocators (htr committee))
          ils.inclusionListTimeliness (ilRoot, il) tx := by
  obtain ⟨ilTxs, hrun, hmem⟩ := collectInclusionListTransactions_ok_mem_iff
    (ILStore.listsAt ils (htr committee))
    (FcMap.lookupD ils.equivocators (htr committee)) ils.inclusionListTimeliness s htotal
  refine ⟨ilTxs, ?_, hmem⟩
  simp only [getInclusionListTransactions]
  rw [run_bind, hcommittee, except_bind_ok]
  exact hrun

end

end
end Wrapper
end Collector

end EthCLSpecs.Proofs.Heze
