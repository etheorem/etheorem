import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.StoreRun

/-!
# Collecting inclusion-list transactions

`getInclusionListTransactions` derives the inclusion-list committee for a slot,
looks up the stored lists for that committee root, and gathers their
transactions. The inner walk is `collectInclusionListTransactions`.

This module proves the committee run equation, the empty-committee arithmetic
error, a predicate for the first reachable missing timeliness key in the
`FcMap.fold` entries array, and how both classes of collector error propagate
through `getInclusionListTransactions`.

`collectInclusionListTransactions` is a plain `def`. Helper theorems stay
untagged.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap throwArithmetic htr StoreTransitionError arrayUnion)
open EthCLSpecs.Heze (Preset Store State Root Slot ValidatorIndex InclusionList Transaction
  InclusionListStore getInclusionListCommittee getInclusionListTransactions
  collectInclusionListTransactions getBeaconCommittee getCommitteeCountPerSlot
  computeEpochAtSlot cyclicSample)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)

/-- `.run` of `throwArithmetic` at the fork-choice store runner. Closes by `rfl`
without unfolding `liftErr`. -/
private theorem throwArithmetic_run {σ α : Type} (descr : String) (s : σ) :
    (throwArithmetic (m := ForkChoiceStoreRun σ) (E := StoreTransitionError) descr
        : ForkChoiceStoreRun σ α).run s
      = .error (.transition (.arithmetic descr)) :=
  rfl

/-- Complete `.run` equation of `getInclusionListCommittee`. The concatenated
indices expression is the one in the source. An empty array throws the
empty-committee arithmetic error. A nonempty array returns `cyclicSample` of
that array and leaves the runner state unchanged. The committee accessor does
not read the runner state, so the equation holds for an arbitrary `σ`. -/
theorem getInclusionListCommittee_run_eq
    {σ : Type} [Preset] [HasherTag] :
    ∀ (state : State) (slot : Slot) (runnerStore : σ),
      let indices :=
        (Array.range (getCommitteeCountPerSlot state (computeEpochAtSlot slot))).foldl
          (fun acc i => acc ++ getBeaconCommittee state slot i)
          (#[] : Array ValidatorIndex)
      (getInclusionListCommittee
          (StoreTransition := ForkChoiceStoreRun σ) state slot).run runnerStore =
        if indices.size == 0 then
          .error (.transition (.arithmetic
            "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee"))
        else
          .ok (cyclicSample indices inclusionListCommitteeSize, runnerStore) := by
  intro state slot runnerStore
  simp only [getInclusionListCommittee]
  split
  · rw [ForkChoiceStoreRun.run_bind, throwArithmetic_run]
    exact ForkChoiceStoreRun.except_bind_error _ _
  · rw [ForkChoiceStoreRun.run_bind, ForkChoiceStoreRun.run_pure, ForkChoiceStoreRun.except_bind_ok, ForkChoiceStoreRun.run_pure]

/-- Exact empty-committee error of `getInclusionListCommittee`. -/
theorem getInclusionListCommittee_run_error_of_empty
    {σ : Type} [Preset] [HasherTag]
    (state : State) (slot : Slot) (runnerStore : σ)
    (h : ((Array.range (getCommitteeCountPerSlot state (computeEpochAtSlot slot))).foldl
        (fun acc i => acc ++ getBeaconCommittee state slot i)
        (#[] : Array ValidatorIndex)).size = 0) :
    (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun σ) state slot).run runnerStore
      = .error (.transition (.arithmetic
          "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee")) := by
  have heq := getInclusionListCommittee_run_eq (σ := σ) state slot runnerStore
  rw [heq]
  split
  · rfl
  · rename_i hne
    have hbeq : ((Array.foldl (fun acc i => acc ++ getBeaconCommittee state slot i) #[]
        (Array.range (getCommitteeCountPerSlot state (computeEpochAtSlot slot)))).size == 0) = true :=
      beq_iff_eq.mpr h
    exact (hne hbeq).elim

/-- `entry` does not fail a timeliness read. An equivocator entry skips the
lookup. A non-equivocator entry whose list root is already in `timeliness`
performs a successful lookup. -/
def timelinessEntryDoesNotError {map : MapKind} [Preset] [FcMap map]
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
def FirstReachableMissingTimeliness {map : MapKind} [Preset] [FcMap map]
    (entries : Array (Root × InclusionList))
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (ilRoot : Root) : Prop :=
  ∃ (i : Nat) (il : InclusionList) (hi : i < entries.size),
    entries[i]'hi = (ilRoot, il)
      ∧ (∀ (j : Nat) (hj : j < i),
          timelinessEntryDoesNotError equivocators timeliness
            (entries[j]'(Nat.lt_trans hj hi)))
      ∧ equivocators.contains il.validatorIndex = false
      ∧ FcMap.lookup timeliness ilRoot = none

/-- One step of the `collectInclusionListTransactions` `foldlM` body, at the
fork-choice store runner. The step does not read the runner state. -/
private def collectStep {map : MapKind} [Preset] [FcMap map] {σ : Type}
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
    {map : MapKind} [Preset] [FcMap map] {σ : Type}
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

private theorem collectStep_run_error_of_missing
    {map : MapKind} [Preset] [FcMap map] {σ : Type}
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (onlyTimely : Bool) (acc : Array Transaction)
    (ilRoot : Root) (il : InclusionList) (s : σ)
    (honly : onlyTimely = true)
    (hnot : equivocators.contains il.validatorIndex = false)
    (hnone : FcMap.lookup timeliness ilRoot = none) :
    (collectStep (σ := σ) equivocators timeliness onlyTimely acc (ilRoot, il)).run s
      = .error (.missingKey ilRoot) := by
  have hmem : ¬ (il.validatorIndex ∈ equivocators) := by
    rw [Array.contains_eq_mem] at hnot
    exact of_decide_eq_false hnot
  simp [collectStep, hmem, honly, FcMap.getOrThrow, FcMap.getOrThrowKey, hnone]
  rfl

private theorem collectStep_run_ok_of_skip
    {map : MapKind} [Preset] [FcMap map] {σ : Type}
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (onlyTimely : Bool) (acc : Array Transaction)
    (entry : Root × InclusionList) (s : σ)
    (honly : onlyTimely = true)
    (hok : timelinessEntryDoesNotError equivocators timeliness entry) :
    ∃ acc', (collectStep (σ := σ) equivocators timeliness onlyTimely acc entry).run s
      = .ok (acc', s) := by
  obtain ⟨ilRoot, il⟩ := entry
  cases hcont : equivocators.contains il.validatorIndex
  · have hsome : (FcMap.lookup timeliness ilRoot).isSome = true := by
      cases hok with
      | inl hmem =>
        nomatch hcont.symm.trans hmem
      | inr h => exact h
    match hlookup : FcMap.lookup timeliness ilRoot with
    | none =>
      simp [hlookup] at hsome
    | some b =>
      simp only [collectStep, hcont, honly]
      simp only [FcMap.getOrThrow, FcMap.getOrThrowKey, hlookup]
      cases b
      · exact ⟨acc, rfl⟩
      · exact ⟨acc ++ il.transactions.toArray, rfl⟩
  · simp only [collectStep, hcont]
    exact ⟨acc, rfl⟩

private theorem foldlM_collectStep_run_ok_of_all_skip
    {map : MapKind} [Preset] [FcMap map] {σ : Type}
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool)
    (onlyTimely : Bool) (honly : onlyTimely = true)
    (l : List (Root × InclusionList))
    (hall : ∀ x ∈ l, timelinessEntryDoesNotError equivocators timeliness x)
    (acc : Array Transaction) (s : σ) :
    ∃ acc',
      (l.foldlM (collectStep (σ := σ) equivocators timeliness onlyTimely) acc).run s
        = .ok (acc', s) := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldlM_nil]
    exact ⟨acc, rfl⟩
  | cons a rest ih =>
    obtain ⟨acc1, hstep⟩ :=
      collectStep_run_ok_of_skip (σ := σ) equivocators timeliness onlyTimely acc a s honly
        (hall a List.mem_cons_self)
    rw [List.foldlM_cons, ForkChoiceStoreRun.run_bind, hstep, ForkChoiceStoreRun.except_bind_ok]
    exact ih (fun x hx => hall x (List.mem_cons.mpr (Or.inr hx))) acc1


/-- If `onlyTimely = true` and the first reachable missing timeliness key in the
`FcMap.fold` entries array is `ilRoot`, collection fails with `.missingKey ilRoot`.
The collector does not read the runner state, so the equation holds for an
arbitrary `σ`. -/
theorem collectInclusionListTransactions_run_error_of_first_missing
    {map : MapKind} [Preset] [FcMap map] {σ : Type}
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
  rw [collectInclusionListTransactions_eq]
  rw [ForkChoiceStoreRun.run_bind]
  let entries := FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[] inclusionLists
  obtain ⟨i, il, hi, hget, hpref, hnot, hnone⟩ := hfirst
  have hfold :
      (entries.foldlM (collectStep (σ := σ) equivocators timeliness onlyTimely) #[]).run runnerStore
        = .error (.missingKey ilRoot) := by
    rw [← Array.foldlM_toList]
    have hi' : i < entries.toList.length := by simpa [Array.length_toList] using hi
    rw [← List.take_append_drop (l := entries.toList) i, List.drop_eq_getElem_cons hi']
    have hget' : entries.toList[i]'hi' = (ilRoot, il) := by
      rw [Array.getElem_toList]; exact hget
    simp only [hget']
    rw [List.foldlM_append, ForkChoiceStoreRun.run_bind]
    obtain ⟨acc', hpre⟩ :=
      foldlM_collectStep_run_ok_of_all_skip (σ := σ) equivocators timeliness onlyTimely honly
        (entries.toList.take i)
        (fun x hx => by
          obtain ⟨j, hj, rfl⟩ := (List.mem_take_iff_getElem).1 hx
          have hj_lt_i : j < i := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
          have := hpref j hj_lt_i
          simpa [Array.getElem_toList] using this)
        #[] runnerStore
    rw [hpre, ForkChoiceStoreRun.except_bind_ok]
    rw [List.foldlM_cons, ForkChoiceStoreRun.run_bind,
      collectStep_run_error_of_missing (σ := σ) equivocators timeliness onlyTimely acc' ilRoot il
        runnerStore honly hnot hnone]
    exact ForkChoiceStoreRun.except_bind_error _ _
  rw [hfold]
  exact ForkChoiceStoreRun.except_bind_error _ _

/-- `.run` of `getInclusionListTransactions` is the committee run bound to
collection at the committee's stored lists. -/
private theorem getInclusionListTransactions_run
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    (store : InclusionListStore map) (state : State) (slot : Slot)
    (onlyTimely : Bool) (runnerStore : Store map) :
    (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store state slot onlyTimely).run runnerStore
      = ((getInclusionListCommittee
            (StoreTransition := ForkChoiceStoreRun (Store map))
            state slot).run runnerStore) >>= fun p =>
          (collectInclusionListTransactions
              (StoreTransition := ForkChoiceStoreRun (Store map))
              ((FcMap.lookup store.inclusionLists (htr p.1)).getD FcMap.empty)
              (FcMap.lookupD store.equivocators (htr p.1))
              store.inclusionListTimeliness onlyTimely).run p.2 := by
  simp only [getInclusionListTransactions]
  rw [ForkChoiceStoreRun.run_bind]

/-- A committee error is the transaction-collection error. -/
theorem getInclusionListTransactions_run_error_of_committee
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    (store : InclusionListStore map) (state : State) (slot : Slot)
    (onlyTimely : Bool) (runnerStore : Store map)
    (err : StoreTransitionError)
    (herr : (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun (Store map)) state slot).run runnerStore
      = .error err) :
    (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store state slot onlyTimely).run runnerStore
      = .error err := by
  rw [getInclusionListTransactions_run, herr, ForkChoiceStoreRun.except_bind_error]

/-- A collection error after a successful committee run is the
transaction-collection error. -/
theorem getInclusionListTransactions_run_error_of_collect
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    (store : InclusionListStore map) (state : State) (slot : Slot)
    (onlyTimely : Bool) (runnerStore postCommitteeStore : Store map)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (err : StoreTransitionError)
    (hok : (getInclusionListCommittee
        (StoreTransition := ForkChoiceStoreRun (Store map)) state slot).run runnerStore
      = .ok (committee, postCommitteeStore))
    (herr : (collectInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        ((FcMap.lookup store.inclusionLists (htr committee)).getD FcMap.empty)
        (FcMap.lookupD store.equivocators (htr committee))
        store.inclusionListTimeliness onlyTimely).run postCommitteeStore
      = .error err) :
    (getInclusionListTransactions
        (StoreTransition := ForkChoiceStoreRun (Store map))
        store state slot onlyTimely).run runnerStore
      = .error err := by
  rw [getInclusionListTransactions_run, hok, ForkChoiceStoreRun.except_bind_ok, herr]

end EthCLSpecs.Proofs.Heze
