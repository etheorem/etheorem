import EthCLLib.Proofs.EngineLaws
import EthCLSpecs.Proofs.Heze.NodeTrace
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction

/-!
# `EthCLSpecs.Proofs.Heze.ILStoreOrder`: the order of the arrivals does not matter

`ilStoreOfArrivals` folds `processInclusionList` over an arrival list
(`OnInclusionList.lean`). The fold result depends on the order of the arrivals. The maps
keep the entries in insertion order. The first arrival of a list from a validator at a key
sets the stored entry and its timeliness. This module proves that the collected
transactions depend only on the timeliness of the first arrival of each list
(`Arrivals.firstTimely`).

`ILStore.Describes` states the fold result in closed form, for an arrival list `arr`:

- A validator is an equivocator at a key exactly when `arr` holds two different lists from
  it at that key (`Arrivals.Equivocates`).
- The entry at a key for a validator is its first arrival there (`Arrivals.firstFrom`): the
  signed list and the timeliness bit of that arrival.

`ilStoreOfArrivals_describes` proves it, with no hypothesis. The induction runs over the
arrivals that remain after a processed prefix. Each step is one of the three branches of
`processInclusionList`. The store keys an entry by the key of its list and its validator,
so no two lists share a slot in the store.

Collection skips an equivocator, so the entry of an equivocator never reaches the result.
`mem_getInclusionListTransactions_iff_collected` states the members of the result: the
transactions of the lists that `Arrivals.Collected` names. `Collected` reads `arr` only
through `firstTimely`, because a list arrived exactly when its `firstTimely` is `some _`.

`getInclusionListTransactions_order_independent` states the main result. Two arrival lists
with the same `firstTimely` give results with the same members. The order of the result
arrays can differ. The EL answer depends only on the members
(`LawfulInclusionList.satisfied_iff`). So
`recordPayloadInclusionListSatisfaction_order_independent` records the same answer, when
both stores walk to the same dependent root. `NodeTrace.answer_order_independent` states
it for two node traces.

The statements cover every key at once.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (ForkChoiceStoreRun LawfulFcMap LawfulInclusionList)
open EthCLSpecs.Heze (Preset Config Store Root Slot InclusionList InclusionListStore
  InclusionListEntry SignedInclusionList Transaction ValidatorIndex ExecutionPayload
  ExecutionRequests BeaconBlock processInclusionList getInclusionListTransactions
  inclusionListItems isInclusionListSatisfied recordPayloadInclusionListSatisfaction
  getShufflingDependentRoot computeEpochAtSlot)

section
variable [Preset]

namespace Arrivals

/-- The list `l` arrives in `arr`. -/
def Arrived (arr : List (SignedInclusionList × Bool)) (l : InclusionList) : Prop :=
  ∃ a ∈ arr, a.1.message = l

/-- The list `l` comes from the validator `v` at the key `k`. -/
def FromAt (k : Slot × Root) (v : ValidatorIndex) (l : InclusionList) : Prop :=
  ilKey l = k ∧ l.validatorIndex = v

/-- `arr` holds two different lists from the validator `v` at the key `k`. -/
def Equivocates (arr : List (SignedInclusionList × Bool)) (k : Slot × Root)
    (v : ValidatorIndex) : Prop :=
  ∃ l₁ l₂, Arrived arr l₁ ∧ Arrived arr l₂ ∧ FromAt k v l₁ ∧ FromAt k v l₂ ∧ l₁ ≠ l₂

/-- The first arrival in `arr` of a list from the validator `v` at the key `k`. -/
def firstFrom (arr : List (SignedInclusionList × Bool)) (k : Slot × Root)
    (v : ValidatorIndex) : Option (SignedInclusionList × Bool) :=
  arr.find? (fun a => ilKey a.1.message == k && a.1.message.validatorIndex == v)

/-- The timeliness of the first arrival of the list `l` in `arr`, or `none` when `l` does
not arrive. -/
def firstTimely (arr : List (SignedInclusionList × Bool)) (l : InclusionList) :
    Option Bool :=
  (arr.find? (fun a => a.1.message == l)).map (·.2)

/-- Collection at the key `k` keeps the transaction `tx`. Some list `l` of `arr` meets three
conditions:

- `l` is at `k` and carries `tx`.
- The validator of `l` does not equivocate at `k`.
- The first arrival of `l` is timely. -/
def Collected (arr : List (SignedInclusionList × Bool)) (k : Slot × Root) (tx : Transaction) :
    Prop :=
  ∃ l, Arrived arr l ∧ ilKey l = k ∧ ¬ Equivocates arr k l.validatorIndex ∧
    firstTimely arr l = some true ∧ tx ∈ l.transactions.toArray

/-- A list arrives in `arr ++ [a]` when it arrives in `arr` or is the message of `a`. -/
theorem arrived_append (arr : List (SignedInclusionList × Bool))
    (a : SignedInclusionList × Bool) (l : InclusionList) :
    Arrived (arr ++ [a]) l ↔ Arrived arr l ∨ a.1.message = l := by
  simp [Arrived, or_and_right, exists_or]

/-- A later arrival keeps every earlier arrival. -/
theorem arrived_of_append {arr : List (SignedInclusionList × Bool)}
    {a : SignedInclusionList × Bool} {l : InclusionList} (h : Arrived arr l) :
    Arrived (arr ++ [a]) l :=
  (arrived_append arr a l).mpr (Or.inl h)

/-- `firstFrom` returns an arrival of `arr` whose list comes from `v` at `k`. -/
theorem firstFrom_some {arr : List (SignedInclusionList × Bool)} {k : Slot × Root}
    {v : ValidatorIndex} {a : SignedInclusionList × Bool} (h : firstFrom arr k v = some a) :
    a ∈ arr ∧ FromAt k v a.1.message := by
  unfold firstFrom at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-- `firstFrom` returns `none` exactly when no list of `arr` comes from `v` at `k`. -/
theorem firstFrom_eq_none {arr : List (SignedInclusionList × Bool)} {k : Slot × Root}
    {v : ValidatorIndex} :
    firstFrom arr k v = none ↔ ∀ l, Arrived arr l → ¬ FromAt k v l := by
  unfold firstFrom Arrived FromAt
  simp only [List.find?_eq_none, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro h l ⟨a, ha, rfl⟩ hf
    exact h a ha hf
  · intro h a ha hf
    exact h a.1.message ⟨a, ha, rfl⟩ hf

/-- A validator that does not equivocate sent one list at the key: the list of its first
arrival. -/
theorem eq_of_firstFrom {arr : List (SignedInclusionList × Bool)} {k : Slot × Root}
    {v : ValidatorIndex} {a : SignedInclusionList × Bool} {l' : InclusionList}
    (h : firstFrom arr k v = some a) (hne : ¬ Equivocates arr k v) (ha : Arrived arr l')
    (hf : FromAt k v l') : l' = a.1.message := by
  obtain ⟨hal, hfl⟩ := firstFrom_some h
  exact Classical.byContradiction fun hne' => hne ⟨l', a.1.message, ha, ⟨a, hal, rfl⟩, hf, hfl, hne'⟩

/-- A later arrival keeps `firstFrom` at `k` and `v` in two cases. `arr` already holds a
list from `v` at `k`, or the arrival does not come from `v` at `k`. -/
theorem firstFrom_append_eq {arr : List (SignedInclusionList × Bool)}
    (a : SignedInclusionList × Bool) {k : Slot × Root} {v : ValidatorIndex}
    (h : FromAt k v a.1.message → ∃ l, Arrived arr l ∧ FromAt k v l) :
    firstFrom (arr ++ [a]) k v = firstFrom arr k v := by
  unfold firstFrom
  rw [List.find?_append]
  cases hs : arr.find? (fun a => ilKey a.1.message == k && a.1.message.validatorIndex == v) with
  | some x => rfl
  | none =>
    have hnot : ¬ FromAt k v a.1.message := by
      intro hf
      obtain ⟨l, hl, hfl⟩ := h hf
      have hnone : firstFrom arr k v = none := hs
      exact firstFrom_eq_none.mp hnone l hl hfl
    have hb : (ilKey a.1.message == k && a.1.message.validatorIndex == v) = false := by
      rw [Bool.eq_false_iff]
      simpa [FromAt] using hnot
    simp [List.find?, hb]

/-- The first arrival from `v` at `k` is the last arrival, when `arr` holds no list from `v`
at `k` and the last arrival comes from `v` at `k`. -/
theorem firstFrom_append_self {arr : List (SignedInclusionList × Bool)}
    (a : SignedInclusionList × Bool) {k : Slot × Root} {v : ValidatorIndex}
    (hnone : firstFrom arr k v = none) (hf : FromAt k v a.1.message) :
    firstFrom (arr ++ [a]) k v = some a := by
  unfold firstFrom at hnone ⊢
  rw [List.find?_append, hnone]
  obtain ⟨hk, hv⟩ := hf
  simp [List.find?, hk, hv]

/-- A new equivocation at `k` and `v` needs the arrival to come from `v` at `k`, and a
different list from `v` at `k` in `arr`. -/
theorem equivocates_append (arr : List (SignedInclusionList × Bool))
    (a : SignedInclusionList × Bool) (k : Slot × Root) (v : ValidatorIndex) :
    Equivocates (arr ++ [a]) k v ↔ Equivocates arr k v ∨
      (FromAt k v a.1.message ∧ ∃ l, Arrived arr l ∧ FromAt k v l ∧ l ≠ a.1.message) := by
  constructor
  · rintro ⟨l₁, l₂, h₁, h₂, f₁, f₂, hne⟩
    rcases (arrived_append arr a l₁).mp h₁ with h₁ | rfl <;>
      rcases (arrived_append arr a l₂).mp h₂ with h₂ | rfl
    · exact Or.inl ⟨l₁, l₂, h₁, h₂, f₁, f₂, hne⟩
    · exact Or.inr ⟨f₂, l₁, h₁, f₁, hne⟩
    · exact Or.inr ⟨f₁, l₂, h₂, f₂, Ne.symm hne⟩
    · exact absurd rfl hne
  · rintro (⟨l₁, l₂, h₁, h₂, f₁, f₂, hne⟩ | ⟨hf, l, hl, hfl, hne⟩)
    · exact ⟨l₁, l₂, arrived_of_append h₁, arrived_of_append h₂, f₁, f₂, hne⟩
    · exact ⟨l, a.1.message, arrived_of_append hl, (arrived_append arr a _).mpr (Or.inr rfl),
        hfl, hf, hne⟩

/-- A list arrives exactly when it has a first timeliness. -/
theorem arrived_iff_isSome (arr : List (SignedInclusionList × Bool)) (l : InclusionList) :
    Arrived arr l ↔ (firstTimely arr l).isSome := by
  simp [firstTimely, Arrived, List.find?_isSome]

omit [Preset] in
/-- Two predicates that agree on every element of a list find the same element. -/
theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, p x = q x) → xs.find? p = xs.find? q := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x rest ih =>
    intro h
    simp only [List.find?_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- The first arrival from a validator that does not equivocate at `k` is the first arrival
of its list. So the timeliness of that arrival is the first timeliness of the list. -/
theorem firstTimely_of_firstFrom {arr : List (SignedInclusionList × Bool)} {k : Slot × Root}
    {v : ValidatorIndex} {a : SignedInclusionList × Bool} (h : firstFrom arr k v = some a)
    (hne : ¬ Equivocates arr k v) : firstTimely arr a.1.message = some a.2 := by
  have hfa := (firstFrom_some h).2
  -- On `arr`, "the list is `a.1.message`" and "the list comes from `v` at `k`" agree.
  have hagree : ∀ x ∈ arr, (x.1.message == a.1.message) =
      (ilKey x.1.message == k && x.1.message.validatorIndex == v) := by
    intro x hx
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Bool.and_eq_true]
    constructor
    · intro hxa
      rw [hxa]
      exact hfa
    · intro hxf
      exact eq_of_firstFrom h hne ⟨x, hx, rfl⟩ hxf
  unfold firstTimely
  rw [find?_congr arr hagree]
  change (firstFrom arr k v).map (·.2) = _
  rw [h]
  rfl

section Congr
variable {arr₁ arr₂ : List (SignedInclusionList × Bool)}
  (h : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
include h

/-- Two arrival lists with the same `firstTimely` have the same arrived lists. -/
theorem arrived_congr (l : InclusionList) : Arrived arr₁ l ↔ Arrived arr₂ l := by
  rw [arrived_iff_isSome, arrived_iff_isSome, h]

/-- Two arrival lists with the same `firstTimely` have the same equivocators. -/
theorem equivocates_congr (k : Slot × Root) (v : ValidatorIndex) :
    Equivocates arr₁ k v ↔ Equivocates arr₂ k v := by
  simp only [Equivocates, arrived_congr h]

/-- `Collected` reads the arrival list only through `firstTimely`. -/
theorem collected_congr (k : Slot × Root) (tx : Transaction) :
    Collected arr₁ k tx ↔ Collected arr₂ k tx := by
  simp only [Collected, arrived_congr h, equivocates_congr h, h]

end Congr

end Arrivals

open Arrivals

/-- Under `LawfulInclusionList`, the EL answer depends only on the members of the
transaction array. -/
theorem isInclusionListSatisfied_congr_mem
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    (payload : ExecutionPayload) {ilTxs₁ ilTxs₂ : Array Transaction}
    (h : ∀ tx, tx ∈ ilTxs₁ ↔ tx ∈ ilTxs₂) :
    isInclusionListSatisfied payload ilTxs₁ = isInclusionListSatisfied payload ilTxs₂ := by
  apply Bool.eq_iff_iff.mpr
  refine (hel.satisfied_iff payload ilTxs₁).trans
    (Iff.trans ?_ (hel.satisfied_iff payload ilTxs₂).symm)
  simp only [h]

variable [HasherTag] {map : MapKind} [FcMap map]

/-- The entry of an arrival: its signed list and its timeliness bit. -/
def entryOf (a : SignedInclusionList × Bool) : InclusionListEntry :=
  { signedInclusionList := a.1, timely := a.2 }

namespace ILStore

/-- The closed form of the IL store after the arrival list `arr`: the equivocators and the
entries, each stated through `arr` alone. -/
structure Describes (arr : List (SignedInclusionList × Bool))
    (s : InclusionListStore map) : Prop where
  /-- The equivocators at `k` are the validators with two different lists at `k`. -/
  equiv : ∀ k v, (FcMap.lookupD s.equivocators k).contains v = true ↔ Equivocates arr k v
  /-- The entry at `k` for `v` is the first arrival from `v` at `k`. -/
  entry : ∀ k v, entryAt s k v = (firstFrom arr k v).map entryOf

variable [LawfulFcMap map (Slot × Root)] [LawfulFcMap map ValidatorIndex]

/-- The empty IL store describes the empty arrival list. -/
theorem describes_nil : Describes [] (InclusionListStore.empty : InclusionListStore map) := by
  refine ⟨fun k v => ?_, fun k v => ?_⟩
  · rw [(before_empty v k).2]
    simp [Equivocates, Arrived]
  · rw [(before_empty v k).1]
    rfl

/-- One fold step keeps `Describes`. -/
theorem describes_step {arr : List (SignedInclusionList × Bool)}
    (a : SignedInclusionList × Bool) {s : InclusionListStore map} (h : Describes arr s) :
    Describes (arr ++ [a]) (arrivalStep s a) := by
  obtain ⟨signed, b⟩ := a
  change Describes _ (processInclusionList s signed b)
  -- `m` is the arriving list, from the validator `v₀` at the key `k₀`.
  have hmsg : ((signed, b) : SignedInclusionList × Bool).1.message = signed.message := rfl
  have hentry0 := h.entry (ilKey signed.message) signed.message.validatorIndex
  cases hff : firstFrom arr (ilKey signed.message) signed.message.validatorIndex with
  | some a0 =>
    -- A stored entry: the first arrival `a0` from the validator at the key.
    rw [hff] at hentry0
    obtain ⟨ha0, hfa0⟩ := firstFrom_some hff
    have hfirst : ∀ k v, FromAt k v ((signed, b) : SignedInclusionList × Bool).1.message →
        ∃ l, Arrived arr l ∧ FromAt k v l := by
      rintro k v ⟨hk, hv⟩
      subst hk hv
      exact ⟨a0.1.message, ⟨a0, ha0, rfl⟩, hfa0⟩
    -- The entries do not change, and neither does `firstFrom`.
    have hkeep : ∀ s' : InclusionListStore map, s'.inclusionLists = s.inclusionLists →
        (∀ k v, (FcMap.lookupD s'.equivocators k).contains v = true ↔
          Equivocates (arr ++ [(signed, b)]) k v) →
        Describes (arr ++ [(signed, b)]) s' := by
      intro s' hlists hequiv
      refine ⟨hequiv, fun k v => ?_⟩
      rw [firstFrom_append_eq _ (hfirst k v), ← h.entry k v]
      simp only [entryAt, entriesAt, hlists]
    have hentry : FcMap.lookup ((FcMap.lookup s.inclusionLists (ilKey signed.message)).getD
        FcMap.empty) signed.message.validatorIndex = some (entryOf a0) := hentry0
    unfold ilKey at hentry
    by_cases hsame : a0.1.message = signed.message
    · -- The same list again: the store does not change.
      have hA : processInclusionList s signed b = s := by
        simp only [processInclusionList, hentry, entryOf, hsame, bne, beq_self_eq_true,
          Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
      rw [hA]
      refine hkeep s rfl (fun k v => ?_)
      rw [h.equiv, equivocates_append, hmsg]
      constructor
      · exact Or.inl
      · rintro (he | ⟨⟨hk, hv⟩, l, hl, hfl, hne⟩)
        · exact he
        · -- A different earlier list from the same validator: already an equivocation.
          subst hk hv
          exact ⟨l, a0.1.message, hl, ⟨a0, ha0, rfl⟩, hfl, hfa0, hsame ▸ hne⟩
    · have hE : Equivocates (arr ++ [(signed, b)]) (ilKey signed.message)
          signed.message.validatorIndex :=
        (equivocates_append _ _ _ _).mpr (Or.inr ⟨⟨rfl, rfl⟩, a0.1.message, ⟨a0, ha0, rfl⟩,
          hfa0, hsame⟩)
      have hequivAll : ∀ k v, Equivocates (arr ++ [(signed, b)]) k v ↔
          Equivocates arr k v ∨ (k = ilKey signed.message ∧ v = signed.message.validatorIndex) := by
        intro k v
        rw [equivocates_append, hmsg]
        constructor
        · rintro (he | ⟨⟨hk, hv⟩, -⟩)
          · exact Or.inl he
          · exact Or.inr ⟨hk.symm, hv.symm⟩
        · rintro (he | ⟨rfl, rfl⟩)
          · exact Or.inl he
          · exact ((equivocates_append _ _ _ _).mp hE)
      by_cases hc : (FcMap.lookupD s.equivocators (ilKey signed.message)).contains
          signed.message.validatorIndex = true
      · -- A known equivocator: the store does not change.
        have hA : processInclusionList s signed b = s := by
          unfold ilKey at hc
          have hne : (a0.1.message != signed.message) = true := by simpa [bne] using hsame
          simp only [processInclusionList, hentry, entryOf, hne, hc, Bool.not_true,
            Bool.and_false, Bool.false_eq_true, ite_false]
        rw [hA]
        refine hkeep s rfl (fun k v => ?_)
        rw [h.equiv, hequivAll]
        constructor
        · exact Or.inl
        · rintro (he | ⟨rfl, rfl⟩)
          · exact he
          · exact (h.equiv _ _).mp hc
      · -- A different list: the validator joins the equivocators at the key.
        have hcf : (FcMap.lookupD s.equivocators (ilKey signed.message)).contains
            signed.message.validatorIndex = false := by simpa using hc
        have hB : processInclusionList s signed b = withEquivocator s signed.message := by
          unfold ilKey at hcf
          have hne : (a0.1.message != signed.message) = true := by simpa [bne] using hsame
          simp only [processInclusionList, hentry, entryOf, hne, hcf, Bool.not_false,
            Bool.and_self, ite_true]
          rfl
        rw [hB]
        refine hkeep _ rfl (fun k v => ?_)
        rw [equivocators_withEquivocator, Bool.or_eq_true, h.equiv, hequivAll]
        simp only [Bool.and_eq_true, beq_iff_eq]
  | none =>
    -- No entry: the arrival is the first list from its validator at its key.
    rw [hff] at hentry0
    have hentry : FcMap.lookup ((FcMap.lookup s.inclusionLists (ilKey signed.message)).getD
        FcMap.empty) signed.message.validatorIndex = none := hentry0
    unfold ilKey at hentry
    have hC : processInclusionList s signed b = withStored s signed b := by
      simp only [processInclusionList, hentry]
      rfl
    rw [hC]
    refine ⟨fun k v => ?_, fun k v => ?_⟩
    · -- The equivocators do not change, and the arrival starts no equivocation.
      change (FcMap.lookupD s.equivocators k).contains v = true ↔ _
      rw [h.equiv, equivocates_append]
      constructor
      · exact Or.inl
      · rintro (he | ⟨⟨hk, hv⟩, l, hl, hfl, -⟩)
        · exact he
        · subst hk hv
          exact absurd hfl (firstFrom_eq_none.mp hff l hl)
    · rw [entryAt_withStored]
      split
      · rename_i hkv
        obtain ⟨rfl, rfl⟩ := hkv
        rw [firstFrom_append_self _ hff ⟨rfl, rfl⟩]
        rfl
      · rename_i hkv
        rw [firstFrom_append_eq _ (fun hf => absurd ⟨hf.1.symm, hf.2.symm⟩ hkv), h.entry k v]

end ILStore

variable [LawfulFcMap map (Slot × Root)] [LawfulFcMap map ValidatorIndex]

/-- The IL store after the arrival list `arr` has the closed form `ILStore.Describes`. -/
theorem ilStoreOfArrivals_describes (arr : List (SignedInclusionList × Bool)) :
    ILStore.Describes arr (ilStoreOfArrivals (map := map) arr) := by
  -- Induction over the rest of the list, with the processed prefix `pre` and its store.
  suffices h : ∀ (rest pre : List (SignedInclusionList × Bool)) (s : InclusionListStore map),
      ILStore.Describes pre s →
      ILStore.Describes (pre ++ rest) (rest.foldl ILStore.arrivalStep s) from
    h arr [] _ ILStore.describes_nil
  intro rest
  induction rest with
  | nil => intro pre s hD; simpa using hD
  | cons a rest ih =>
    intro pre s hD
    have hassoc : pre ++ a :: rest = (pre ++ [a]) ++ rest := by simp
    rw [hassoc]
    exact ih _ _ (ILStore.describes_step a hD)

/-- The timely inclusion-list transactions at `(slot, dependentRoot)`, after the arrival
list `arr`. A transaction is in the result exactly when `Collected arr (slot,
dependentRoot)` holds for it. -/
theorem mem_getInclusionListTransactions_iff_collected
    (arr : List (SignedInclusionList × Bool)) (slot : Slot) (dependentRoot : Root)
    (tx : Transaction) :
    tx ∈ getInclusionListTransactions (ilStoreOfArrivals (map := map) arr) slot dependentRoot
        (onlyTimely := true) ↔
      Collected arr (slot, dependentRoot) tx := by
  have hD := ilStoreOfArrivals_describes (map := map) arr
  rw [mem_getInclusionListTransactions_iff]
  constructor
  · rintro ⟨⟨vi, e⟩, hitem, hequiv, htimely, htx⟩
    have he := (mem_inclusionListItems_iff _ _ _ vi e).mp hitem
    rw [hD.entry] at he
    obtain ⟨a, hff, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨ha, hk, hv⟩ := firstFrom_some hff
    have hne : ¬ Equivocates arr (slot, dependentRoot) vi := fun hE => by
      have := (hD.equiv _ _).mpr hE
      simp_all
    refine ⟨a.1.message, ⟨a, ha, rfl⟩, hk, hv ▸ hne, ?_, htx⟩
    rw [firstTimely_of_firstFrom hff hne]
    exact congrArg some (htimely rfl)
  · rintro ⟨l, hl, hk, hne, ht, htx⟩
    -- The first arrival from the validator of `l` at the key carries `l`.
    cases hff : firstFrom arr (slot, dependentRoot) l.validatorIndex with
    | none => exact absurd ⟨hk, rfl⟩ (firstFrom_eq_none.mp hff l hl)
    | some a =>
      have hla := eq_of_firstFrom hff hne hl ⟨hk, rfl⟩
      have hentry : ILStore.entryAt (ilStoreOfArrivals (map := map) arr) (slot, dependentRoot)
          l.validatorIndex = some (entryOf a) := by
        rw [hD.entry, hff]
        rfl
      refine ⟨(l.validatorIndex, entryOf a),
        (mem_inclusionListItems_iff _ _ _ _ _).mpr hentry, ?_, fun _ => ?_, ?_⟩
      · cases hc : (FcMap.lookupD (ilStoreOfArrivals (map := map) arr).equivocators
            (slot, dependentRoot)).contains l.validatorIndex
        · rfl
        · exact absurd ((hD.equiv _ _).mp hc) hne
      · have hfa := firstTimely_of_firstFrom hff hne
        rw [← hla, ht] at hfa
        exact (Option.some.inj hfa).symm
      · change tx ∈ a.1.message.transactions.toArray
        rw [← hla]
        exact htx

/-- Order independence. Take two arrival lists with the same first timeliness for every
list. At every key, the two collections have the same members. -/
theorem getInclusionListTransactions_order_independent
    (arr₁ arr₂ : List (SignedInclusionList × Bool))
    (htimely : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
    (slot : Slot) (dependentRoot : Root) (tx : Transaction) :
    tx ∈ getInclusionListTransactions (ilStoreOfArrivals (map := map) arr₁) slot dependentRoot
        (onlyTimely := true) ↔
      tx ∈ getInclusionListTransactions (ilStoreOfArrivals (map := map) arr₂) slot dependentRoot
        (onlyTimely := true) := by
  rw [mem_getInclusionListTransactions_iff_collected, mem_getInclusionListTransactions_iff_collected]
  exact collected_congr htimely _ tx

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]

/-- The record handler writes the same answer for two stores under `LawfulInclusionList`.
The IL stores of the two stores come from arrival lists with the same first timeliness.
Both stores hold the block at `root`, and both dependent-root walks return the same root. -/
theorem recordPayloadInclusionListSatisfaction_order_independent
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    (store₁ store₂ runner₁ runner₂ post₁ post₂ : Store map)
    (arr₁ arr₂ : List (SignedInclusionList × Bool))
    (hils₁ : store₁.inclusionListStore = ilStoreOfArrivals arr₁)
    (hils₂ : store₂.inclusionListStore = ilStoreOfArrivals arr₂)
    (htimely : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
    (root : Root) (payload : ExecutionPayload) (block : BeaconBlock) (dependentRoot : Root)
    (hblock₁ : FcMap.lookup store₁.blocks root = some block)
    (hblock₂ : FcMap.lookup store₂.blocks root = some block) (hslot : block.slot ≠ 0)
    (hdep₁ : (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store map))
        store₁ root (computeEpochAtSlot (block.slot - 1))).run runner₁
      = .ok (dependentRoot, post₁))
    (hdep₂ : (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store map))
        store₂ root (computeEpochAtSlot (block.slot - 1))).run runner₂
      = .ok (dependentRoot, post₂)) :
    ∃ answer : Bool,
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₁ root payload).run runner₁
        = .ok ({ store₁ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₁.payloadInclusionListSatisfaction root answer }, post₁) ∧
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₂ root payload).run runner₂
        = .ok ({ store₂ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₂.payloadInclusionListSatisfaction root answer }, post₂) := by
  refine ⟨_, recordPayloadInclusionListSatisfaction_run_eq store₁ runner₁ post₁ root payload
    block dependentRoot hblock₁ hslot hdep₁, ?_⟩
  rw [recordPayloadInclusionListSatisfaction_run_eq store₂ runner₂ post₂ root payload block
    dependentRoot hblock₂ hslot hdep₂, hils₁, hils₂,
    isInclusionListSatisfied_congr_mem hel payload
      (getInclusionListTransactions_order_independent arr₁ arr₂ htimely _ _)]

variable [Config] [CryptoBackend] [DataAvailability]

/-- Two node traces, each from a seed with the empty IL store. Their IL arrivals have the
same first timeliness for every list. Both final stores hold the block at `root`, and both
dependent-root walks return the same root. Then the record handler writes the same answer
at both final stores. -/
theorem NodeTrace.answer_order_independent
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    {s0₁ s0₂ store₁ store₂ : Store map} {events₁ events₂ : List TraceEvent}
    {arr₁ arr₂ : List (SignedInclusionList × Bool)}
    (h₁ : NodeTrace s0₁ events₁ arr₁ store₁)
    (hseed₁ : s0₁.inclusionListStore = InclusionListStore.empty)
    (h₂ : NodeTrace s0₂ events₂ arr₂ store₂)
    (hseed₂ : s0₂.inclusionListStore = InclusionListStore.empty)
    (htimely : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
    (runner₁ runner₂ post₁ post₂ : Store map) (root : Root) (payload : ExecutionPayload)
    (block : BeaconBlock) (dependentRoot : Root)
    (hblock₁ : FcMap.lookup store₁.blocks root = some block)
    (hblock₂ : FcMap.lookup store₂.blocks root = some block) (hslot : block.slot ≠ 0)
    (hdep₁ : (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store map))
        store₁ root (computeEpochAtSlot (block.slot - 1))).run runner₁
      = .ok (dependentRoot, post₁))
    (hdep₂ : (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store map))
        store₂ root (computeEpochAtSlot (block.slot - 1))).run runner₂
      = .ok (dependentRoot, post₂)) :
    ∃ answer : Bool,
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₁ root payload).run runner₁
        = .ok ({ store₁ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₁.payloadInclusionListSatisfaction root answer }, post₁) ∧
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₂ root payload).run runner₂
        = .ok ({ store₂ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₂.payloadInclusionListSatisfaction root answer }, post₂) :=
  recordPayloadInclusionListSatisfaction_order_independent hel store₁ store₂ runner₁ runner₂
    post₁ post₂ arr₁ arr₂ (h₁.ilStore hseed₁) (h₂.ilStore hseed₂) htimely root payload block
    dependentRoot hblock₁ hblock₂ hslot hdep₁ hdep₂

end

end EthCLSpecs.Proofs.Heze
