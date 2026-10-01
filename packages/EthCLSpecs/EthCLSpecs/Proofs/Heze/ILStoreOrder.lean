import EthCLLib.Proofs.EngineLaws
import EthCLSpecs.Proofs.Heze.NodeTrace
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction

/-!
# `EthCLSpecs.Proofs.Heze.ILStoreOrder`: the order of the arrivals does not matter

`ilStoreOfArrivals` folds `processInclusionList` over an arrival list
(`OnInclusionList.lean`). The fold result depends on the order of the arrivals. The maps
keep the stored lists in insertion order. The first arrival of a list sets its timeliness.
This module proves that the collected transactions depend only on the timeliness of the
first arrival of each list (`Arrivals.firstTimely`).

`ILStore.Describes` states the fold result in closed form, for an arrival list `arr`:

- A validator is an equivocator at a committee key exactly when `arr` holds two different
  lists from it at that key (`Arrivals.Equivocates`).
- The lists stored at a key are the first lists from each validator at that key
  (`Arrivals.firstFrom`), each at its own root.
- A stored list has the timeliness of its first arrival.

`ilStoreOfArrivals_describes` proves it. The induction runs over the arrivals that remain
after a processed prefix. Each step is one of the three branches of
`processInclusionList`. The one hypothesis is `Arrivals.HashInjective`: two different
arriving lists have different roots. The timeliness map uses the list root alone as its
key, for all committee keys. So a collision lets one list overwrite the timeliness of
another.

Collection skips an equivocator before it reads the timeliness, so the stored list of an
equivocator never reaches the result. `getInclusionListTransactions_mem_iff_collected`
states the members of the result: the transactions of the lists that `Arrivals.Collected`
names. `Collected` reads `arr` only through `firstTimely`, because a list arrived exactly
when its `firstTimely` is `some _`.

`getInclusionListTransactions_order_independent` states the main result. Two arrival lists
with the same `firstTimely` give results with the same members. The order of the result
arrays can differ. The EL answer depends only on the members
(`LawfulInclusionList.satisfied_iff`). So
`recordPayloadInclusionListSatisfaction_order_independent` records the same answer.
`NodeTrace.answer_order_independent` states it for two node traces.

The statements cover every committee key at once. They need no hypothesis on how committee
keys repeat across slots.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (ForkChoiceStoreRun LawfulFcMap LawfulInclusionList pureState)
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Slot InclusionList InclusionListStore
  SignedInclusionList Transaction ValidatorIndex ExecutionPayload ExecutionRequests
  processInclusionList getInclusionListCommittee
  getInclusionListTransactions isInclusionListSatisfied recordPayloadInclusionListSatisfaction)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)

section
variable [Preset]

namespace Arrivals

/-- The list `l` arrives in `arr`. -/
def Arrived (arr : List (SignedInclusionList × UInt64)) (l : InclusionList) : Prop :=
  ∃ a ∈ arr, a.1.message = l

/-- The list `l` comes from the validator `v` at the committee key `k`. -/
def FromAt (k : Root) (v : ValidatorIndex) (l : InclusionList) : Prop :=
  l.inclusionListCommitteeRoot = k ∧ l.validatorIndex = v

/-- `arr` holds two different lists from the validator `v` at the committee key `k`. -/
def Equivocates (arr : List (SignedInclusionList × UInt64)) (k : Root) (v : ValidatorIndex) :
    Prop :=
  ∃ l₁ l₂, Arrived arr l₁ ∧ Arrived arr l₂ ∧ FromAt k v l₁ ∧ FromAt k v l₂ ∧ l₁ ≠ l₂

/-- The first list in `arr` from the validator `v` at the committee key `k`. -/
def firstFrom (arr : List (SignedInclusionList × UInt64)) (k : Root) (v : ValidatorIndex) :
    Option InclusionList :=
  (arr.find? (fun a => a.1.message.inclusionListCommitteeRoot == k &&
    a.1.message.validatorIndex == v)).map (·.1.message)

/-- A list arrives in `arr ++ [a]` when it arrives in `arr` or is the message of `a`. -/
theorem arrived_append (arr : List (SignedInclusionList × UInt64))
    (a : SignedInclusionList × UInt64) (l : InclusionList) :
    Arrived (arr ++ [a]) l ↔ Arrived arr l ∨ a.1.message = l := by
  simp [Arrived, or_and_right, exists_or]

/-- A later arrival keeps every earlier arrival. -/
theorem arrived_of_append {arr : List (SignedInclusionList × UInt64)}
    {a : SignedInclusionList × UInt64} {l : InclusionList} (h : Arrived arr l) :
    Arrived (arr ++ [a]) l :=
  (arrived_append arr a l).mpr (Or.inl h)

/-- More arrivals keep every earlier arrival. -/
theorem arrived_of_append_left {arr rest : List (SignedInclusionList × UInt64)}
    {l : InclusionList} (h : Arrived arr l) : Arrived (arr ++ rest) l := by
  obtain ⟨a, ha, hl⟩ := h
  exact ⟨a, List.mem_append_left _ ha, hl⟩

/-- `firstFrom` returns a list of `arr` from `v` at `k`. -/
theorem firstFrom_some {arr : List (SignedInclusionList × UInt64)} {k : Root}
    {v : ValidatorIndex} {l : InclusionList} (h : firstFrom arr k v = some l) :
    Arrived arr l ∧ FromAt k v l := by
  unfold firstFrom at h
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some ha
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨⟨a, List.mem_of_find?_eq_some ha, rfl⟩, hp⟩

/-- `firstFrom` returns `none` exactly when no list of `arr` comes from `v` at `k`. -/
theorem firstFrom_eq_none {arr : List (SignedInclusionList × UInt64)} {k : Root}
    {v : ValidatorIndex} :
    firstFrom arr k v = none ↔ ∀ l, Arrived arr l → ¬ FromAt k v l := by
  unfold firstFrom Arrived FromAt
  simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro h l ⟨a, ha, rfl⟩ hf
    exact h a ha hf
  · intro h a ha hf
    exact h a.1.message ⟨a, ha, rfl⟩ hf

/-- A validator that does not equivocate sent one list at the key: its first list. -/
theorem eq_of_firstFrom {arr : List (SignedInclusionList × UInt64)} {k : Root}
    {v : ValidatorIndex} {l l' : InclusionList} (h : firstFrom arr k v = some l)
    (hne : ¬ Equivocates arr k v) (ha : Arrived arr l') (hf : FromAt k v l') : l' = l := by
  obtain ⟨hal, hfl⟩ := firstFrom_some h
  exact Classical.byContradiction fun hne' => hne ⟨l', l, ha, hal, hf, hfl, hne'⟩

/-- The first list of a validator that does not equivocate at `k` is any of its lists at
`k`. -/
theorem firstFrom_of_arrived {arr : List (SignedInclusionList × UInt64)} {k : Root}
    {l : InclusionList} (ha : Arrived arr l) (hk : l.inclusionListCommitteeRoot = k)
    (hne : ¬ Equivocates arr k l.validatorIndex) :
    firstFrom arr k l.validatorIndex = some l := by
  cases hf : firstFrom arr k l.validatorIndex with
  | none => exact absurd ⟨hk, rfl⟩ (firstFrom_eq_none.mp hf l ha)
  | some x => rw [eq_of_firstFrom hf hne ha ⟨hk, rfl⟩]

/-- A later arrival keeps `firstFrom` at `k` and `v` in two cases. `arr` already holds a
list from `v` at `k`, or the arrival does not come from `v` at `k`. -/
theorem firstFrom_append_eq {arr : List (SignedInclusionList × UInt64)}
    (a : SignedInclusionList × UInt64) {k : Root} {v : ValidatorIndex}
    (h : FromAt k v a.1.message → ∃ l, Arrived arr l ∧ FromAt k v l) :
    firstFrom (arr ++ [a]) k v = firstFrom arr k v := by
  unfold firstFrom
  rw [List.find?_append]
  cases hs : arr.find? (fun a => a.1.message.inclusionListCommitteeRoot == k &&
      a.1.message.validatorIndex == v) with
  | some x => rfl
  | none =>
    have hnot : ¬ FromAt k v a.1.message := by
      intro hf
      obtain ⟨l, hl, hfl⟩ := h hf
      have hnone : firstFrom arr k v = none := by
        unfold firstFrom
        rw [hs]
        rfl
      exact firstFrom_eq_none.mp hnone l hl hfl
    have hb : (a.1.message.inclusionListCommitteeRoot == k &&
        a.1.message.validatorIndex == v) = false := by
      rw [Bool.eq_false_iff]
      simpa [FromAt] using hnot
    simp [List.find?, hb]

/-- The first list from `v` at `k` is the arrival itself, when `arr` holds no list from `v`
at `k` and the arrival comes from `v` at `k`. -/
theorem firstFrom_append_self {arr : List (SignedInclusionList × UInt64)}
    (a : SignedInclusionList × UInt64) {k : Root} {v : ValidatorIndex}
    (hnone : firstFrom arr k v = none) (hf : FromAt k v a.1.message) :
    firstFrom (arr ++ [a]) k v = some a.1.message := by
  unfold firstFrom at hnone ⊢
  rw [List.find?_append]
  rw [Option.map_eq_none_iff] at hnone
  obtain ⟨hk, hv⟩ := hf
  simp [hnone, List.find?, hk, hv]

/-- A new equivocation at `k` and `v` needs the arrival to come from `v` at `k`, and a
different list from `v` at `k` in `arr`. -/
theorem equivocates_append (arr : List (SignedInclusionList × UInt64))
    (a : SignedInclusionList × UInt64) (k : Root) (v : ValidatorIndex) :
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

section
variable [HasherTag]

/-- Two different lists of `arr` have different roots. -/
def HashInjective (arr : List (SignedInclusionList × UInt64)) : Prop :=
  ∀ l₁ l₂, Arrived arr l₁ → Arrived arr l₂ → htr l₁ = htr l₂ → l₁ = l₂

/-- `HashInjective` holds for every prefix of a list that has it. -/
theorem hashInjective_of_append_left {arr rest : List (SignedInclusionList × UInt64)}
    (h : HashInjective (arr ++ rest)) : HashInjective arr :=
  fun l₁ l₂ h₁ h₂ => h l₁ l₂ (arrived_of_append_left h₁) (arrived_of_append_left h₂)

end

variable [Config]

/-- The timeliness of the first arrival of the list `l` in `arr`, or `none` when `l` does
not arrive. The test is `t < ilDueMs`, as in the fold step
(`ILStore.arrivalStep`). -/
def firstTimely (arr : List (SignedInclusionList × UInt64)) (l : InclusionList) :
    Option Bool :=
  (arr.find? (fun a => a.1.message == l)).map (fun a => decide (a.2 < ilDueMs))

/-- Collection at the committee key `k` keeps the transaction `tx`. Some list `l` of `arr`
meets three conditions:

- `l` is at `k` and carries `tx`.
- The validator of `l` does not equivocate at `k`.
- The first arrival of `l` is timely. -/
def Collected (arr : List (SignedInclusionList × UInt64)) (k : Root) (tx : Transaction) :
    Prop :=
  ∃ l, Arrived arr l ∧ l.inclusionListCommitteeRoot = k ∧
    ¬ Equivocates arr k l.validatorIndex ∧ firstTimely arr l = some true ∧
    tx ∈ l.transactions.toArray

/-- A list arrives exactly when it has a first timeliness. -/
theorem arrived_iff_isSome (arr : List (SignedInclusionList × UInt64)) (l : InclusionList) :
    Arrived arr l ↔ (firstTimely arr l).isSome := by
  simp [firstTimely, Arrived, List.find?_isSome]

/-- A later arrival does not change the first timeliness of a list that already arrived. -/
theorem firstTimely_append_of_arrived {arr : List (SignedInclusionList × UInt64)}
    (a : SignedInclusionList × UInt64) {l : InclusionList} (h : Arrived arr l) :
    firstTimely (arr ++ [a]) l = firstTimely arr l := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((arrived_iff_isSome arr l).mp h)
  unfold firstTimely at hb ⊢
  rw [List.find?_append]
  obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.mp hb
  simp [hx]

/-- The first arrival of a list that did not arrive before is the last arrival. -/
theorem firstTimely_append_self {arr : List (SignedInclusionList × UInt64)}
    (a : SignedInclusionList × UInt64) (h : ¬ Arrived arr a.1.message) :
    firstTimely (arr ++ [a]) a.1.message = some (decide (a.2 < ilDueMs)) := by
  have hnone : firstTimely arr a.1.message = none := by
    cases hs : firstTimely arr a.1.message with
    | none => rfl
    | some _ => exact absurd ((arrived_iff_isSome _ _).mpr (by simp [hs])) h
  unfold firstTimely at hnone ⊢
  rw [List.find?_append]
  rw [Option.map_eq_none_iff] at hnone
  simp [hnone]

section Congr
variable {arr₁ arr₂ : List (SignedInclusionList × UInt64)}
  (h : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
include h

/-- Two arrival lists with the same `firstTimely` have the same arrived lists. -/
theorem arrived_congr (l : InclusionList) : Arrived arr₁ l ↔ Arrived arr₂ l := by
  rw [arrived_iff_isSome, arrived_iff_isSome, h]

/-- Two arrival lists with the same `firstTimely` have the same equivocators. -/
theorem equivocates_congr (k : Root) (v : ValidatorIndex) :
    Equivocates arr₁ k v ↔ Equivocates arr₂ k v := by
  simp only [Equivocates, arrived_congr h]

/-- `HashInjective` reads only the arrived lists, so it holds for both arrival lists or for
neither. -/
theorem hashInjective_congr [HasherTag] : HashInjective arr₁ ↔ HashInjective arr₂ := by
  simp only [HashInjective, arrived_congr h]

/-- `Collected` reads the arrival list only through `firstTimely`. -/
theorem collected_congr (k : Root) (tx : Transaction) :
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

variable [HasherTag] [Config] {map : MapKind} [FcMap map]

namespace ILStore

/-- The closed form of the IL store after the arrival list `arr`: the equivocators, the
stored lists, and their timeliness, each stated through `arr` alone. -/
structure Describes (arr : List (SignedInclusionList × UInt64))
    (s : InclusionListStore map) : Prop where
  /-- The equivocators at `k` are the validators with two different lists at `k`. -/
  equiv : ∀ k v, (FcMap.lookupD s.equivocators k).contains v = true ↔ Equivocates arr k v
  /-- The lists at `k` are the first lists of each validator at `k`, at their roots. -/
  stored : ∀ k r l, storedAt s k r = some l ↔
    firstFrom arr k l.validatorIndex = some l ∧ r = htr l
  /-- A stored list has the timeliness of its first arrival. -/
  timely : ∀ k r l, storedAt s k r = some l →
    FcMap.lookup s.inclusionListTimeliness r = firstTimely arr l

/-- A step whose store keeps the stored lists and the timeliness. The arrival must not
start a new first list, and the equivocators must match. Branch (A) and branch (B) of
`processInclusionList` are such steps. -/
theorem describes_keep {arr : List (SignedInclusionList × UInt64)}
    {a : SignedInclusionList × UInt64} {s s' : InclusionListStore map}
    (hlists : s'.inclusionLists = s.inclusionLists)
    (htim : s'.inclusionListTimeliness = s.inclusionListTimeliness)
    (hfirst : ∀ k v, FromAt k v a.1.message → ∃ l, Arrived arr l ∧ FromAt k v l)
    (hequiv : ∀ k v,
      (FcMap.lookupD s'.equivocators k).contains v = true ↔ Equivocates (arr ++ [a]) k v)
    (h : Describes arr s) : Describes (arr ++ [a]) s' := by
  have hst : ∀ k r, storedAt s' k r = storedAt s k r := fun k r => by
    simp only [storedAt, listsAt, hlists]
  refine ⟨hequiv, fun k r l => ?_, fun k r l hl => ?_⟩
  · rw [hst, firstFrom_append_eq a (hfirst k l.validatorIndex)]
    exact h.stored k r l
  · rw [hst] at hl
    rw [htim, h.timely k r l hl, firstTimely_append_of_arrived a
      (firstFrom_some ((h.stored k r l).mp hl).1).1]

variable [LawfulFcMap map Root]

/-- The empty IL store describes the empty arrival list. -/
theorem describes_nil : Describes [] (InclusionListStore.empty : InclusionListStore map) := by
  have hnil : ∀ k r, storedAt (InclusionListStore.empty : InclusionListStore map) k r = none :=
    fun k r => by
      simp [storedAt, listsAt, InclusionListStore.empty, LawfulFcMap.lookup_empty]
  refine ⟨fun k v => ?_, fun k r l => ?_, fun k r l h => ?_⟩
  · rw [(before_empty v k).2]
    simp [Equivocates, Arrived]
  · rw [hnil]
    simp [firstFrom]
  · rw [hnil] at h
    cases h

/-- Branch (C) of `processInclusionList`: the first list from its validator at its key. -/
theorem describes_stored {arr : List (SignedInclusionList × UInt64)}
    {a : SignedInclusionList × UInt64} {s : InclusionListStore map}
    (hinj : HashInjective (arr ++ [a]))
    (hnone : firstFrom arr a.1.message.inclusionListCommitteeRoot
      a.1.message.validatorIndex = none)
    (h : Describes arr s) :
    Describes (arr ++ [a])
      (withStored s a.1.message (decide (a.2 < ilDueMs))) := by
  -- `m` is the arriving list. It is new: no list of `arr` comes from its validator at its key.
  have hnew : ¬ Arrived arr a.1.message := fun ha =>
    firstFrom_eq_none.mp hnone _ ha ⟨rfl, rfl⟩
  have hm : Arrived (arr ++ [a]) a.1.message := (arrived_append arr a _).mpr (Or.inr rfl)
  have hstored : ∀ k r l, storedAt (withStored s a.1.message
      (decide (a.2 < ilDueMs))) k r = some l ↔
      firstFrom (arr ++ [a]) k l.validatorIndex = some l ∧ r = htr l := by
    intro k r l
    rw [storedAt_withStored]
    by_cases hf : FromAt k l.validatorIndex a.1.message
    · -- The arrival comes from the validator of `l` at `k`: it is the new first list.
      obtain ⟨hk, hv⟩ := hf
      subst hk
      rw [← hv, firstFrom_append_self a hnone ⟨rfl, rfl⟩]
      constructor
      · intro hl
        split at hl
        · cases hl
          exact ⟨rfl, ‹_ ∧ _›.2⟩
        · have := ((h.stored _ r l).mp hl).1
          rw [← hv, hnone] at this
          cases this
      · rintro ⟨hml, rfl⟩
        cases hml
        simp
    · rw [firstFrom_append_eq a (fun hf' => absurd hf' hf)]
      constructor
      · intro hl
        split at hl
        · rename_i hkr
          cases hl
          exact absurd ⟨hkr.1.symm, rfl⟩ hf
        · exact (h.stored k r l).mp hl
      · rintro ⟨hff, hr⟩
        split
        · -- A stored list at the root of the arrival is the arrival itself, by `hinj`.
          rename_i hkr
          have hl := (firstFrom_some hff).1
          have hlm := hinj l a.1.message (arrived_of_append hl) hm (hr.symm.trans hkr.2)
          subst hlm
          exact absurd ⟨hkr.1.symm, rfl⟩ hf
        · exact (h.stored k r l).mpr ⟨hff, hr⟩
  refine ⟨fun k v => ?_, hstored, fun k r l hl => ?_⟩
  · -- Branch (C) keeps the equivocators, and the arrival starts no equivocation.
    change (FcMap.lookupD s.equivocators k).contains v = true ↔ _
    rw [h.equiv, equivocates_append]
    constructor
    · exact Or.inl
    · rintro (he | ⟨hf, l, hl, hfl, -⟩)
      · exact he
      · obtain ⟨hk, hv⟩ := hf
        subst hk hv
        exact absurd hfl (firstFrom_eq_none.mp hnone l hl)
  · obtain ⟨hff, hr⟩ := (hstored k r l).mp hl
    simp only [withStored]
    by_cases hrm : htr a.1.message = r
    · -- The root of the arrival: `l` is the arrival, with the timeliness just written.
      rw [← hrm, LawfulFcMap.lookup_insert_self]
      have hlm := hinj l a.1.message (firstFrom_some hff).1 hm (hr.symm.trans hrm.symm)
      subst hlm
      rw [firstTimely_append_self a hnew]
    · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hrm]
      rw [storedAt_withStored, if_neg (fun hkr => hrm hkr.2.symm)] at hl
      rw [h.timely k r l hl, firstTimely_append_of_arrived a
        (firstFrom_some ((h.stored k r l).mp hl).1).1]

/-- One fold step keeps `Describes`, under `HashInjective` on the longer list. -/
theorem describes_step {arr : List (SignedInclusionList × UInt64)}
    (a : SignedInclusionList × UInt64) {s : InclusionListStore map}
    (hinj : HashInjective (arr ++ [a])) (h : Describes arr s) :
    Describes (arr ++ [a]) (arrivalStep s a) := by
  obtain ⟨signed, t⟩ := a
  change Describes _ (processInclusionList s signed.message (decide (t < ilDueMs)))
  -- `m` is the arriving list.
  generalize hm : signed.message = m
  have hmsg : (signed, t).1.message = m := hm
  by_cases hE : Equivocates arr m.inclusionListCommitteeRoot m.validatorIndex
  · -- Branch (A): a known equivocator. The store does not change.
    have hA : processInclusionList s m (decide (t < ilDueMs)) = s := by
      simp only [processInclusionList, (h.equiv _ _).mpr hE, if_true]
    rw [hA]
    refine describes_keep rfl rfl (fun k v hf => ?_) (fun k v => ?_) h
    · obtain ⟨hk, hv⟩ := hf
      obtain ⟨l, -, hl, -, hfl, -⟩ := hE
      rw [hmsg] at hk hv
      subst hk hv
      exact ⟨l, hl, hfl⟩
    · rw [h.equiv, equivocates_append, hmsg]
      constructor
      · exact Or.inl
      · rintro (he | ⟨⟨hk, hv⟩, -⟩)
        · exact he
        · subst hk hv
          exact hE
  · have hcont : (FcMap.lookupD s.equivocators m.inclusionListCommitteeRoot).contains
        m.validatorIndex = false := by
      cases hc : (FcMap.lookupD s.equivocators m.inclusionListCommitteeRoot).contains
          m.validatorIndex
      · rfl
      · exact absurd ((h.equiv _ _).mp hc) hE
    cases hff : firstFrom arr m.inclusionListCommitteeRoot m.validatorIndex with
    | some l0 =>
      -- Branch (B): the validator has a stored list, its first list `l0`.
      obtain ⟨hl0, hkl, hvl⟩ := firstFrom_some hff
      have hfind : (FcMap.values (listsAt s m.inclusionListCommitteeRoot)).find?
          (fun il => il.validatorIndex == m.validatorIndex) = some l0 := by
        cases hfd : (FcMap.values (listsAt s m.inclusionListCommitteeRoot)).find?
            (fun il => il.validatorIndex == m.validatorIndex) with
        | none =>
          have hst := (h.stored _ (htr l0) l0).mpr ⟨by rw [hvl]; exact hff, rfl⟩
          exfalso
          rw [List.find?_eq_none] at hfd
          exact hfd l0 ((EthCLLib.Proofs.FcMap.mem_values _ l0).mpr ⟨_, hst⟩) (by simp [hvl])
        | some x =>
          obtain ⟨⟨r, hr⟩, hxv⟩ := find?_values_stored s _ _ x hfd
          have hx := ((h.stored _ r x).mp hr).1
          rw [hxv, hff] at hx
          cases hx
          rfl
      unfold listsAt at hfind
      have hfirst : ∀ k v, FromAt k v (signed, t).1.message →
          ∃ l, Arrived arr l ∧ FromAt k v l := by
        rintro k v ⟨hk, hv⟩
        rw [hmsg] at hk hv
        subst hk hv
        exact ⟨l0, hl0, hkl, hvl⟩
      by_cases heq : l0 = m
      · -- The same list again: the store does not change.
        subst heq
        have hB : processInclusionList s l0 (decide (t < ilDueMs)) = s := by
          simp only [processInclusionList, hcont, hfind, beq_self_eq_true,
            Bool.false_eq_true, if_false, if_true]
        rw [hB]
        refine describes_keep rfl rfl hfirst (fun k v => ?_) h
        rw [h.equiv, equivocates_append, hmsg]
        constructor
        · exact Or.inl
        · rintro (he | ⟨⟨hk, hv⟩, l, hl, hfl, hne⟩)
          · exact he
          · subst hk hv
            exact absurd (eq_of_firstFrom hff hE hl hfl) hne
      · -- A different list: the validator joins the equivocators at the key of `m`.
        have hB : processInclusionList s m (decide (t < ilDueMs))
            = withEquivocator s m := by
          have hbeq : (l0 == m) = false := by simpa using heq
          simp only [processInclusionList, hcont, hfind, hbeq, Bool.false_eq_true, if_false]
          rfl
        rw [hB]
        refine describes_keep (s := s) rfl rfl hfirst (fun k v => ?_) h
        rw [equivocators_withEquivocator, Bool.or_eq_true, h.equiv, equivocates_append, hmsg]
        simp only [Bool.and_eq_true, beq_iff_eq]
        constructor
        · rintro (he | ⟨rfl, rfl⟩)
          · exact Or.inl he
          · exact Or.inr ⟨⟨rfl, rfl⟩, l0, hl0, ⟨hkl, hvl⟩, heq⟩
        · rintro (he | ⟨⟨hk, hv⟩, -⟩)
          · exact Or.inl he
          · exact Or.inr ⟨hk.symm, hv.symm⟩
    | none =>
      -- Branch (C): no stored list from the validator at the key of `m`.
      have hfind : (FcMap.values (listsAt s m.inclusionListCommitteeRoot)).find?
          (fun il => il.validatorIndex == m.validatorIndex) = none :=
        find?_values_eq_none s _ _ (fun r l hl hlv => by
          have hx := ((h.stored _ r l).mp hl).1
          rw [hlv, hff] at hx
          cases hx)
      unfold listsAt at hfind
      have hC : processInclusionList s m (decide (t < ilDueMs))
          = withStored s m (decide (t < ilDueMs)) := by
        simp only [processInclusionList, hcont, hfind, Bool.false_eq_true, if_false]
        rfl
      rw [hC]
      subst hm
      exact describes_stored hinj hff h

end ILStore

variable [LawfulFcMap map Root]

/-- The IL store after the arrival list `arr` has the closed form `ILStore.Describes`,
when two different lists of `arr` have different roots. -/
theorem ilStoreOfArrivals_describes (arr : List (SignedInclusionList × UInt64))
    (hinj : HashInjective arr) :
    ILStore.Describes arr (ilStoreOfArrivals (map := map) arr) := by
  -- Induction over the rest of the list, with the processed prefix `pre` and its store.
  suffices h : ∀ (rest pre : List (SignedInclusionList × UInt64)) (s : InclusionListStore map),
      HashInjective (pre ++ rest) → ILStore.Describes pre s →
      ILStore.Describes (pre ++ rest) (rest.foldl ILStore.arrivalStep s) from
    h arr [] _ hinj ILStore.describes_nil
  intro rest
  induction rest with
  | nil => intro pre s _ hD; simpa using hD
  | cons a rest ih =>
    intro pre s hinj hD
    have hassoc : pre ++ a :: rest = (pre ++ [a]) ++ rest := by simp
    rw [hassoc] at hinj ⊢
    exact ih _ _ hinj
      (ILStore.describes_step a (hashInjective_of_append_left hinj) hD)

/-- The inclusion-list transactions for `slot`, after the arrival list `arr`. When the
committee run returns `committee`, the collection succeeds. A transaction is in the result
exactly when `Collected arr (htr committee)` holds for it. -/
theorem getInclusionListTransactions_mem_iff_collected {σ : Type}
    (arr : List (SignedInclusionList × UInt64)) (hinj : HashInjective arr)
    (state : BeaconState) (slot : Slot) (s : σ)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (hcommittee : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun σ)
        (pureState state) slot).run s = .ok (committee, s)) :
    ∃ ilTxs, (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun σ)
        (ilStoreOfArrivals (map := map) arr) (pureState state) slot (onlyTimely := true)).run s
          = .ok (ilTxs, s) ∧
      ∀ tx, tx ∈ ilTxs ↔ Collected arr (htr committee) tx := by
  have hD := ilStoreOfArrivals_describes (map := map) arr hinj
  obtain ⟨ilTxs, hrun, hmem⟩ := getInclusionListTransactions_ok_mem_iff
    (ilStoreOfArrivals (map := map) arr) state slot s committee hcommittee
    (total_arrivals arr (htr committee))
  refine ⟨ilTxs, hrun, fun tx => (hmem tx).trans ?_⟩
  constructor
  · rintro ⟨r, l, hst, hne, ht, htx⟩
    obtain ⟨hff, -⟩ := (hD.stored _ r l).mp hst
    obtain ⟨hl, hk, -⟩ := firstFrom_some hff
    refine ⟨l, hl, hk, fun he => ?_, ?_, htx⟩
    · have := (hD.equiv _ _).mpr he
      simp_all
    · rw [← hD.timely _ r l hst]
      exact ht
  · rintro ⟨l, hl, hk, hne, ht, htx⟩
    have hst := (hD.stored _ (htr l) l).mpr ⟨firstFrom_of_arrived hl hk hne, rfl⟩
    refine ⟨htr l, l, hst, ?_, (hD.timely _ _ l hst).trans ht, htx⟩
    cases hc : (FcMap.lookupD (ilStoreOfArrivals (map := map) arr).equivocators
        (htr committee)).contains l.validatorIndex
    · rfl
    · exact absurd ((hD.equiv _ _).mp hc) hne

/-- Order independence. Take two arrival lists with the same first timeliness for every
list, and with `HashInjective` on the first. The second then has `HashInjective` too. When
the committee run returns `committee`, both collections succeed, and their results have the
same members. -/
theorem getInclusionListTransactions_order_independent {σ : Type}
    (arr₁ arr₂ : List (SignedInclusionList × UInt64)) (hinj : HashInjective arr₁)
    (htimely : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
    (state : BeaconState) (slot : Slot) (s₁ s₂ : σ)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (hcommittee : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun σ)
        (pureState state) slot).run s₁ = .ok (committee, s₁)) :
    ∃ ilTxs₁ ilTxs₂,
      (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun σ)
        (ilStoreOfArrivals (map := map) arr₁) (pureState state) slot (onlyTimely := true)).run s₁
          = .ok (ilTxs₁, s₁) ∧
      (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun σ)
        (ilStoreOfArrivals (map := map) arr₂) (pureState state) slot (onlyTimely := true)).run s₂
          = .ok (ilTxs₂, s₂) ∧
      ∀ tx, tx ∈ ilTxs₁ ↔ tx ∈ ilTxs₂ := by
  obtain ⟨ilTxs₁, hrun₁, hmem₁⟩ := getInclusionListTransactions_mem_iff_collected (map := map)
    arr₁ hinj state slot s₁ committee hcommittee
  obtain ⟨ilTxs₂, hrun₂, hmem₂⟩ := getInclusionListTransactions_mem_iff_collected (map := map)
    arr₂ ((hashInjective_congr htimely).mp hinj) state slot s₂ committee
    (getInclusionListCommittee_run_ok_transfer state slot s₁ s₂ committee hcommittee)
  exact ⟨ilTxs₁, ilTxs₂, hrun₁, hrun₂, fun tx =>
    (hmem₁ tx).trans ((collected_congr htimely _ tx).trans (hmem₂ tx).symm)⟩

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]

/-- The record handler writes the same answer for two stores under `LawfulInclusionList`.
The IL stores of the two stores come from arrival lists with the same first timeliness.
`hcommittee` names the committee of the previous slot at the runner of the first run. -/
theorem recordPayloadInclusionListSatisfaction_order_independent
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    (store₁ store₂ runner₁ runner₂ : Store map)
    (arr₁ arr₂ : List (SignedInclusionList × UInt64))
    (hils₁ : store₁.inclusionListStore = ilStoreOfArrivals arr₁)
    (hils₂ : store₂.inclusionListStore = ilStoreOfArrivals arr₂)
    (hinj : HashInjective arr₁) (htimely : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
    (state : BeaconState) (root : Root) (payload : ExecutionPayload)
    (hslot : state.slot ≠ 0)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (hcommittee : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun (Store map))
        (pureState state) (state.slot - 1)).run runner₁ = .ok (committee, runner₁)) :
    ∃ answer : Bool,
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₁ (pureState state) root
          payload).run runner₁
        = .ok ({ store₁ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₁.payloadInclusionListSatisfaction root answer }, runner₁) ∧
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₂ (pureState state) root
          payload).run runner₂
        = .ok ({ store₂ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₂.payloadInclusionListSatisfaction root answer }, runner₂) := by
  obtain ⟨ilTxs₁, ilTxs₂, hrun₁, hrun₂, hmem⟩ :=
    getInclusionListTransactions_order_independent (map := map) arr₁ arr₂ hinj htimely state
      (state.slot - 1) runner₁ runner₂ committee hcommittee
  rw [← hils₁] at hrun₁
  rw [← hils₂] at hrun₂
  refine ⟨isInclusionListSatisfied payload ilTxs₁,
    recordPayloadInclusionListSatisfaction_run_eq store₁ runner₁ runner₁ state root payload
      ilTxs₁ hslot hrun₁, ?_⟩
  rw [isInclusionListSatisfied_congr_mem hel payload hmem]
  exact recordPayloadInclusionListSatisfaction_run_eq store₂ runner₂ runner₂ state root payload
    ilTxs₂ hslot hrun₂

variable [CryptoBackend] [DataAvailability]

/-- Two node traces, each from a seed with the empty IL store. Their IL arrivals have the
same first timeliness for every list. Two different lists of the first trace have
different roots. Then the record handler writes the same answer at both final stores. -/
theorem NodeTrace.answer_order_independent
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    {s0₁ s0₂ store₁ store₂ : Store map} {events₁ events₂ : List TraceEvent}
    {arr₁ arr₂ : List (SignedInclusionList × UInt64)}
    (h₁ : NodeTrace s0₁ events₁ arr₁ store₁)
    (hseed₁ : s0₁.inclusionListStore = InclusionListStore.empty)
    (h₂ : NodeTrace s0₂ events₂ arr₂ store₂)
    (hseed₂ : s0₂.inclusionListStore = InclusionListStore.empty)
    (hinj : HashInjective arr₁) (htimely : ∀ l, firstTimely arr₁ l = firstTimely arr₂ l)
    (runner₁ runner₂ : Store map) (state : BeaconState) (root : Root)
    (payload : ExecutionPayload) (hslot : state.slot ≠ 0)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize)
    (hcommittee : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun (Store map))
        (pureState state) (state.slot - 1)).run runner₁ = .ok (committee, runner₁)) :
    ∃ answer : Bool,
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₁ (pureState state) root
          payload).run runner₁
        = .ok ({ store₁ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₁.payloadInclusionListSatisfaction root answer }, runner₁) ∧
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map)) store₂ (pureState state) root
          payload).run runner₂
        = .ok ({ store₂ with
            payloadInclusionListSatisfaction :=
              FcMap.insert store₂.payloadInclusionListSatisfaction root answer }, runner₂) :=
  recordPayloadInclusionListSatisfaction_order_independent hel store₁ store₂ runner₁ runner₂
    arr₁ arr₂ (h₁.ilStore hseed₁) (h₂.ilStore hseed₂) hinj htimely state root payload hslot
    committee hcommittee

end

end EthCLSpecs.Proofs.Heze
