import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions

/-!
# `EthCLSpecs.Proofs.Heze.OnInclusionList`: the honest list in the IL store

`onInclusionList` reads the time into the slot and compares it with
`getInclusionListDueMs`. Then it passes the list to `processInclusionList`.
`onInclusionList_run_eq` states this run.

The arrival model is a list of `(SignedInclusionList, t)` pairs. `t` is the time into the
current slot at arrival, as in pyspec: the slot of the list does not enter the timeliness,
and pyspec leaves the slot check to the p2p layer. `ilStoreOfArrivals` folds
`processInclusionList` over the list, from the empty IL store that `getForkchoiceStore`
seeds. `onInclusionList_run_eq` shows that each successful run of the handler is one step
of this fold. In the model, only `onInclusionList` writes the IL store. So the model
assumes two things: the store started from the seed, and every arrival went through a
successful `onInclusionList` run, in list order.

`honestStored_of_arrivals` proves the main fact. Take an honest list `il`, and suppose
`ArrivalHypotheses il before after`. Then, after the arrivals, the IL store holds `il`
under its committee key with the timeliness of its first arrival. The validator of `il`
is not an equivocator for that key. The validator can send lists for other committee
keys, and `arrivalHypotheses_two_keys` shows that the hypotheses hold for such a
history.

The hypotheses are per committee key. The store key is the list's own
`inclusionListCommitteeRoot`, which the sender sets and `on_inclusion_list` does not
check. For an honest list it is the `hash_tree_root` of the committee. That root carries
no slot, and the store keeps every key. So two slots with the same committee share a key.
On a small validator set, a key can repeat across epochs. A second list from an honest
validator under a repeated key then fails the hypotheses, and pyspec, like the model,
marks the validator as an equivocator.

The first arrival sets the timeliness. A later arrival of the same list goes to branch (B)
of `processInclusionList`, which changes nothing. Thus the store keeps an honest list that
first arrives late as late, even when a copy arrives on time later. This is the spec
behavior.

`ILStore.Total` is a second invariant of the fold: every stored list has a timeliness
entry. The collection of the inclusion-list transactions throws without it
(`GetInclusionListTransactions.lean`). `total_arrivals` proves it for every arrival list.
The fold invariants and their step lemmas live in the namespace `ILStore`.

The proofs use two `==` facts. `Transaction` is a subtype of `Array UInt8`, so its `==`
comes from `DecidableEq` and is lawful. `InclusionList` has a derived structural `BEq`,
and the `ReflBEq` instance below makes it reflexive (`beq_self_eq_true`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLLib.Proofs
open EthCLSpecs.Heze (Preset Config Store Root InclusionList InclusionListStore
  SignedInclusionList Transaction ValidatorIndex onInclusionList processInclusionList
  timeIntoSlotMs getInclusionListDueMs)

/-- `==` on `Transaction` is lawful. The instance comes from `DecidableEq` on the subtype. -/
example : LawfulBEq Transaction := inferInstance

-- Core's `ReflBEq` handler proves that the derived `BEq` is reflexive, field by field.
deriving instance ReflBEq for InclusionList

/-- Take a store where the time into the slot is `t`. Then `onInclusionList` replaces the
IL store with the result of `processInclusionList` on the list. The timeliness argument is
`t < getInclusionListDueMs`. -/
theorem onInclusionList_run_eq {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
    (store : Store map) (signed : SignedInclusionList) (t : UInt64)
    (hclock : (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) store).run
      store = .ok (t, store)) :
    (onInclusionList (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        signed).run store
      = .ok ((), { store with
          inclusionListStore := processInclusionList store.inclusionListStore signed.message
            (decide (t < getInclusionListDueMs)) }) := by
  simp [onInclusionList, StateT.run_bind, hclock]
  rfl

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The store after branch (B) with a different list: the validator of `il` joins the
equivocators at the key of `il`. -/
def withEquivocator (s : InclusionListStore map) (il : InclusionList) :
    InclusionListStore map :=
  { s with
      equivocators :=
        FcMap.insert s.equivocators il.inclusionListCommitteeRoot
          ((FcMap.lookupD s.equivocators il.inclusionListCommitteeRoot).push
            il.validatorIndex) }

/-- The store after branch (C): `il` at its root under its key, with timeliness `b`. -/
def withStored (s : InclusionListStore map) (il : InclusionList) (b : Bool) :
    InclusionListStore map :=
  { s with
      inclusionLists :=
        FcMap.insert s.inclusionLists il.inclusionListCommitteeRoot
          (FcMap.insert ((FcMap.lookup s.inclusionLists il.inclusionListCommitteeRoot).getD
            FcMap.empty) (htr il) il)
      inclusionListTimeliness := FcMap.insert s.inclusionListTimeliness (htr il) b }

/-- `processInclusionList` has three results. It leaves the store unchanged (branch (A),
and branch (B) with an equal list). It adds the arriving validator to the equivocators at
the arriving key (branch (B) with a different list). It stores the arriving list at its
root, with the given timeliness (branch (C)). -/
theorem processInclusionList_cases (s : InclusionListStore map) (il : InclusionList)
    (b : Bool) :
    processInclusionList s il b = s ∨
    processInclusionList s il b = withEquivocator s il ∨
    processInclusionList s il b = withStored s il b := by
  simp only [processInclusionList]
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- The assumptions on the arrival list `before ++ (signed, t) :: after` for an honest
list `il`:

- `first`: no list in `before` comes from the validator of `il` for the committee key of
  `il`, so `(signed, t)` is the first arrival of a list from that validator for that key;
- `sig`: one list per key: each list in `after` from the validator of `il`, for the
  committee key of `il`, is `il`;
- `hash`: no hash collision: each list in `after` other than `il`, whatever its key, has
  a different root. -/
structure ArrivalHypotheses (il : InclusionList)
    (before after : List (SignedInclusionList × UInt64)) : Prop where
  first : ∀ a ∈ before, a.1.message.inclusionListCommitteeRoot = il.inclusionListCommitteeRoot →
    a.1.message.validatorIndex ≠ il.validatorIndex
  sig : ∀ a ∈ after, a.1.message.inclusionListCommitteeRoot = il.inclusionListCommitteeRoot →
    a.1.message.validatorIndex = il.validatorIndex → a.1.message = il
  hash : ∀ a ∈ after, a.1.message ≠ il → htr a.1.message ≠ htr il

namespace ILStore

/-- Every stored list has a timeliness entry: `TimelinessTotal` holds at every committee
key. -/
def Total (s : InclusionListStore map) : Prop :=
  ∀ k, TimelinessTotal (listsAt s k) s.inclusionListTimeliness

/-- At the committee key `k`, no stored list comes from `v`, and `v` is not an
equivocator. Other keys are free: the validator can hold lists for other committee
keys. -/
def Before (v : ValidatorIndex) (k : Root) (s : InclusionListStore map) : Prop :=
  (∀ r l, storedAt s k r = some l → l.validatorIndex ≠ v) ∧
  (FcMap.lookupD s.equivocators k).contains v = false

/-- `il` is stored at its key and root with timeliness `b`. At that key, each stored
list from the validator of `il` is `il`, and the validator is not an equivocator. -/
def After (il : InclusionList) (b : Bool) (s : InclusionListStore map) : Prop :=
  storedAt s il.inclusionListCommitteeRoot (htr il) = some il ∧
  FcMap.lookup s.inclusionListTimeliness (htr il) = some b ∧
  (∀ r l, storedAt s il.inclusionListCommitteeRoot r = some l →
    l.validatorIndex = il.validatorIndex → l = il) ∧
  (FcMap.lookupD s.equivocators il.inclusionListCommitteeRoot).contains il.validatorIndex
    = false

/-- The fold step of the arrival model. -/
def arrivalStep [Config] (s : InclusionListStore map) (a : SignedInclusionList × UInt64) :
    InclusionListStore map :=
  processInclusionList s a.1.message (decide (a.2 < getInclusionListDueMs))

end ILStore

/-- The IL store after the arrival list. Each arrival is a signed list and the time into
the slot at its arrival. The fold starts from the empty IL store, the seed of
`getForkchoiceStore`. -/
def ilStoreOfArrivals [Config] (arrivals : List (SignedInclusionList × UInt64)) :
    InclusionListStore map :=
  arrivals.foldl ILStore.arrivalStep InclusionListStore.empty

variable [LawfulFcMap map Root]

namespace ILStore

/-- A stored list after branch (C). The new list is at its root under its key. Every
other lookup returns the old entry. -/
theorem storedAt_withStored (s : InclusionListStore map) (il : InclusionList) (b : Bool)
    (k r : Root) :
    storedAt (withStored s il b) k r
      = if k = il.inclusionListCommitteeRoot ∧ r = htr il then some il
        else storedAt s k r := by
  unfold storedAt listsAt withStored
  by_cases hk : il.inclusionListCommitteeRoot = k
  · subst hk
    rw [LawfulFcMap.lookup_insert_self]
    by_cases hr : htr il = r
    · subst hr
      simp
    · simp [LawfulFcMap.lookup_insert_ne _ _ _ _ hr, Ne.symm hr]
  · simp [LawfulFcMap.lookup_insert_ne _ _ _ _ hk, Ne.symm hk]

/-- A list from the validator `v` stored at the key `k` after branch (C) with the list
`a` was stored before, when `a` does not come from `v` at `k`. -/
theorem storedAt_withStored_of_ne (s : InclusionListStore map) (a : InclusionList)
    (b : Bool) (k r : Root) (v : ValidatorIndex) (l : InclusionList)
    (hv : a.inclusionListCommitteeRoot = k → a.validatorIndex ≠ v)
    (hl : storedAt (withStored s a b) k r = some l) (hlv : l.validatorIndex = v) :
    storedAt s k r = some l := by
  rw [storedAt_withStored] at hl
  split at hl
  · rename_i hkr
    cases hl
    exact absurd hlv (hv hkr.1.symm)
  · exact hl

/-- An equivocator entry after branch (B). The validator of `il` joins the entry at the
key of `il`. Every other entry stays. -/
theorem equivocators_withEquivocator (s : InclusionListStore map) (il : InclusionList)
    (k : Root) (v : ValidatorIndex) :
    (FcMap.lookupD (withEquivocator s il).equivocators k).contains v
      = ((FcMap.lookupD s.equivocators k).contains v ||
          (k == il.inclusionListCommitteeRoot && v == il.validatorIndex)) := by
  unfold withEquivocator
  simp only [FcMap.lookupD]
  by_cases hk : il.inclusionListCommitteeRoot = k
  · subst hk
    rw [LawfulFcMap.lookup_insert_self]
    cases h : (v == il.validatorIndex) <;> simp_all
  · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk]
    simp [Ne.symm hk]

/-- Branch (B) with the list `a` keeps `v` out of the equivocators at `k` when `a` does
not come from `v` at `k`. -/
theorem equivocators_withEquivocator_of_ne (s : InclusionListStore map) (a : InclusionList)
    (k : Root) (v : ValidatorIndex)
    (hv : a.inclusionListCommitteeRoot = k → a.validatorIndex ≠ v)
    (h : (FcMap.lookupD s.equivocators k).contains v = false) :
    (FcMap.lookupD (withEquivocator s a).equivocators k).contains v = false := by
  rw [equivocators_withEquivocator, h]
  by_cases hk : a.inclusionListCommitteeRoot = k
  · simp [hk, Ne.symm (hv hk)]
  · simp [Ne.symm hk]

/-- `find?` over the stored values at the key `k` finds no list from the validator `v`
when no list stored at `k` comes from `v`. -/
theorem find?_values_eq_none (s : InclusionListStore map) (k : Root) (v : ValidatorIndex)
    (h : ∀ r l, storedAt s k r = some l → l.validatorIndex ≠ v) :
    (FcMap.values (listsAt s k)).find?
      (fun l => l.validatorIndex == v) = none := by
  rw [List.find?_eq_none]
  intro l hl
  obtain ⟨r, hr⟩ := (FcMap.mem_values _ l).mp hl
  simpa using h r l hr

/-- `find?` over the stored values at the key `k` returns a list from the validator `v`
that is stored at `k`. -/
theorem find?_values_stored (s : InclusionListStore map) (k : Root) (v : ValidatorIndex)
    (l : InclusionList)
    (h : (FcMap.values (listsAt s k)).find?
      (fun l => l.validatorIndex == v) = some l) :
    (∃ r, storedAt s k r = some l) ∧ l.validatorIndex = v := by
  have hmem := List.mem_of_find?_eq_some h
  have hv := List.find?_some h
  exact ⟨(FcMap.mem_values _ l).mp hmem, by simpa using hv⟩

/-- The empty IL store has no stored list, so `Total` holds for it. -/
theorem total_empty : Total (InclusionListStore.empty : InclusionListStore map) := by
  intro k r l h
  change storedAt _ k r = some l at h
  simp [storedAt, listsAt, InclusionListStore.empty, LawfulFcMap.lookup_empty] at h

/-- `processInclusionList` keeps `Total`. Branch (C) stores the list and writes its
timeliness at the same root. The other branches do not change the stored lists. -/
theorem total_step (s : InclusionListStore map) (il : InclusionList) (b : Bool)
    (h : Total s) : Total (processInclusionList s il b) := by
  rcases processInclusionList_cases s il b with he | he | he <;> rw [he]
  · exact h
  · exact h
  · intro k r l hl
    change storedAt _ k r = some l at hl
    rw [storedAt_withStored] at hl
    by_cases hr : r = htr il
    · subst hr
      simp [withStored]
    · have hl' : storedAt s k r = some l := by simpa [hr] using hl
      simpa [withStored, LawfulFcMap.lookup_insert_ne _ _ _ _ (Ne.symm hr)] using h k r l hl'

/-- The empty IL store satisfies `Before v k` for every validator and key. -/
theorem before_empty (v : ValidatorIndex) (k : Root) :
    Before v k (InclusionListStore.empty : InclusionListStore map) := by
  refine ⟨fun r l h => ?_, ?_⟩
  · simp [storedAt, listsAt, InclusionListStore.empty, LawfulFcMap.lookup_empty] at h
  · simp [FcMap.lookupD, InclusionListStore.empty, LawfulFcMap.lookup_empty,
      show (default : Array ValidatorIndex) = #[] from rfl]

/-- A list keeps `Before v k` unless it comes from `v` at the key `k`. -/
theorem before_step (v : ValidatorIndex) (k : Root) (s : InclusionListStore map)
    (il : InclusionList) (b : Bool)
    (hv : il.inclusionListCommitteeRoot = k → il.validatorIndex ≠ v) (h : Before v k s) :
    Before v k (processInclusionList s il b) := by
  obtain ⟨hstored, hequiv⟩ := h
  rcases processInclusionList_cases s il b with he | he | he <;> rw [he]
  · exact ⟨hstored, hequiv⟩
  · exact ⟨hstored, equivocators_withEquivocator_of_ne s il k v hv hequiv⟩
  · exact ⟨fun r l hl hlv =>
      hstored r l (storedAt_withStored_of_ne s il b k r v l hv hl hlv) hlv, hequiv⟩

/-- The first arrival of `il` at its key. Under `Before`, `processInclusionList` takes
branch (C) and stores `il` with the timeliness `b` of this arrival. So `After il b`
holds. -/
theorem after_first (s : InclusionListStore map) (il : InclusionList) (b : Bool)
    (h : Before il.validatorIndex il.inclusionListCommitteeRoot s) :
    After il b (processInclusionList s il b) := by
  obtain ⟨hstored, hA⟩ := h
  have hfind := find?_values_eq_none s il.inclusionListCommitteeRoot il.validatorIndex
    hstored
  -- `processInclusionList` spells out the lookup that `listsAt` names.
  unfold listsAt at hfind
  -- Branch (C): the validator is not an equivocator, and no stored list comes from it.
  have hC : processInclusionList s il b = withStored s il b := by
    simp only [processInclusionList, hA, hfind, Bool.false_eq_true, if_false]
    rfl
  rw [hC]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [storedAt_withStored]
    simp
  · exact LawfulFcMap.lookup_insert_self _ _ _
  · intro r l hl hlv
    rw [storedAt_withStored] at hl
    split at hl
    · cases hl
      rfl
    · exact absurd hlv (hstored r l hl)
  · exact hA

/-- Under the two assumptions on an arriving list `a`, `After il bil` holds after the
step. The timeliness `b` of the arrival does not change the timeliness `bil` of `il`.
`hsig`: a list from the validator of `il` for the same committee key is `il`. It holds
when the key names one slot (module docstring). `hhash`: a list other than `il` has a
different root. The hash is collision resistant. -/
theorem after_step (s : InclusionListStore map) (il a : InclusionList) (bil b : Bool)
    (hsig : a.inclusionListCommitteeRoot = il.inclusionListCommitteeRoot →
      a.validatorIndex = il.validatorIndex → a = il)
    (hhash : a ≠ il → htr a ≠ htr il)
    (h : After il bil s) : After il bil (processInclusionList s a b) := by
  obtain ⟨hil, htimely, huniq, hequiv⟩ := h
  by_cases hai : a = il
  · -- The same list again. `hequiv` closes branch (A), and branch (B) finds `il`.
    subst hai
    have hsame : processInclusionList s a b = s := by
      simp only [processInclusionList, hequiv, Bool.false_eq_true, if_false]
      split
      · rename_i existing hfound
        obtain ⟨⟨r, hr⟩, hv⟩ := find?_values_stored s _ _ existing hfound
        rw [huniq r existing hr hv, beq_self_eq_true]
        rfl
      · rename_i hnone
        -- `a` is stored at its key, so `find?` cannot return `none`.
        exfalso
        rw [List.find?_eq_none] at hnone
        exact hnone a ((FcMap.mem_values _ a).mpr ⟨_, hil⟩) (by simp)
    rw [hsame]
    exact ⟨hil, htimely, huniq, hequiv⟩
  · have hv : a.inclusionListCommitteeRoot = il.inclusionListCommitteeRoot →
        a.validatorIndex ≠ il.validatorIndex := fun hk h => hai (hsig hk h)
    have hr : htr a ≠ htr il := hhash hai
    rcases processInclusionList_cases s a b with he | he | he <;> rw [he]
    · exact ⟨hil, htimely, huniq, hequiv⟩
    · exact ⟨hil, htimely, huniq, equivocators_withEquivocator_of_ne s a _ _ hv hequiv⟩
    · refine ⟨?_, ?_, fun r' l hl hlv =>
        huniq r' l (storedAt_withStored_of_ne s a b _ r' _ l hv hl hlv) hlv, hequiv⟩
      · rw [storedAt_withStored]
        simp [Ne.symm hr, hil]
      · simp only [withStored]
        rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hr]
        exact htimely

/-- The lists in `before` keep `Before v k` when none of them comes from `v` at `k`. -/
theorem before_arrivals [Config] (v : ValidatorIndex) (k : Root) :
    ∀ (before : List (SignedInclusionList × UInt64)) (s : InclusionListStore map),
      (∀ a ∈ before, a.1.message.inclusionListCommitteeRoot = k →
        a.1.message.validatorIndex ≠ v) →
      Before v k s → Before v k (before.foldl arrivalStep s) := by
  intro before
  induction before with
  | nil => intro s _ h; exact h
  | cons a rest ih =>
    intro s hne h
    exact ih _ (fun a' ha' => hne a' (by simp [ha']))
      (before_step _ _ _ _ _ (hne a (by simp)) h)

/-- The lists in `after` keep `After il bil` under the two assumptions on each list. -/
theorem after_arrivals [Config] (il : InclusionList) (bil : Bool) :
    ∀ (after : List (SignedInclusionList × UInt64)) (s : InclusionListStore map),
      (∀ a ∈ after, a.1.message.inclusionListCommitteeRoot = il.inclusionListCommitteeRoot →
        a.1.message.validatorIndex = il.validatorIndex → a.1.message = il) →
      (∀ a ∈ after, a.1.message ≠ il → htr a.1.message ≠ htr il) →
      After il bil s → After il bil (after.foldl arrivalStep s) := by
  intro after
  induction after with
  | nil => intro s _ _ h; exact h
  | cons a rest ih =>
    intro s hsig hhash h
    exact ih _ (fun a' ha' => hsig a' (by simp [ha'])) (fun a' ha' => hhash a' (by simp [ha']))
      (after_step _ il a.1.message bil _ (hsig a (by simp)) (hhash a (by simp)) h)

end ILStore

/-- Every stored list has a timeliness entry after any arrival list. -/
theorem total_arrivals [Config] (arrivals : List (SignedInclusionList × UInt64)) :
    ILStore.Total (ilStoreOfArrivals (map := map) arrivals) := by
  unfold ilStoreOfArrivals
  suffices h : ∀ s : InclusionListStore map, ILStore.Total s →
      ILStore.Total (arrivals.foldl ILStore.arrivalStep s) from
    h _ ILStore.total_empty
  induction arrivals with
  | nil => intro s h; exact h
  | cons a rest ih => intro s h; exact ih _ (ILStore.total_step _ _ _ h)

/-- The honest list after the arrivals. The arrival list is `before ++ (signed, t) :: after`
with `signed.message = il`, under `ArrivalHypotheses il before after`.

`first` and `sig` read only lists for the committee key of `il`. The validator can send
lists for other committee keys. The module docstring explains when a key repeats across
slots. `hash` reads every list in `after`, because the timeliness map is keyed by list
root alone. `before` needs no such hypothesis: the first arrival of `il` takes branch (C),
which overwrites any entry at `htr il`.

Then the IL store holds `il` under its key at `htr il`, with the timeliness of the first
arrival: `true` when `t < getInclusionListDueMs`, and `false` otherwise. The validator of
`il` is not an equivocator at that key. -/
theorem honestStored_of_arrivals [Config]
    (before after : List (SignedInclusionList × UInt64)) (signed : SignedInclusionList)
    (t : UInt64) (il : InclusionList) (hil : signed.message = il)
    (h : ArrivalHypotheses il before after) :
    ILStore.After il (decide (t < getInclusionListDueMs))
      (ilStoreOfArrivals (map := map) (before ++ (signed, t) :: after)) := by
  subst hil
  unfold ilStoreOfArrivals
  rw [List.foldl_append, List.foldl_cons]
  apply ILStore.after_arrivals _ _ after _ h.sig h.hash
  have hB := ILStore.before_arrivals (map := map) signed.message.validatorIndex
    signed.message.inclusionListCommitteeRoot before _ h.first
    (ILStore.before_empty signed.message.validatorIndex signed.message.inclusionListCommitteeRoot)
  -- `arrivalStep` on `(signed, t)` unfolds to `processInclusionList` with this timeliness.
  exact ILStore.after_first _ signed.message (decide (t < getInclusionListDueMs)) hB

/-- `ArrivalHypotheses` holds for a validator that sits on two committees with different
keys. The validator signs `il'` under one key and `il` under the other. `il'` arrives
before `il`, and a copy of `il'` arrives again after it. The conditions are that the two
keys differ and that the two lists have different roots. A statement with `first` and
`sig` over every committee key fails for this history. -/
theorem arrivalHypotheses_two_keys (il il' : InclusionList) (t' : UInt64)
    (signed' : SignedInclusionList) (hil' : signed'.message = il')
    (hkey : il'.inclusionListCommitteeRoot ≠ il.inclusionListCommitteeRoot)
    (hroot : htr il' ≠ htr il) :
    ArrivalHypotheses il [(signed', t')] [(signed', t')] where
  first a ha := by
    simp only [List.mem_singleton] at ha
    subst ha
    simp only [hil']
    exact fun hk => absurd hk hkey
  sig a ha := by
    simp only [List.mem_singleton] at ha
    subst ha
    simp only [hil']
    exact fun hk => absurd hk hkey
  hash a ha := by
    simp only [List.mem_singleton] at ha
    subst ha
    simp only [hil']
    exact fun _ => hroot

end

end EthCLSpecs.Proofs.Heze
