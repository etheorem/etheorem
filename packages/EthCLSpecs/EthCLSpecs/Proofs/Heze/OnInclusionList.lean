import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLLib.Proofs.StateFree

/-!
# `EthCLSpecs.Proofs.Heze.OnInclusionList`: the honest list in the IL store

`onInclusionList` (`Heze/ForkChoice.lean:539-590`) reads the store, runs the checks of
v1.7.0-beta.4, judges the timeliness of the list, and then sets the store with the
result of `processInclusionList`. It sets the store it read first, so a successful run
writes only the IL store. `onInclusionList_run_ok` states this: a successful run is one
`processInclusionList` step with a timeliness bit `b`. The bit is `true` exactly when
`InclusionListTimely` holds: the list is for the current slot, and the time into the
slot is before the deadline `getInclusionListDueMs`. The deadline raises when its checked
product `INCLUSION_LIST_DUE_BPS * SLOT_DURATION_MS` overflows, and such a run is not
successful.

The arrival model is a list of `(SignedInclusionList, Bool)` pairs: each list that
`onInclusionList` accepted, and the timeliness bit of that run. `ilStoreOfArrivals` folds
`processInclusionList` over the list, from the empty IL store that `getForkchoiceStore`
seeds. In the model, only `onInclusionList` writes the IL store. So the model assumes two
things: the store started from the seed, and every arrival went through a successful
`onInclusionList` run, in list order.

`honestStored_of_arrivals` proves the main fact. Take an honest list `il`, and suppose
`ArrivalHypotheses il before after`. Then, after the arrivals, the IL store holds an
entry for `il` under its key `(slot, dependent_root)` and its validator, with the
timeliness of its first arrival. The validator of `il` is not an equivocator for that
key. The validator can send lists for other keys, and `arrivalHypotheses_two_keys` shows
that the hypotheses hold for such a history.

The store holds one entry per validator and key. The key carries the slot, so a list for
one slot never shares a key with a list for another slot.

The first arrival sets the timeliness. A later arrival of the same list finds the stored
entry and changes nothing. Thus the store keeps an honest list that first arrives late as
late, even when a copy arrives on time later. This is the spec behavior.

The proofs use the `==` on `InclusionList`, a derived structural `BEq`. The `ReflBEq`
instance below makes it reflexive (`beq_self_eq_true`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs
open EthCLSpecs.Heze (Preset Config Store Root Slot InclusionList InclusionListStore
  InclusionListEntry SignedInclusionList Transaction ValidatorIndex onInclusionList
  processInclusionList getCurrentSlot getTimeIntoSlotMs getInclusionListDueMs)

/-- `==` on `Transaction` is lawful. The instance comes from `DecidableEq` on the subtype. -/
example : LawfulBEq Transaction := inferInstance

-- Core's `ReflBEq` handler proves that the derived `BEq` is reflexive, field by field.
deriving instance ReflBEq for InclusionList

section Handler
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- The list is timely at `store`. The current slot is `slot`, and the time into the slot
is before the deadline `getInclusionListDueMs`, which does not raise. Both reads take the
store argument and no runner state. -/
def InclusionListTimely (store : Store map) (slot : Slot) : Prop :=
  (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
      = .ok (slot, store) ∧
    ∃ t d, (getTimeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) store).run
        store = .ok (t, store) ∧ getInclusionListDueMs = .ok d ∧ t < d

omit [Preset] [HasherTag] [Config] in
/-- A successful `liftErr` run reads an `.ok` value and keeps the state. -/
private theorem run_liftErr_eq_ok {σ ε' ε α : Type} [ErrorConv ε' ε] (x : Except ε' α)
    (sb s : σ) (a : α)
    (h : (liftErr (m := StateT σ (Except ε)) (E := ε') (F := ε) x).run sb = .ok (a, s)) :
    x = .ok a ∧ s = sb := by
  cases x with
  | error e =>
    rw [run_liftErr_of_error _ sb rfl] at h
    cases h
  | ok a' =>
    rw [run_liftErr_of_ok _ sb rfl] at h
    injection h with h
    injection h with h1 h2
    exact ⟨by rw [h1], h2.symm⟩

omit [FcMap map] in
/-- `getCurrentSlot` reads no runner state. -/
theorem getCurrentSlot_stateFree (store : Store map) :
    StateFree (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store) := by
  unfold getCurrentSlot EthCLSpecs.Heze.getSlotsSinceGenesis liftErr
  free_solve

omit [FcMap map] in
/-- `getTimeIntoSlotMs` reads no runner state. -/
theorem getTimeIntoSlotMs_stateFree (store : Store map) :
    StateFree
      (getTimeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) store) := by
  unfold getTimeIntoSlotMs getCurrentSlot EthCLSpecs.Heze.getSlotsSinceGenesis liftErr
    checkedSub
  free_solve

variable [CryptoBackend]

/-- A successful `onInclusionList` run writes only the IL store. The new IL store is
`processInclusionList` of the old one, the signed list, and a timeliness bit `b`. The bit
is `true` exactly when the list is timely at the store (`InclusionListTimely`). -/
theorem onInclusionList_run_ok (store s' : Store map) (signed : SignedInclusionList)
    (h : (onInclusionList (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      signed).run store = .ok ((), s')) :
    ∃ b : Bool,
      s' = { store with inclusionListStore :=
        processInclusionList store.inclusionListStore signed b } ∧
      (b = true ↔ InclusionListTimely store signed.message.slot) := by
  unfold onInclusionList at h
  -- The handler reads the store first. That read returns `store` in `store`.
  obtain ⟨st0, s0, hget, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hget' : (Except.ok (st0, s0) : Except StoreTransitionError _) = .ok (store, store) :=
    hget.symm.trans rfl
  injection hget' with hget'
  injection hget' with h0 h1
  subst st0 s0
  -- The current slot, read at `store`.
  obtain ⟨cs, s1, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hs1 := ((getCurrentSlot_stateFree store).run_eq hcs).1
  subst s1
  -- The tail, the same in both branches of the lookahead check: the timeliness bit, then
  -- the `set` of the store the handler read first.
  have htail : ∀ (st : Store map),
      (if (signed.message.slot == cs) = true then
          (do
            let t ← getTimeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) store
            let d ← liftErr (m := ForkChoiceStoreRun (Store map)) (F := StoreTransitionError)
              getInclusionListDueMs
            let isTimely ← pure (decide (t < d))
            set ({ store with inclusionListStore :=
              processInclusionList store.inclusionListStore signed isTimely } : Store map))
        else
          (do
            let isTimely ← pure false
            set ({ store with inclusionListStore :=
              processInclusionList store.inclusionListStore signed isTimely } : Store map))
        : ForkChoiceStoreRun (Store map) Unit).run st = .ok ((), s') →
      ∃ b : Bool,
        s' = { store with inclusionListStore :=
          processInclusionList store.inclusionListStore signed b } ∧
        (b = true ↔ InclusionListTimely store signed.message.slot) := by
    intro st hrun
    split at hrun
    · rename_i hslot
      obtain ⟨t, s2, ht, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      obtain ⟨d, s4, hd, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      obtain ⟨b, s3, hb, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      have hbt := run_pure_eq_ok _ _ _ _ hb
      have htStore := ((getTimeIntoSlotMs_stateFree store).run_eq ht).2 store
      have hdue := (run_liftErr_eq_ok _ _ _ _ hd).1
      injection hrun with hrun
      injection hrun with _ hrun
      refine ⟨b, hrun.symm, ?_⟩
      subst hbt
      have hcsSlot : signed.message.slot = cs := beq_iff_eq.mp hslot
      constructor
      · intro hlt
        exact ⟨hcsSlot ▸ hcs, t, d, htStore, hdue, of_decide_eq_true hlt⟩
      · rintro ⟨-, t', d', ht', hd', hlt⟩
        rw [htStore] at ht'
        injection ht' with ht'
        injection ht' with ht'
        subst ht'
        rw [hdue] at hd'
        injection hd' with hd'
        subst hd'
        exact decide_eq_true hlt
    · rename_i hslot
      obtain ⟨b, s3, hb, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      have hbf := run_pure_eq_ok _ _ _ _ hb
      injection hrun with hrun
      injection hrun with _ hrun
      refine ⟨b, hrun.symm, ?_⟩
      subst hbf
      constructor
      · intro hf
        exact absurd hf Bool.false_ne_true
      rintro ⟨hcur, -⟩
      -- A timely list is for the current slot, which the handler read as `cs`.
      rw [hcs] at hcur
      injection hcur with hcur
      injection hcur with hcur
      exact absurd (beq_iff_eq.mpr hcur.symm) hslot
  -- The checks between the clock read and the lookahead branch: each one either raises or
  -- passes, and none of them sets the store.
  repeat (first
    | (dsimp only at h)
    | (obtain ⟨_, _, _, h⟩ := run_bind_eq_ok _ _ _ _ h))
  split at h <;>
    (repeat (obtain ⟨_, _, _, h⟩ := run_bind_eq_ok _ _ _ _ h)) <;>
    exact htail _ h

end Handler

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The store key of a list: its slot and its dependent root. -/
def ilKey (il : InclusionList) : Slot × Root := (il.slot, il.dependentRoot)

/-- The store after the stored-entry branch with a different list: the validator of `il`
joins the equivocators at the key of `il`. -/
def withEquivocator (s : InclusionListStore map) (il : InclusionList) :
    InclusionListStore map :=
  { s with
      equivocators :=
        FcMap.insert s.equivocators (ilKey il)
          ((FcMap.lookupD s.equivocators (ilKey il)).push il.validatorIndex) }

/-- The store after the no-entry branch: an entry with `signed` and the timeliness `b`, at
the key of the list and its validator. -/
def withStored (s : InclusionListStore map) (signed : SignedInclusionList) (b : Bool) :
    InclusionListStore map :=
  { s with
      inclusionLists :=
        FcMap.insert s.inclusionLists (ilKey signed.message)
          (FcMap.insert (ILStore.entriesAt s (ilKey signed.message))
            signed.message.validatorIndex
            ({ signedInclusionList := signed, timely := b } : InclusionListEntry)) }

/-- `processInclusionList` has three results. It leaves the store unchanged (a stored
entry with an equal list, or an equivocator already marked). It adds the validator to
the equivocators at the key (a stored entry with a different list). It stores an entry
for the list (no stored entry). -/
theorem processInclusionList_cases (s : InclusionListStore map) (signed : SignedInclusionList)
    (b : Bool) :
    processInclusionList s signed b = s ∨
    processInclusionList s signed b = withEquivocator s signed.message ∨
    processInclusionList s signed b = withStored s signed b := by
  simp only [processInclusionList]
  split
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

/-- The assumptions on the arrival list `before ++ (signed, b) :: after` for an honest
list `il`:

- `first`: no list in `before` comes from the validator of `il` for the key of `il`. So
  `(signed, b)` is the first arrival of a list from that validator for that key.
- `sig` (one list per key): each list in `after` from the validator of `il`, for the key
  of `il`, is `il`. -/
structure ArrivalHypotheses (il : InclusionList)
    (before after : List (SignedInclusionList × Bool)) : Prop where
  first : ∀ a ∈ before, ilKey a.1.message = ilKey il →
    a.1.message.validatorIndex ≠ il.validatorIndex
  sig : ∀ a ∈ after, ilKey a.1.message = ilKey il →
    a.1.message.validatorIndex = il.validatorIndex → a.1.message = il

namespace ILStore

/-- At the key `k`, the store holds no entry for `v`, and `v` is not an equivocator. -/
def Before (v : ValidatorIndex) (k : Slot × Root) (s : InclusionListStore map) : Prop :=
  entryAt s k v = none ∧ (FcMap.lookupD s.equivocators k).contains v = false

/-- At the key of `il`, the entry for the validator of `il` holds `il` with timeliness
`b`, and the validator is not an equivocator. -/
def After (il : InclusionList) (b : Bool) (s : InclusionListStore map) : Prop :=
  (∃ e, entryAt s (ilKey il) il.validatorIndex = some e ∧
    e.signedInclusionList.message = il ∧ e.timely = b) ∧
  (FcMap.lookupD s.equivocators (ilKey il)).contains il.validatorIndex = false

/-- The fold step of the arrival model. -/
def arrivalStep (s : InclusionListStore map) (a : SignedInclusionList × Bool) :
    InclusionListStore map :=
  processInclusionList s a.1 a.2

end ILStore

/-- The IL store after the arrival list. Each arrival is a signed list and the timeliness
bit of its `onInclusionList` run. The fold starts from the empty IL store, the seed of
`getForkchoiceStore`. -/
def ilStoreOfArrivals (arrivals : List (SignedInclusionList × Bool)) :
    InclusionListStore map :=
  arrivals.foldl ILStore.arrivalStep InclusionListStore.empty

variable [LawfulFcMap map (Slot × Root)] [LawfulFcMap map ValidatorIndex]

namespace ILStore

/-- An entry after the no-entry branch. The new entry is at the key of the list and its
validator. Every other lookup returns the old entry. -/
theorem entryAt_withStored (s : InclusionListStore map) (signed : SignedInclusionList)
    (b : Bool) (k : Slot × Root) (v : ValidatorIndex) :
    entryAt (withStored s signed b) k v
      = if k = ilKey signed.message ∧ v = signed.message.validatorIndex then
          some ({ signedInclusionList := signed, timely := b } : InclusionListEntry)
        else entryAt s k v := by
  unfold entryAt entriesAt withStored
  by_cases hk : ilKey signed.message = k
  · subst hk
    rw [LawfulFcMap.lookup_insert_self]
    by_cases hv : signed.message.validatorIndex = v
    · subst hv
      simp [entriesAt]
    · simp [LawfulFcMap.lookup_insert_ne _ _ _ _ hv, Ne.symm hv, entriesAt]
  · simp [LawfulFcMap.lookup_insert_ne _ _ _ _ hk, Ne.symm hk]

omit [LawfulFcMap map ValidatorIndex] in
/-- An equivocator entry after the stored-entry branch with a different list. The
validator of `il` joins the entry at the key of `il`. Every other entry stays. -/
theorem equivocators_withEquivocator (s : InclusionListStore map) (il : InclusionList)
    (k : Slot × Root) (v : ValidatorIndex) :
    (FcMap.lookupD (withEquivocator s il).equivocators k).contains v
      = ((FcMap.lookupD s.equivocators k).contains v ||
          (k == ilKey il && v == il.validatorIndex)) := by
  unfold withEquivocator
  simp only [FcMap.lookupD]
  by_cases hk : ilKey il = k
  · subst hk
    rw [LawfulFcMap.lookup_insert_self]
    cases h : (v == il.validatorIndex) <;> simp_all
  · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk]
    simp [Ne.symm hk]

omit [LawfulFcMap map ValidatorIndex] in
/-- The stored-entry branch with a different list keeps `v` out of the equivocators at
`k` when the list does not come from `v` at `k`. -/
theorem equivocators_withEquivocator_of_ne (s : InclusionListStore map) (il : InclusionList)
    (k : Slot × Root) (v : ValidatorIndex)
    (hv : ilKey il = k → il.validatorIndex ≠ v)
    (h : (FcMap.lookupD s.equivocators k).contains v = false) :
    (FcMap.lookupD (withEquivocator s il).equivocators k).contains v = false := by
  rw [equivocators_withEquivocator, h]
  by_cases hk : ilKey il = k
  · simp [hk, Ne.symm (hv hk)]
  · simp [Ne.symm hk]

/-- The empty IL store satisfies `Before v k` for every validator and key. -/
theorem before_empty (v : ValidatorIndex) (k : Slot × Root) :
    Before v k (InclusionListStore.empty : InclusionListStore map) := by
  refine ⟨?_, ?_⟩
  · simp [entryAt, entriesAt, InclusionListStore.empty, LawfulFcMap.lookup_empty]
  · simp [FcMap.lookupD, InclusionListStore.empty, LawfulFcMap.lookup_empty,
      show (default : Array ValidatorIndex) = #[] from rfl]

/-- A list keeps `Before v k` unless it comes from `v` at the key `k`. -/
theorem before_step (v : ValidatorIndex) (k : Slot × Root) (s : InclusionListStore map)
    (signed : SignedInclusionList) (b : Bool)
    (hv : ilKey signed.message = k → signed.message.validatorIndex ≠ v)
    (h : Before v k s) : Before v k (processInclusionList s signed b) := by
  obtain ⟨hentry, hequiv⟩ := h
  rcases processInclusionList_cases s signed b with he | he | he <;> rw [he]
  · exact ⟨hentry, hequiv⟩
  · exact ⟨hentry, equivocators_withEquivocator_of_ne s _ k v hv hequiv⟩
  · refine ⟨?_, hequiv⟩
    rw [entryAt_withStored, ite_eq_right (fun hkv => hv hkv.1.symm hkv.2.symm), hentry]

/-- The first arrival of a list at its key. Under `Before`, `processInclusionList` takes
the no-entry branch and stores the list with the timeliness `b` of this arrival. So
`After` holds. -/
theorem after_first (s : InclusionListStore map) (signed : SignedInclusionList) (b : Bool)
    (h : Before signed.message.validatorIndex (ilKey signed.message) s) :
    After signed.message b (processInclusionList s signed b) := by
  obtain ⟨hentry, hequiv⟩ := h
  have hstored : processInclusionList s signed b = withStored s signed b := by
    unfold entryAt entriesAt ilKey at hentry
    simp only [processInclusionList, hentry]
    rfl
  rw [hstored]
  refine ⟨⟨{ signedInclusionList := signed, timely := b }, ?_, rfl, rfl⟩, hequiv⟩
  rw [entryAt_withStored, ite_eq_left ⟨rfl, rfl⟩]

/-- Under the assumption on an arriving list `a`, `After il bil` holds after the step.
The timeliness `b` of the arrival does not change the timeliness `bil` of `il`. `hsig`:
a list from the validator of `il` for the same key is `il`. -/
theorem after_step (s : InclusionListStore map) (il : InclusionList)
    (a : SignedInclusionList) (bil b : Bool)
    (hsig : ilKey a.message = ilKey il → a.message.validatorIndex = il.validatorIndex →
      a.message = il)
    (h : After il bil s) : After il bil (processInclusionList s a b) := by
  obtain ⟨⟨e, hentry, hmsg, htimely⟩, hequiv⟩ := h
  by_cases hai : a.message = il
  · -- The same list again: the stored entry holds an equal list, so nothing changes.
    subst hai
    have hsame : processInclusionList s a b = s := by
      unfold entryAt entriesAt ilKey at hentry
      simp only [processInclusionList, hentry, hmsg, bne, beq_self_eq_true, Bool.not_true,
        Bool.false_and, Bool.false_eq_true, ite_false]
    rw [hsame]
    exact ⟨⟨e, hentry, hmsg, htimely⟩, hequiv⟩
  · have hv : ilKey a.message = ilKey il → a.message.validatorIndex ≠ il.validatorIndex :=
      fun hk hvv => hai (hsig hk hvv)
    rcases processInclusionList_cases s a b with he | he | he <;> rw [he]
    · exact ⟨⟨e, hentry, hmsg, htimely⟩, hequiv⟩
    · exact ⟨⟨e, hentry, hmsg, htimely⟩,
        equivocators_withEquivocator_of_ne s _ _ _ hv hequiv⟩
    · refine ⟨⟨e, ?_, hmsg, htimely⟩, hequiv⟩
      rw [entryAt_withStored, ite_eq_right (fun hkv => hv hkv.1.symm hkv.2.symm), hentry]

/-- The lists in `before` keep `Before v k` when none of them comes from `v` at `k`. -/
theorem before_arrivals (v : ValidatorIndex) (k : Slot × Root) :
    ∀ (before : List (SignedInclusionList × Bool)) (s : InclusionListStore map),
      (∀ a ∈ before, ilKey a.1.message = k → a.1.message.validatorIndex ≠ v) →
      Before v k s → Before v k (before.foldl arrivalStep s) := by
  intro before
  induction before with
  | nil => intro s _ h; exact h
  | cons a rest ih =>
    intro s hne h
    exact ih _ (fun a' ha' => hne a' (by simp [ha']))
      (before_step _ _ _ _ _ (hne a (by simp)) h)

/-- The lists in `after` keep `After il bil` under the assumption on each list. -/
theorem after_arrivals (il : InclusionList) (bil : Bool) :
    ∀ (after : List (SignedInclusionList × Bool)) (s : InclusionListStore map),
      (∀ a ∈ after, ilKey a.1.message = ilKey il →
        a.1.message.validatorIndex = il.validatorIndex → a.1.message = il) →
      After il bil s → After il bil (after.foldl arrivalStep s) := by
  intro after
  induction after with
  | nil => intro s _ h; exact h
  | cons a rest ih =>
    intro s hsig h
    exact ih _ (fun a' ha' => hsig a' (by simp [ha']))
      (after_step _ il a.1 bil _ (hsig a (by simp)) h)

end ILStore

/-- The honest list after the arrivals. The arrival list is `before ++ (signed, b) :: after`
with `signed.message = il`, under `ArrivalHypotheses il before after`.

`first` and `sig` read only lists for the key of `il`. The validator can send lists for
other keys. Then the IL store holds an entry for `il` under its key and its validator,
with the timeliness `b` of the first arrival. The validator of `il` is not an equivocator
at that key. -/
theorem honestStored_of_arrivals
    (before after : List (SignedInclusionList × Bool)) (signed : SignedInclusionList)
    (b : Bool) (il : InclusionList) (hil : signed.message = il)
    (h : ArrivalHypotheses il before after) :
    ILStore.After il b (ilStoreOfArrivals (map := map) (before ++ (signed, b) :: after)) := by
  subst hil
  unfold ilStoreOfArrivals
  rw [List.foldl_append, List.foldl_cons]
  apply ILStore.after_arrivals _ _ after _ h.sig
  have hB := ILStore.before_arrivals (map := map) signed.message.validatorIndex
    (ilKey signed.message) before _ h.first
    (ILStore.before_empty signed.message.validatorIndex (ilKey signed.message))
  exact ILStore.after_first _ signed b hB

omit [HasherTag] [LawfulFcMap map (Slot × Root)] [LawfulFcMap map ValidatorIndex] in
/-- `ArrivalHypotheses` holds for a validator that sends lists for two keys. The validator
signs `il'` under one key and `il` under the other. `il'` arrives before `il`, and a copy
of `il'` arrives again after it. The condition is that the two keys differ. A statement
with `first` and `sig` over every key fails for this history. -/
theorem arrivalHypotheses_two_keys (il il' : InclusionList) (b' : Bool)
    (signed' : SignedInclusionList) (hil' : signed'.message = il')
    (hkey : ilKey il' ≠ ilKey il) :
    ArrivalHypotheses il [(signed', b')] [(signed', b')] where
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

end

end EthCLSpecs.Proofs.Heze
