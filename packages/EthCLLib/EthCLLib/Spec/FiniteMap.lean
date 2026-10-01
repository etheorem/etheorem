import Init.Data.Ord.Vector
import Init.Data.Range.Lemmas
import Init.Data.Vector.Lemmas
import Init.Data.List.TakeDrop
import Init.Data.List.Monadic
import Std.Data.TreeMap
import Std.Data.HashMap
import SizzLean
import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Spec.FiniteMap`: the fork-choice map backing, higher-kinded

The fork-choice `Store` holds finite maps over several key types
(`Root` / `Checkpoint` / `ValidatorIndex`), and the framework abstracts the *map
backing* as a single higher-kinded family so the store's laws are provable on a
deterministic backing while the runner uses a fast one
(`FRAMEWORK_ARCHITECTURE.md` §9).

`MapKind` is the kind a `map` variable ranges over: a function from a key type
(carrying the structure a stock map needs) and a value type to a concrete map.
Its kind bakes the **union** `[Ord K] [BEq K] [Hashable K]`, so one shape backs
both `treeMap` (ordered, `Ord`, proof-friendly, deterministic key order) and
`hashMap` (`BEq` + `Hashable`, `O(1)`, the runner's). `Store` is parameterized by
`map` alone, so `Store treeMap` and `Store hashMap` are distinct types that
coexist with no ambient current map.
-/

set_option autoImplicit false

open SizzLean.Repr

namespace EthCLLib.Spec

/-- Hash a fixed-length vector by its array, so a `Vector`-keyed map (`Root =
Vector UInt8 32`, …) can use `hashMap`. -/
instance instHashableVector {α : Type} {n : Nat} [Hashable α] : Hashable (Vector α n) :=
  ⟨fun v => hash v.toArray⟩

/-- Lexicographic `Ord` on a fixed-length byte vector, so a `Root`- or
`Checkpoint`-keyed map satisfies `MapKind`'s `[Ord K]`. It sits here beside
`instHashableVector` for the same reason: `Vector UInt8 n` is a SizzLean type
naming no spec concept, so no fork owns it. -/
instance instOrdVectorUInt8 {n : Nat} : Ord (Vector UInt8 n) where
  compare a b := Id.run do
    for i in [0:n] do
      let x := a.toArray[i]!
      let y := b.toArray[i]!
      if x < y then return .lt
      if x > y then return .gt
    return .eq

/-! ### Lawful order for `instOrdVectorUInt8`

The standard `Std.TransOrd (Vector α n)` instance is
`Std.TransCmp (Vector.compareLex compare)`. It does not synthesize for
`Vector UInt8 n`: `Ord (Vector UInt8 n)` is `instOrdVectorUInt8`, and
that `compare` is a `forIn` loop, not definitionally
`Vector.compareLex compare`. The loop is extensionally the standard
lexicographic comparator. Transitivity transports along that
equality.
-/

section instOrdVectorUInt8_lawful
open Std Legacy

private theorem uint8_lt_gt_eq_compare (x y : UInt8) :
    (if x < y then Ordering.lt else if x > y then Ordering.gt else Ordering.eq)
      = compare x y := by
  rcases Nat.lt_trichotomy x.toNat y.toNat with h | h | h
  · have hlt : x < y := (UInt8.lt_iff_toNat_lt).2 h
    simp [hlt, compare, compareOfLessAndEq]
  · have heq : x = y := UInt8.toNat_inj.mp h
    subst heq
    simp [compare, compareOfLessAndEq]
  · have hgt : x > y := gt_iff_lt.mpr ((UInt8.lt_iff_toNat_lt).2 h)
    have hnlt : ¬ x < y := fun hlt =>
      Nat.lt_irrefl _ (Nat.lt_trans h ((UInt8.lt_iff_toNat_lt).1 hlt))
    simp [hnlt, hgt, compare, compareOfLessAndEq]
    intro heq
    exact Nat.lt_irrefl _ (heq ▸ h)

/-- Recursive form of the `instOrdVectorUInt8` loop, from index `i`. -/
private def vectorUInt8CompareGo {n : Nat} (a b : Vector UInt8 n) (i : Nat) : Ordering :=
  if h : i < n then
    if a[i] < b[i] then .lt
    else if a[i] > b[i] then .gt
    else vectorUInt8CompareGo a b (i + 1)
  else
    .eq
termination_by n - i

private theorem vectorUInt8CompareGo_eq_listCompareLex {n : Nat}
    (a b : Vector UInt8 n) :
    ∀ i, i ≤ n →
      vectorUInt8CompareGo a b i =
        List.compareLex compare (a.toList.drop i) (b.toList.drop i) := by
  intro i hi
  induction hdiff : n - i generalizing i with
  | zero =>
    have hle : n ≤ i := Nat.le_of_sub_eq_zero hdiff
    unfold vectorUInt8CompareGo
    have hnlt : ¬ i < n := Nat.not_lt.mpr hle
    rw [dif_neg hnlt]
    rw [List.drop_eq_nil_of_le (by simpa [Vector.length_toList] using hle)]
    rw [List.drop_eq_nil_of_le (by simpa [Vector.length_toList] using hle)]
    rfl
  | succ k ih =>
    have hlt : i < n := Nat.lt_of_sub_pos (by simp [hdiff])
    unfold vectorUInt8CompareGo
    rw [dif_pos hlt]
    have hlen : i < a.toList.length := by simpa [Vector.length_toList] using hlt
    have hlenb : i < b.toList.length := by simpa [Vector.length_toList] using hlt
    rw [List.drop_eq_getElem_cons hlen, List.drop_eq_getElem_cons hlenb,
        List.compareLex_cons_cons]
    have hx : a.toList[i] = a[i] := Vector.getElem_toList (xs := a) (i := i)
      (h := by simpa [Vector.length_toList] using hlt)
    have hy : b.toList[i] = b[i] := Vector.getElem_toList (xs := b) (i := i)
      (h := by simpa [Vector.length_toList] using hlt)
    rw [hx, hy, ← uint8_lt_gt_eq_compare]
    split
    · simp [Ordering.then]
    · split
      · simp [Ordering.then]
      · simp [Ordering.then]
        exact ih (i + 1) (Nat.succ_le_of_lt hlt) (by omega)

/-- One step of the early-return `forIn` that `instOrdVectorUInt8` runs. -/
private def vectorUInt8CompareStep {n : Nat} (a b : Vector UInt8 n) (i : Nat) :
    Id (ForInStep (MProd (Option Ordering) PUnit)) :=
  let x := a.toArray[i]!
  let y := b.toArray[i]!
  if x < y then
    pure (ForInStep.done ⟨some .lt, ()⟩)
  else if x > y then
    pure (ForInStep.done ⟨some .gt, ()⟩)
  else
    pure (ForInStep.yield ⟨none, ()⟩)

/-- The `instOrdVectorUInt8` loop, starting at index `i`. -/
private def vectorUInt8CompareForIn {n : Nat} (a b : Vector UInt8 n) (i : Nat) :
    Ordering :=
  Id.run (
    forIn (List.range' i (n - i) 1)
      (MProd.mk (none : Option Ordering) PUnit.unit)
      (fun j _ => vectorUInt8CompareStep a b j)
    >>= fun r =>
      match r.fst with
      | none => pure Ordering.eq
      | some o => pure o)

private theorem instOrdVectorUInt8_compare_eq_forIn_zero {n : Nat}
    (a b : Vector UInt8 n) :
    compare a b = vectorUInt8CompareForIn a b 0 := by
  simp only [compare, vectorUInt8CompareForIn]
  simp [Range.forIn_eq_forIn_range', Range.size, vectorUInt8CompareStep, pure_bind]

private theorem vectorUInt8CompareForIn_eq_ite {n : Nat} (a b : Vector UInt8 n)
    (i k : Nat) (hlt : i < n) (hdiff : n - i = k + 1) :
    vectorUInt8CompareForIn a b i =
      if a[i] < b[i] then Ordering.lt
      else if a[i] > b[i] then Ordering.gt
      else vectorUInt8CompareForIn a b (i + 1) := by
  have hrange :
      List.range' i (n - i) 1 = i :: List.range' (i + 1) k 1 := by
    rw [hdiff, List.range'_succ]
  unfold vectorUInt8CompareForIn
  rw [hrange, List.forIn_cons]
  have hsz : i < a.toArray.size := by simp [hlt]
  have hszb : i < b.toArray.size := by simp [hlt]
  simp only [vectorUInt8CompareStep, getElem!_pos (c := a.toArray) i hsz,
    getElem!_pos (c := b.toArray) i hszb, Vector.getElem_toArray]
  split
  · simp
  · split
    · simp
    · have htail : n - (i + 1) = k := by omega
      simp [htail]

private theorem vectorUInt8CompareForIn_eq_eq {n : Nat} (a b : Vector UInt8 n)
    (i : Nat) (hle : n ≤ i) :
    vectorUInt8CompareForIn a b i = Ordering.eq := by
  have hlen : n - i = 0 := Nat.sub_eq_zero_of_le hle
  unfold vectorUInt8CompareForIn
  simp [hlen, List.forIn_nil]

private theorem vectorUInt8CompareForIn_eq_compareGo {n : Nat}
    (a b : Vector UInt8 n) :
    ∀ i, i ≤ n → vectorUInt8CompareForIn a b i = vectorUInt8CompareGo a b i := by
  intro i hi
  induction hdiff : n - i generalizing i with
  | zero =>
    have hle : n ≤ i := Nat.le_of_sub_eq_zero hdiff
    rw [vectorUInt8CompareForIn_eq_eq a b i hle]
    unfold vectorUInt8CompareGo
    simp [Nat.not_lt.mpr hle]
  | succ k ih =>
    have hlt : i < n := Nat.lt_of_sub_pos (by simp [hdiff])
    rw [vectorUInt8CompareForIn_eq_ite a b i k hlt hdiff]
    unfold vectorUInt8CompareGo
    rw [dif_pos hlt]
    split
    · rfl
    · split
      · rfl
      · exact ih (i + 1) (Nat.succ_le_of_lt hlt) (by omega)

/-- The `instOrdVectorUInt8` comparator agrees with the standard
lexicographic comparator `Vector.compareLex compare`. The standard
`Std.TransOrd (Vector α n)` instance proves transitivity of
`Vector.compareLex compare`. That is not definitionally the `compare`
of `instOrdVectorUInt8`, so the standard instance does not synthesize
for `Vector UInt8 n`. This extensional equality is the bridge. -/
theorem instOrdVectorUInt8_compare_eq_compareLex {n : Nat} :
    compare (α := Vector UInt8 n) = Vector.compareLex compare := by
  funext a b
  rw [instOrdVectorUInt8_compare_eq_forIn_zero,
    vectorUInt8CompareForIn_eq_compareGo a b 0 (Nat.zero_le _),
    vectorUInt8CompareGo_eq_listCompareLex a b 0 (Nat.zero_le _)]
  simpa [List.drop_zero] using
    (Vector.compareLex_eq_compareLex_toList
      (cmp := compare) (a := a) (b := b)).symm

/-- `instOrdVectorUInt8` is a transitive order. The standard
`Std.TransOrd (Vector α n)` instance does not apply: it is
`Std.TransCmp (Vector.compareLex compare)`, while `Std.TransOrd` for
this type asks for `Std.TransCmp` of `instOrdVectorUInt8.compare`.
Those comparators are extensionally equal by
`instOrdVectorUInt8_compare_eq_compareLex`, and this instance
transports transitivity along that equality. -/
instance instTransOrdVectorUInt8 {n : Nat} : TransOrd (Vector UInt8 n) where
  eq_swap := by
    intro a b
    simpa [instOrdVectorUInt8_compare_eq_compareLex] using
      OrientedCmp.eq_swap
        (cmp := Vector.compareLex (compare : UInt8 → UInt8 → Ordering))
        (a := a) (b := b)
  isLE_trans := by
    intro a b c hab hbc
    rw [instOrdVectorUInt8_compare_eq_compareLex] at hab hbc ⊢
    exact TransCmp.isLE_trans
      (cmp := Vector.compareLex (compare : UInt8 → UInt8 → Ordering))
      (a := a) (b := b) (c := c) hab hbc

/-- `instOrdVectorUInt8` returns `.eq` only on equal vectors. Core proves it for
`Vector.compareLex compare`, and `instOrdVectorUInt8_compare_eq_compareLex` moves it to
the byte loop. `treeMap`'s lookup laws need it to turn "the keys compare equal" into
`k = k'`. -/
instance instLawfulEqOrdVectorUInt8 {n : Nat} : LawfulEqOrd (Vector UInt8 n) :=
  show LawfulEqCmp (compare : Vector UInt8 n → Vector UInt8 n → Ordering) from
    instOrdVectorUInt8_compare_eq_compareLex ▸ inferInstance

end instOrdVectorUInt8_lawful

/-- The kind of a finite-map *family*: `key type → value type → concrete map`,
given the key carries the union of structure both stock maps need. -/
abbrev MapKind := (K : Type) → [Ord K] → [BEq K] → [Hashable K] → Type → Type

/-- The operation contract a fork-choice map provides. One instance serves every
key type at once (`map Root V`, `map Checkpoint V`, …). `lookup` is partial; a
miss is the `missingKey` reject of the error model. `fold` / `keys` back the
all-keys walks (`getHead`, the filtered block tree). -/
class FcMap (map : MapKind) where
  /-- The empty map. -/
  empty    : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V
  /-- Insert (or overwrite) a key. -/
  insert   : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → K → V → map K V
  /-- Lookup; `none` on a miss (the `missingKey` reject). -/
  lookup   : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → K → Option V
  /-- Membership test. -/
  contains : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → K → Bool
  /-- Left fold over the entries. -/
  fold     : {K V β : Type} → [Ord K] → [BEq K] → [Hashable K] → (β → K → V → β) → β → map K V → β
  /-- The keys, as a list. -/
  keys     : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → List K

/-- Lookup with a default, what the store accessors want. -/
def FcMap.lookupD {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    [Inhabited V] (m : map K V) (k : K) : V := (FcMap.lookup m k).getD default

/-- The map's values (the all-values walk the fork choice needs, e.g. scanning every stored
block for a proposer equivocation). -/
def FcMap.values {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    (m : map K V) : List V := (FcMap.keys m).filterMap (FcMap.lookup m ·)

/-- The keys whose entry satisfies `p` (the "children of a block" walk: the keys whose
stored value's `parentRoot` matches). `p` sees the key and the value. -/
def FcMap.filterKeys {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    (m : map K V) (p : K → V → Bool) : List K :=
  (FcMap.keys m).filter (fun k => match FcMap.lookup m k with | some v => p k v | none => false)

/-- `Std.TreeMap` family: ordered, deterministic key order, the proof-friendly
default (uses `[Ord K]`). -/
@[reducible] def treeMap : MapKind := fun K _ _ _ V => Std.TreeMap K V

/-- `Std.HashMap` family: `O(1)`, the runner's choice (uses `[BEq K] [Hashable K]`). -/
@[reducible] def hashMap : MapKind := fun K _ _ _ V => Std.HashMap K V

instance : FcMap treeMap where
  empty := ∅
  insert m k v := m.insert k v
  lookup m k := m.get? k
  contains m k := m.contains k
  fold f init m := m.foldl f init
  keys m := m.keys

instance : FcMap hashMap where
  empty := ∅
  insert m k v := m.insert k v
  lookup m k := m.get? k
  contains m k := m.contains k
  fold f init m := m.fold f init
  keys m := m.keys

/-- Look up `k` in a fork-choice map, or throw the store machine's `missingKey errKey`
reject (the `missingKey` branch of the error model). A handler binds it with `←` in place of
the `let some v := FcMap.lookup m k | throw (.missingKey …)` destructure, which repeats the
key. The error key is explicit because a `Checkpoint`-keyed lookup reports the checkpoint's
`root`, not the checkpoint itself. -/
def FcMap.getOrThrowKey {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    {m : Type → Type} [Monad m] [MonadExceptOf StoreTransitionError m]
    (mp : map K V) (k : K) (errKey : Vector UInt8 32) : m V :=
  match FcMap.lookup mp k with
  | some v => pure v
  | none   => throw (StoreTransitionError.missingKey errKey)

/-- `getOrThrowKey` for a `Root`-keyed map: a miss reports the lookup key itself.
The `Vector UInt8 32` structure it needs is all global here (`instOrdVectorUInt8`,
`instHashableVector`, `Vector`'s own `BEq`), so nothing rides in as a binder. -/
@[inline] def FcMap.getOrThrow {map : MapKind} [FcMap map] {V : Type}
    {m : Type → Type} [Monad m] [MonadExceptOf StoreTransitionError m]
    (mp : map (Vector UInt8 32) V) (k : Vector UInt8 32) : m V :=
  FcMap.getOrThrowKey mp k k

/-- Look up `k`, or throw the spec's `assert` reject. The fused form of the pyspec pair
`assert k in d` followed by `d[k]`: the membership assert is the spec's own opening line, so
a miss is an *expected rejection* (`.assert`), where `getOrThrow`'s bare-`d[k]` miss is
`missingKey` (a bug-smell). Post-assert the key is present, so binding the value at the
assert site is observably identical to the spec's later read. `descr` renders the asserted
condition, diagnostic only. -/
def FcMap.getOrAssert {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    {m : Type → Type} [Monad m] [MonadExceptOf StoreTransitionError m]
    (mp : map K V) (k : K) (descr : String) : m V :=
  match FcMap.lookup mp k with
  | some v => pure v
  | none   => throw (StoreTransitionError.assert descr)

end EthCLLib.Spec
