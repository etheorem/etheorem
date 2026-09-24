import Std.Data.TreeMap.Lemmas
import Std.Data.HashMap.Lemmas
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLLib.Proofs.LawfulFcMap`: the laws of a fork-choice map

`FcMap` names the operations of a fork-choice map. It states no law about them. A
proof about the store needs the laws. For example, a lookup after an insert at the
same key returns the inserted value. `LawfulFcMap` states six laws:

- `lookup_insert_self`: a lookup at the inserted key returns the inserted value;
- `contains_eq_isSome_lookup`: `contains` agrees with `Option.isSome` of `lookup`;
- `lookup_empty`: the empty map has no entries;
- `lookup_insert_ne`: an insert does not change a lookup at a different key;
- `mem_fold_push`: a fold that pushes each entry lists exactly the entries;
- `mem_keys`: `keys` lists exactly the keys with an entry.

The class is parameterized by the map family and the key type. The `treeMap`
instance needs a transitive order with lawful equality on the key
(`[Std.TransOrd K] [Std.LawfulEqOrd K]`). The `hashMap` instance needs a lawful `==`
and a hash that respects it (`[LawfulBEq K] [LawfulHashable K]`). `lookup_insert_ne`
and the two enumeration laws are the reason for the lawful-equality binders: they
turn "the keys compare equal" into `k = k'`.

For `Root` (`Vector UInt8 32`), the order laws `instTransOrdVectorUInt8` and
`instLawfulEqOrdVectorUInt8` sit beside `instOrdVectorUInt8` in
`EthCLLib/Spec/FiniteMap.lean`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-- The laws of one `FcMap` family at one key type. -/
class LawfulFcMap (map : MapKind) (K : Type)
    [Ord K] [BEq K] [Hashable K] [FcMap map] : Prop where
  /-- Lookup of a key just inserted at that key returns the inserted value. -/
  lookup_insert_self :
    ∀ {V : Type} (m : map K V) (k : K) (v : V),
      FcMap.lookup (FcMap.insert m k v) k = some v
  /-- Membership is `Option.isSome` of lookup. -/
  contains_eq_isSome_lookup :
    ∀ {V : Type} (m : map K V) (k : K),
      FcMap.contains m k = (FcMap.lookup m k).isSome
  /-- The empty map has no entries. -/
  lookup_empty :
    ∀ {V : Type} (k : K), FcMap.lookup (FcMap.empty : map K V) k = none
  /-- An insert does not change a lookup at a different key. -/
  lookup_insert_ne :
    ∀ {V : Type} (m : map K V) (k k' : K) (v : V),
      k ≠ k' → FcMap.lookup (FcMap.insert m k v) k' = FcMap.lookup m k'
  /-- A fold that pushes each entry lists exactly the entries of the map. -/
  mem_fold_push :
    ∀ {V : Type} (m : map K V) (k : K) (v : V),
      (k, v) ∈ (FcMap.fold (fun (acc : Array (K × V)) k v => acc.push (k, v)) #[] m).toList
        ↔ FcMap.lookup m k = some v
  /-- `keys` lists exactly the keys with an entry. -/
  mem_keys :
    ∀ {V : Type} (m : map K V) (k : K),
      k ∈ FcMap.keys m ↔ (FcMap.lookup m k).isSome

/-- Lookup of a key just inserted at that key returns the inserted value. -/
@[simp] theorem FcMap.lookup_insert_self
    {map : MapKind} {K : Type}
    [Ord K] [BEq K] [Hashable K] [FcMap map] [LawfulFcMap map K]
    {V : Type} (m : map K V) (k : K) (v : V) :
    FcMap.lookup (FcMap.insert m k v) k = some v :=
  LawfulFcMap.lookup_insert_self m k v

/-- An inserted key is present in the resulting map. -/
@[simp] theorem FcMap.contains_insert_self
    {map : MapKind} {K : Type}
    [Ord K] [BEq K] [Hashable K] [FcMap map] [LawfulFcMap map K]
    {V : Type} (m : map K V) (k : K) (v : V) :
    FcMap.contains (FcMap.insert m k v) k = true := by
  rw [LawfulFcMap.contains_eq_isSome_lookup, FcMap.lookup_insert_self]
  rfl

/-- A value is in `FcMap.values` exactly when some key maps to it. -/
theorem FcMap.mem_values
    {map : MapKind} {K : Type}
    [Ord K] [BEq K] [Hashable K] [FcMap map] [LawfulFcMap map K]
    {V : Type} (m : map K V) (v : V) :
    v ∈ FcMap.values m ↔ ∃ k, FcMap.lookup m k = some v := by
  unfold FcMap.values
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp h
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact List.mem_filterMap.mpr ⟨k, (LawfulFcMap.mem_keys m k).mpr (by simp [hk]), hk⟩

/-- `treeMap` is lawful at keys whose `compare` is a transitive order that returns
`.eq` only on equal keys. -/
instance instLawfulFcMapTreeMap {K : Type}
    [Ord K] [BEq K] [Hashable K] [Std.TransOrd K] [Std.LawfulEqOrd K] :
    LawfulFcMap treeMap K where
  lookup_insert_self _ _ _ := Std.TreeMap.getElem?_insert_self
  contains_eq_isSome_lookup _ _ := Std.TreeMap.isSome_getElem?_eq_contains.symm
  lookup_empty _ := Std.TreeMap.getElem?_emptyc
  lookup_insert_ne m k k' v hne := by
    show (m.insert k v).get? k' = m.get? k'
    simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
    rw [if_neg (fun h => hne (Std.LawfulEqCmp.eq_of_compare h))]
  mem_fold_push m k v := by
    show (k, v) ∈ (m.foldl _ #[]).toList ↔ m.get? k = some v
    -- `simp` turns the fold of pushes over `toList` into `toList` itself.
    rw [Std.TreeMap.foldl_eq_foldl_toList]
    simp
  mem_keys m k := by
    show k ∈ m.keys ↔ (m.get? k).isSome
    rw [Std.TreeMap.mem_keys, Std.TreeMap.mem_iff_contains,
      ← Std.TreeMap.isSome_getElem?_eq_contains]
    rfl

/-- `hashMap` is lawful at keys whose `==` is equality and whose hash respects it. -/
instance instLawfulFcMapHashMap {K : Type}
    [Ord K] [BEq K] [Hashable K] [LawfulBEq K] [LawfulHashable K] :
    LawfulFcMap hashMap K where
  lookup_insert_self _ _ _ := Std.HashMap.getElem?_insert_self
  contains_eq_isSome_lookup _ _ := Std.HashMap.isSome_getElem?_eq_contains.symm
  lookup_empty _ := Std.HashMap.getElem?_empty
  lookup_insert_ne m k k' v hne := by
    show (m.insert k v).get? k' = m.get? k'
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rw [if_neg (by simpa using hne)]
  mem_fold_push m k v := by
    show (k, v) ∈ (m.fold _ #[]).toList ↔ m.get? k = some v
    -- `simp` turns the fold of pushes over `toList` into `toList` itself.
    rw [Std.HashMap.fold_eq_foldl_toList]
    simp
  mem_keys m k := by
    show k ∈ m.keys ↔ (m.get? k).isSome
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains,
      ← Std.HashMap.isSome_getElem?_eq_contains]
    rfl

example : LawfulFcMap treeMap (Vector UInt8 32) := inferInstance
example : LawfulFcMap hashMap (Vector UInt8 32) := inferInstance

end EthCLLib.Proofs
