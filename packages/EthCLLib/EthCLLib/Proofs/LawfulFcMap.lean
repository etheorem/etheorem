import Std.Data.TreeMap.Lemmas
import Std.Data.HashMap.Lemmas
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLLib.Proofs.LawfulFcMap`: same-key insertion for `FcMap`

`FcMap` is the operation contract. This module adds the two same-key
insertion facts a store postcondition needs: lookup of an inserted key
returns that value, and the inserted key is present.

The class is parameterized by the map family and the key type.
`instLawfulFcMapTreeMap` needs `[Std.TransOrd K]`. `instLawfulFcMapHashMap`
needs `[EquivBEq K]` and `[LawfulHashable K]`.

`contains` and `lookup` are independent `FcMap` fields. The class
records that `contains` agrees with `Option.isSome` of `lookup`. The
public membership theorem follows from that agreement and the lookup
law. The two public insertion theorems carry `@[simp]`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-- Same-key insertion laws for one `FcMap` family at one key type. -/
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

/-- `treeMap` is lawful at keys whose `compare` is a transitive order. -/
instance instLawfulFcMapTreeMap {K : Type}
    [Ord K] [BEq K] [Hashable K] [Std.TransOrd K] :
    LawfulFcMap treeMap K where
  lookup_insert_self m k v := by
    simpa only [FcMap.lookup, FcMap.insert, Std.TreeMap.get?_eq_getElem?] using
      Std.TreeMap.getElem?_insert_self (t := m) (k := k) (v := v)
  contains_eq_isSome_lookup m k := by
    simpa only [FcMap.contains, FcMap.lookup, Std.TreeMap.get?_eq_getElem?] using
      Std.TreeMap.contains_eq_isSome_getElem? (t := m) (a := k)

/-- `hashMap` is lawful at keys whose `BEq` is an equivalence and whose
hash respects that equality. -/
instance instLawfulFcMapHashMap {K : Type}
    [Ord K] [BEq K] [Hashable K] [EquivBEq K] [LawfulHashable K] :
    LawfulFcMap hashMap K where
  lookup_insert_self m k v := by
    simpa only [FcMap.lookup, FcMap.insert, Std.HashMap.get?_eq_getElem?] using
      Std.HashMap.getElem?_insert_self (m := m) (k := k) (v := v)
  contains_eq_isSome_lookup m k := by
    simpa only [FcMap.contains, FcMap.lookup, Std.HashMap.get?_eq_getElem?] using
      Std.HashMap.contains_eq_isSome_getElem? (m := m) (a := k)

example : LawfulFcMap treeMap (Vector UInt8 32) := inferInstance
example : LawfulFcMap hashMap (Vector UInt8 32) := inferInstance

end EthCLLib.Proofs
