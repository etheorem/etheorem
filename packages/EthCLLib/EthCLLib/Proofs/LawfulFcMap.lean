import EthCLLib.Spec.FiniteMap

/-!
# `EthCLLib.Proofs.LawfulFcMap`: same-key insertion for `FcMap`

`FcMap` is the operation contract. This module adds the two same-key
insertion facts a store postcondition needs: lookup of an inserted key
returns that value, and the inserted key is present.

The class is parameterized by the map family and the key type. Concrete
`treeMap` and `hashMap` instances are separate: each key type carries its
own `TransOrd` or `EquivBEq` / `LawfulHashable` obligations.

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

end EthCLLib.Proofs
