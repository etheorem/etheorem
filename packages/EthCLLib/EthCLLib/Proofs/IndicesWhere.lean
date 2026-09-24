import EthCLLib.Spec.Arith
import EthCLLib.Proofs.Lemmas

/-!
# `EthCLLib.Proofs.IndicesWhere`: `indicesWhere` returns distinct indices

`EthCLLib.Spec.indicesWhere` (`EthCLLib/Spec/Arith.lean:195-199`) is the loop
behind `get_active_validator_indices` and its sibling walks. It walks
`0 … size-1` and pushes each index that passes the predicate.
`indicesWhere_toList` states the loop as a filter over `List.range`, followed by
`UInt64.ofNat`. `indicesWhere_nodup` follows. The kept indices are distinct, and
below `2 ^ 64` the cast keeps them distinct.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-- The loop over a list, from an arbitrary starting array. This is the form
`simp` leaves once the range loop becomes a list loop. -/
private theorem forIn_push_filter {α : Type} [Inhabited α] (xs : Array α)
    (p : α → Nat → Bool) (l : List Nat) (acc : Array UInt64) :
    (forIn (m := Id) l acc fun i r =>
        if p xs[i]! i = true then pure (ForInStep.yield (r.push (UInt64.ofNat i)))
        else pure (ForInStep.yield r)).toList =
      acc.toList ++ (l.filter (fun i => p xs[i]! i)).map UInt64.ofNat := by
  induction l generalizing acc with
  | nil =>
    -- In `Id` the empty loop is `acc`, and the filter of `[]` is `[]`, so both
    -- sides reduce to `acc.toList` up to `++ []`.
    exact (List.append_nil _).symm
  | cons i l ih =>
    by_cases h : p xs[i]! i = true <;> simp [List.forIn_cons, h, ih]

/-- `indicesWhere` is a filter over `List.range xs.size`, cast to `UInt64`. -/
theorem indicesWhere_toList {α : Type} [Inhabited α] (xs : Array α)
    (p : α → Nat → Bool) :
    (indicesWhere xs p).toList =
      ((List.range xs.size).filter (fun i => p xs[i]! i)).map UInt64.ofNat := by
  -- `for i in [0 : n]` over `Id` is a left fold over `List.range' 0 n`.
  simp only [indicesWhere, Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [← List.range_eq_range'] at *
  simpa using forIn_push_filter xs p (List.range xs.size) #[]

/-- `indicesWhere` returns at most one index per entry of `xs`. -/
theorem indicesWhere_size_le {α : Type} [Inhabited α] (xs : Array α)
    (p : α → Nat → Bool) : (indicesWhere xs p).size ≤ xs.size := by
  have h := congrArg List.length (indicesWhere_toList xs p)
  simp only [Array.length_toList, List.length_map] at h
  rw [h]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The indices `indicesWhere` returns are distinct, for an array below `2 ^ 64`
entries. -/
theorem indicesWhere_nodup {α : Type} [Inhabited α] (xs : Array α)
    (p : α → Nat → Bool) (h64 : xs.size ≤ 2 ^ 64) :
    (indicesWhere xs p).toList.Nodup := by
  rw [indicesWhere_toList]
  refine nodup_map_of_injOn (List.nodup_range.filter _) ?_
  intro a ha b hb hab
  have ha' : a < 2 ^ 64 := by
    have := List.mem_range.mp (List.mem_filter.mp ha).1; omega
  have hb' : b < 2 ^ 64 := by
    have := List.mem_range.mp (List.mem_filter.mp hb).1; omega
  have := congrArg UInt64.toNat hab
  rwa [toNat_ofNat_lt64 ha', toNat_ofNat_lt64 hb'] at this

end EthCLLib.Proofs
