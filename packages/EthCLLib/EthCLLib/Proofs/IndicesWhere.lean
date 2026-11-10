import EthCLLib.Spec.Arith

/-!
# `EthCLLib.Proofs.IndicesWhere`: what the index filter returns

`indicesWhere xs p` walks `[0, xs.size)` and keeps each index `i` whose element satisfies
`p xs[i] i`, as a `uint64`. The spec's registry filters (`get_active_validator_indices`,
`get_eligible_validator_indices`) are this walk over the validator list. Two facts read it:

* `mem_indicesWhere`: every index it returns is in range and satisfies `p`, so a read at that
  index cannot fail.
* `indicesWhere_size_pos`: an element that satisfies `p` makes the result nonempty, so a
  sampler over it never sees an empty candidate list.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (indicesWhere)

/-- The walk of `indicesWhere` over a list of positions, from an accumulator `out`: every index it
adds is a position of the list that satisfies `p`; it adds one when some position does; and it
never drops an element of `out`. -/
private theorem indicesWhere_walk {α : Type} [Inhabited α] (xs : Array α) (p : α → Nat → Bool) :
    ∀ (l : List Nat) (out : Array UInt64),
      (∀ y ∈ (Id.run (forIn l out fun i (r : Array UInt64) =>
          if p xs[i]! i = true then pure (ForInStep.yield (r.push (UInt64.ofNat i)))
          else pure (ForInStep.yield r)) : Array UInt64),
        y ∈ out ∨ ∃ i ∈ l, y = UInt64.ofNat i ∧ p xs[i]! i = true) ∧
      ((∃ i ∈ l, p xs[i]! i = true) →
        0 < (Id.run (forIn l out fun i (r : Array UInt64) =>
          if p xs[i]! i = true then pure (ForInStep.yield (r.push (UInt64.ofNat i)))
          else pure (ForInStep.yield r)) : Array UInt64).size) ∧
      out.size ≤ (Id.run (forIn l out fun i (r : Array UInt64) =>
          if p xs[i]! i = true then pure (ForInStep.yield (r.push (UInt64.ofNat i)))
          else pure (ForInStep.yield r)) : Array UInt64).size := by
  intro l
  induction l with
  | nil =>
    intro out
    simp only [List.forIn_nil]
    refine ⟨fun y hy => Or.inl hy, fun h => ?_, Nat.le_refl _⟩
    obtain ⟨_, hi, _⟩ := h
    nomatch hi
  | cons i rest ih =>
    intro out
    by_cases hp : p xs[i]! i = true
    · simp only [List.forIn_cons, hp, ↓reduceIte, pure_bind]
      obtain ⟨hmem, hpos, hsize⟩ := ih (out.push (UInt64.ofNat i))
      refine ⟨fun y hy => ?_, fun _ => ?_, ?_⟩
      · rcases hmem y hy with hy' | ⟨j, hj, hyj⟩
        · rcases Array.mem_push.mp hy' with hy'' | rfl
          · exact Or.inl hy''
          · exact Or.inr ⟨i, List.mem_cons_self, rfl, hp⟩
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hyj⟩
      · have := hsize
        simp only [Array.size_push] at this
        exact Nat.lt_of_lt_of_le (Nat.succ_pos _) this
      · have := hsize
        simp only [Array.size_push] at this
        omega
    · simp only [List.forIn_cons, hp, Bool.false_eq_true, ↓reduceIte, pure_bind]
      obtain ⟨hmem, hpos, hsize⟩ := ih out
      refine ⟨fun y hy => ?_, fun ⟨j, hj, hpj⟩ => ?_, hsize⟩
      · rcases hmem y hy with hy' | ⟨j, hj, hyj⟩
        · exact Or.inl hy'
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hyj⟩
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact absurd hpj hp
        · exact hpos ⟨j, hj, hpj⟩

/-- `indicesWhere` as the walk over `List.range' 0 xs.size`. -/
private theorem indicesWhere_eq {α : Type} [Inhabited α] (xs : Array α) (p : α → Nat → Bool) :
    indicesWhere xs p = Id.run (forIn (List.range' 0 xs.size) #[] fun i (r : Array UInt64) =>
      if p xs[i]! i = true then pure (ForInStep.yield (r.push (UInt64.ofNat i)))
      else pure (ForInStep.yield r)) := by
  unfold indicesWhere
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

/-- Every index `indicesWhere` returns is a position of `xs` whose element satisfies `p`. -/
theorem mem_indicesWhere {α : Type} [Inhabited α] {xs : Array α} {p : α → Nat → Bool}
    {y : UInt64} (hy : y ∈ indicesWhere xs p) :
    ∃ i, i < xs.size ∧ y = UInt64.ofNat i ∧ p xs[i]! i = true := by
  rw [indicesWhere_eq] at hy
  rcases (indicesWhere_walk xs p _ #[]).1 y hy with h | ⟨i, hi, hyi, hpi⟩
  · exact absurd h (by simp)
  · exact ⟨i, by simpa using (List.mem_range'_1.mp hi).2, hyi, hpi⟩

/-- A position whose element satisfies `p` makes `indicesWhere` nonempty. -/
theorem indicesWhere_size_pos {α : Type} [Inhabited α] {xs : Array α} {p : α → Nat → Bool}
    (h : ∃ i, i < xs.size ∧ p xs[i]! i = true) : 0 < (indicesWhere xs p).size := by
  rw [indicesWhere_eq]
  obtain ⟨i, hi, hpi⟩ := h
  exact (indicesWhere_walk xs p _ #[]).2.1 ⟨i, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, hpi⟩

end EthCLLib.Proofs
