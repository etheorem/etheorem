import EthCLLib.Spec.Arith

/-!
# `EthCLLib.Proofs.Arith`: what `saturatingSub` and `arrayUnion` compute

`saturatingSub` is the spec's `saturating_sub` (`phase0/beacon-chain.md:1038-1042`), a helper
that predates v1.7.0. Beta.4 applies it at every subtraction the spec floors at zero:
`decrease_balance`, `get_previous_epoch`, the inactivity-score updates, the builder balance
sweep. A fork proof about one of those wants to read the stored value back as a number, and
the facts below say what that number is: the truncating `Nat` difference, which never exceeds
the minuend. That is the no-underflow claim, stated once for every caller.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-- `saturatingSub a b` reads back as the truncating `Nat` difference `a.toNat - b.toNat`.
`Nat` subtraction floors at zero exactly where `saturating_sub` does, so one equation covers
both arms, and a bare `UInt64` subtraction, which would wrap near `2 ^ 64`, is excluded. -/
theorem saturatingSub_toNat (a b : UInt64) : (saturatingSub a b).toNat = a.toNat - b.toNat := by
  unfold saturatingSub
  split
  · rename_i h
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)]
  · rename_i h
    have hle : a.toNat ≤ b.toNat := by
      have h' : ¬ b.toNat < a.toNat := fun hlt => h (UInt64.lt_iff_toNat_lt.mpr hlt)
      omega
    simp [Nat.sub_eq_zero_of_le hle]

/-! ## `arrayUnion`

`arrayUnion xs ys` is the dedup-append union: `xs`, then each element of `ys` not already
present. Two facts characterize it under a lawful `BEq`: what it contains, and that it adds no
duplicate to a duplicate-free `xs`. Heze's `get_inclusion_list_transactions` relies on both for
its `list(set(transactions))`. -/

/-- One step of `arrayUnion`'s fold, as a list fact: folding the dedup-push over `l` from `acc`
yields exactly the elements of `acc` and of `l`. -/
private theorem mem_foldl_dedupPush_iff {α : Type} [BEq α] [LawfulBEq α] (x : α) :
    ∀ (l : List α) (acc : Array α),
      x ∈ l.foldl (fun acc i => if acc.contains i then acc else acc.push i) acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc => by simp
  | y :: l, acc => by
    rw [List.foldl_cons, mem_foldl_dedupPush_iff x l]
    cases hy : acc.contains y with
    | true =>
      simp only [↓reduceIte]
      have hmem : y ∈ acc := Array.contains_iff_mem.mp hy
      constructor
      · intro h; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro h; rcases h with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hmem
          · exact Or.inr h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Array.mem_push]
      constructor
      · intro h; rcases h with (h | rfl) | h
        · exact Or.inl h
        · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro h; rcases h with h | h
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr h

/-- What `arrayUnion xs ys` contains: an element of `xs` or of `ys`. -/
theorem mem_arrayUnion_iff {α : Type} [BEq α] [LawfulBEq α] (x : α) (xs ys : Array α) :
    x ∈ arrayUnion xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  unfold arrayUnion
  rw [← Array.foldl_toList, mem_foldl_dedupPush_iff, Array.mem_toList_iff]

/-- The dedup-push fold keeps a duplicate-free accumulator duplicate-free. -/
private theorem nodup_foldl_dedupPush {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (acc : Array α), acc.toList.Nodup →
      (l.foldl (fun acc i => if acc.contains i then acc else acc.push i) acc).toList.Nodup
  | [], acc, h => h
  | y :: l, acc, h => by
    rw [List.foldl_cons]
    apply nodup_foldl_dedupPush l
    cases hy : acc.contains y with
    | true => simp only [↓reduceIte]; exact h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Array.toList_push]
      apply List.nodup_append.mpr
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb; subst hab
      have : acc.contains a = true := Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp ha)
      rw [hy] at this
      exact Bool.false_ne_true this

/-- `arrayUnion` adds no duplicate: from a duplicate-free `xs` (the empty array in the spec
callers) the union is duplicate-free, whatever `ys` repeats. -/
theorem nodup_arrayUnion {α : Type} [BEq α] [LawfulBEq α] (xs ys : Array α)
    (h : xs.toList.Nodup) : (arrayUnion xs ys).toList.Nodup := by
  unfold arrayUnion
  rw [← Array.foldl_toList]
  exact nodup_foldl_dedupPush ys.toList xs h

/-- `saturatingSub a b` never exceeds `a`. -/
theorem saturatingSub_le (a b : UInt64) : saturatingSub a b ≤ a := by
  rw [UInt64.le_iff_toNat_le, saturatingSub_toNat]
  omega

end EthCLLib.Proofs
