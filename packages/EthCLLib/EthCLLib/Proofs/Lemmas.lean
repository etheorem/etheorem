/-!
# `EthCLLib.Proofs.Lemmas`: list and `UInt64` lemmas that core Lean lacks

Core Lean `4.29.1` has no form of `Nodup.map` that needs injectivity only on
the list. It also has no "same members" form of `Perm` for duplicate-free lists.
It has no membership congruence for `flatMap`, and no rule that puts an entry of a
duplicate-free `flatMap` in one block. Its `UInt64.ofNat` round-trip
states the bound as `UInt64.size`, which `omega` does not read. The theorems here
supply these forms for the proof modules beside this one.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

/-- A map that is injective on a duplicate-free list keeps it duplicate-free. -/
theorem nodup_map_of_injOn {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hl.2 fun x hx y hy => hf x (.tail _ hx) y (.tail _ hy)⟩
    rintro ⟨b, hb, hfb⟩
    exact hl.1 (hf b (.tail _ hb) a (.head _) hfb ▸ hb)

/-- Two duplicate-free lists with the same members are permutations. -/
theorem perm_of_nodup_of_mem_iff {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ :=
  List.perm_iff_count.mpr fun a => by rw [h₁.count, h₂.count]; simp only [h a]

/-- `flatMap` over a list reads its function only at the list's members. -/
theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (.head _), ih fun x hx => h x (.tail _ hx)]

/-- An entry of a duplicate-free `flatMap` sits in one block: when `x` is in the blocks of
`a` and of `b`, then `a = b`. -/
theorem flatMap_nodup_block_eq {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup →
      ∀ {a b : α} {x : β}, a ∈ l → b ∈ l → x ∈ f a → x ∈ f b → a = b
  | [], _, _, _, _, ha, _, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, x, ha, hb, hxa, hxb => by
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, hl, hdis⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd rfl (hdis x hxa x (List.mem_flatMap.mpr ⟨b, hb', hxb⟩))
    · exact absurd rfl (hdis x hxb x (List.mem_flatMap.mpr ⟨a, ha', hxa⟩))
    · exact flatMap_nodup_block_eq hl ha' hb' hxa hxb

/-- `UInt64.ofNat` round-trips below `2 ^ 64`. Core states the bound as
`UInt64.size`. `omega` can discharge the `2 ^ 64` form. -/
theorem toNat_ofNat_lt64 {m : Nat} (h : m < 2 ^ 64) : (UInt64.ofNat m).toNat = m :=
  UInt64.toNat_ofNat_of_lt' h

end EthCLLib.Proofs
