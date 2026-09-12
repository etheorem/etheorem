import EthCLLib.Proofs.MerkleOpening
import SizzLean.Proofs.Merkleize
import SizzLean.Proofs.ShapeAgreement

/-!
# `EthCLLib.Proofs.MerkleShape`: reading a position out of a built tree

Where `MerkleOpening.lean` says a path exists, this module says what the path
reaches. `nodeAt_ofSubtrees` reads position `k` of an `ofSubtrees` tree back as
sub-tree `k % 2 ^ depth`. `nodeAt_ofShape_container` specialises that to a
container, whose depth makes the residue collapse.

Both results quantify over `nodeAt`, so they sit framework-side with the rest of
the path vocabulary. SizzLean supplies the tree builders and their shape facts,
and states nothing about paths into them.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open SizzLean SizzLean.Hasher SizzLean.Cache.MerkleTree SizzLean.Spec
open EthCLLib.Spec

/-! ### Reading a position out of an `ofSubtrees` tree

`nodeAt` routes on bit `d` of the index and passes the index **unchanged** into
the chosen child, re-reading the next bit one level down. `ofSubtrees` splits its
list at `2 ^ d`, so the right child's position is `k - 2 ^ d`. The two only line
up modulo `2 ^ depth`.

The statement below therefore indexes at `k % 2 ^ depth`, and not at `k` under a
`k < subs.length` hypothesis. Under that hypothesis the right branch's induction
hypothesis would need `k < 2 ^ d`, which is false exactly there. -/

/-- `routeRight` reads bit `d`. -/
private theorem routeRight_true_iff (k d : Nat) :
    routeRight k d = true ↔ k / 2 ^ d % 2 = 1 := by
  simp [routeRight, Nat.shiftRight_eq_div_pow]

/-- Splitting a residue at the top bit. Stated additively so `omega` can finish
each of the two branches below, treating `2 ^ d` and the residues as atoms. -/
private theorem mod_two_pow_succ (k d : Nat) :
    k % 2 ^ (d + 1) = 2 ^ d * (k / 2 ^ d % 2) + k % 2 ^ d := by
  have h1 : k % 2 ^ (d + 1) / 2 ^ d = k / 2 ^ d % 2 := by
    rw [Nat.pow_succ]
    exact Nat.mod_mul_right_div_self k (2 ^ d) 2
  have h2 : k % 2 ^ (d + 1) % 2 ^ d = k % 2 ^ d :=
    Nat.mod_mod_of_dvd k ⟨2, by rw [Nat.pow_succ]⟩
  have h3 := Nat.div_add_mod (k % 2 ^ (d + 1)) (2 ^ d)
  rw [h1, h2] at h3
  omega

private theorem mod_two_pow_succ_of_false {k d : Nat} (h : routeRight k d = false) :
    k % 2 ^ (d + 1) = k % 2 ^ d := by
  have hne : k / 2 ^ d % 2 ≠ 1 := by
    intro hc
    rw [(routeRight_true_iff k d).mpr hc] at h
    exact Bool.noConfusion h
  have hlt : k / 2 ^ d % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [mod_two_pow_succ, show k / 2 ^ d % 2 = 0 by omega]
  omega

private theorem mod_two_pow_succ_of_true {k d : Nat} (h : routeRight k d = true) :
    k % 2 ^ (d + 1) = 2 ^ d + k % 2 ^ d := by
  rw [mod_two_pow_succ, (routeRight_true_iff k d).mp h]
  omega

/-- **Position `k` of an `ofSubtrees` tree is sub-tree `k % 2 ^ depth`.**

The out-of-range `zeroLeaf` pad never appears. The hypothesis says something
occupies the position. In the right branch that reads
`2 ^ d + k % 2 ^ d < subs.length`, which forces the dropped half to be
non-empty. The pad's depth varies with the descent, and this proof never has to
name it. -/
theorem nodeAt_ofSubtrees (H : Type) [Hasher H] :
    ∀ (depth : Nat) (subs : List Node) (k : Nat) (hk : k % 2 ^ depth < subs.length),
      nodeAt (Node.ofSubtrees H subs depth) depth k = subs[k % 2 ^ depth] := by
  intro depth
  induction depth with
  | zero =>
      -- `hk` is the very proof the goal's `getElem` carries, so it must not be
      -- rewritten in place. Everything goes through `simp`, which copes with the
      -- dependency.
      intro subs k hk
      rw [nodeAt_zero]
      cases subs with
      | nil      => simp at hk
      | cons s _ => simp [Node.ofSubtrees, Nat.mod_one]
  | succ d ih =>
      intro subs k hk
      have hmodlt : k % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
      rw [ofSubtrees_succ]
      simp only [nodeAt]
      cases hbit : routeRight k d with
      | false =>
          have hmod := mod_two_pow_succ_of_false hbit
          have hklt : k % 2 ^ d < subs.length := by rw [← hmod]; exact hk
          simp only [Bool.false_eq_true, if_false]
          have hk' : k % 2 ^ d < (subs.take (2 ^ d)).length := by
            rw [List.length_take]; omega
          rw [ih (subs.take (2 ^ d)) k hk']
          simp [hmod]
      | true =>
          have hmod := mod_two_pow_succ_of_true hbit
          have hklt : 2 ^ d + k % 2 ^ d < subs.length := by rw [← hmod]; exact hk
          have hne : ¬ (subs.drop (2 ^ d)).isEmpty = true := by
            simp only [List.isEmpty_iff, List.drop_eq_nil_iff]
            omega
          simp only [if_true, if_neg hne]
          have hk' : k % 2 ^ d < (subs.drop (2 ^ d)).length := by
            rw [List.length_drop]; omega
          rw [ih (subs.drop (2 ^ d)) k hk']
          simp [hmod]

/-! ### Reading a container's field sub-tree

`nodeAt_ofSubtrees` indexes modulo `2 ^ depth`. At a container the depth is
`chunkDepth fs.length`, and `chunkDepth` is `⌈log₂⌉`. The tree is therefore at
least as wide as the field list, and the residue collapses. -/

/-- Sub-tree `k` of a container is field `k`'s own `ofShape` tree. Induction on
`fs` and `k` together, matching `fieldAt`'s recursion exactly. -/
private theorem subtreesForFields_getElem (H : Type) [Hasher H] :
    ∀ (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length),
      (Node.subtreesForFields H fs vs)[k]'(by
        rw [subtreesForFields_length]; exact hk)
        = Node.ofShape H (fs[k]) (SSZType.fieldAt fs vs k hk)
  | _ :: _,  _,  0,     _  => by
      simp [Node.subtreesForFields, SSZType.fieldAt]
  | _ :: ts, vs, k + 1, hk => by
      have hk' : k < ts.length := by simp only [List.length_cons] at hk; omega
      simp only [Node.subtreesForFields, List.getElem_cons_succ, SSZType.fieldAt]
      exact subtreesForFields_getElem H ts vs.2 k hk'

/-- The field-`k` sub-tree of a container tree is the field value's own `ofShape`
tree. `GeneralizedIndexBranch.lean`'s two-step witness discharges its `hsub`
through this. -/
theorem nodeAt_ofShape_container (H : Type) [Hasher H]
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length) :
    nodeAt (Node.ofShape H (.container fs) vs) (chunkDepth fs.length) k
      = Node.ofShape H (fs[k]) (SSZType.fieldAt fs vs k hk) := by
  have hmod : k % 2 ^ chunkDepth fs.length = k :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hk (le_two_pow_chunkDepth fs.length))
  have hk'' : k % 2 ^ chunkDepth fs.length < (Node.subtreesForFields H fs vs).length := by
    rw [hmod, subtreesForFields_length]; exact hk
  simp only [Node.ofShape]
  rw [nodeAt_ofSubtrees H (chunkDepth fs.length) (Node.subtreesForFields H fs vs) k hk'']
  simp only [hmod]
  exact subtreesForFields_getElem H fs vs k hk

end EthCLLib.Proofs
