import SizzLean.Spec.HashTreeRoot
import SizzLean.Cache.MerkleTree.Build
import SizzLean.Cache.MerkleTree.SetAt
import SizzLean.Proofs.Merkle.Build
import SizzLean.Proofs.Merkle.Chunk
import SizzLean.Proofs.Merkle.OfShape

/-!
# `SizzLean.Proofs.Merkle.Progressive`: the progressive container tree

`Node.ofShape` builds a progressive container as
`mix_in_active_fields` over `Node.ofProgressiveSubtrees`, with the field
sub-trees placed in the progressive shelves. This file proves two facts
about that arm.

1. **Root.** Given field sub-trees that are coherent and root to the
   spec's field roots, the arm roots to `SSZType.hashTreeRoot` and is
   coherent (`ofShape_progressiveContainer_root_coherent`). The progressive
   shapes sit outside `SSZType.BasicSupported`, so `ofShape_root` does not
   cover them; this theorem is the step such an extension consumes.
2. **Path.** The bit path `progressiveFieldBits active k`, which the
   `sszUpdate` elaborator keys a field write with, reaches field `k`'s
   sub-tree (`getAtBits_ofShape_progressiveContainer`). A write at that
   path replaces exactly the field it names.

Lean idiom, annotated once: `Node.ofShape` and `SSZType.hashTreeRoot`
compile by well-founded recursion, so the proofs unfold them through
their equation lemmas (`simp only [Node.ofShape]`). The tree builders in
this file recurse structurally and unfold the same way.
-/

set_option autoImplicit false

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec
open SizzLean.Cache.MerkleTree

/-! ### Placement of the field sub-trees -/

/-- The placed list holds one sub-tree per mask bit. -/
theorem length_placeActiveSubtrees :
    ∀ (active : List Bool) (nodes : List Node),
      (placeActiveSubtrees active nodes).length = active.length
  | [], _ => rfl
  | false :: bits, nodes => by
      simp only [placeActiveSubtrees, List.length_cons, length_placeActiveSubtrees bits nodes]
  | true :: bits, _ :: ns => by
      simp only [placeActiveSubtrees, List.length_cons, length_placeActiveSubtrees bits ns]
  | true :: bits, [] => by
      simp only [placeActiveSubtrees, List.length_cons, length_placeActiveSubtrees bits []]

/-- The placed sub-trees root to the spec's placed chunks. -/
theorem placeActiveSubtrees_roots (H : Type) [Hasher H] :
    ∀ (active : List Bool) (nodes : List Node),
      (placeActiveSubtrees active nodes).map (Node.root H)
        = placeActiveChunks active (nodes.map (Node.root H))
  | [], _ => rfl
  | false :: bits, nodes => by
      simp only [placeActiveSubtrees, placeActiveChunks, List.map_cons, Node.root,
        placeActiveSubtrees_roots H bits nodes]
      rfl
  | true :: bits, n :: ns => by
      simp only [placeActiveSubtrees, placeActiveChunks, List.map_cons,
        placeActiveSubtrees_roots H bits ns]
  | true :: bits, [] => by
      simp only [placeActiveSubtrees, placeActiveChunks, List.map_cons, List.map_nil,
        Node.root, placeActiveSubtrees_roots H bits []]
      rfl

/-- Placement keeps coherence: the gap leaves are coherent, and every
other entry is a supplied sub-tree. -/
theorem placeActiveSubtrees_coherent (H : Type) [Hasher H] :
    ∀ (active : List Bool) (nodes : List Node), (∀ m ∈ nodes, m.Coherent H) →
      ∀ n ∈ placeActiveSubtrees active nodes, n.Coherent H
  | [], _, _, n, hn => by cases hn
  | false :: bits, nodes, hc, n, hn => by
      rw [placeActiveSubtrees] at hn
      cases hn with
      | head => exact Node.Coherent.leaf _
      | tail _ hn => exact placeActiveSubtrees_coherent H bits nodes hc n hn
  | true :: bits, m :: ms, hc, n, hn => by
      rw [placeActiveSubtrees] at hn
      cases hn with
      | head => exact hc m (List.mem_cons_self ..)
      | tail _ hn =>
          exact placeActiveSubtrees_coherent H bits ms
            (fun x hx => hc x (List.mem_cons_of_mem _ hx)) n hn
  | true :: bits, [], hc, n, hn => by
      rw [placeActiveSubtrees] at hn
      cases hn with
      | head => exact Node.Coherent.leaf _
      | tail _ hn => exact placeActiveSubtrees_coherent H bits [] hc n hn

/-- The mask position of field `k` is a mask index. -/
theorem activeChunkPos_lt :
    ∀ (active : List Bool) (k : Nat), k < active.count true →
      activeChunkPos active k < active.length
  | [], _, h => by simp at h
  | false :: bits, k, h => by
      simp only [activeChunkPos, List.length_cons]
      have := activeChunkPos_lt bits k (by simpa using h)
      omega
  | true :: _, 0, _ => by simp [activeChunkPos]
  | true :: bits, k + 1, h => by
      simp only [activeChunkPos, List.length_cons]
      have := activeChunkPos_lt bits k (by simp at h; omega)
      omega

/-- Field `k` lands at its mask position. -/
theorem getElem?_placeActiveSubtrees :
    ∀ (active : List Bool) (nodes : List Node) (k : Nat), k < nodes.length →
      (placeActiveSubtrees active nodes)[activeChunkPos active k]? = nodes[k]?
        ∨ k ≥ active.count true
  | [], _, k, _ => by simp
  | false :: bits, nodes, k, hk => by
      rcases getElem?_placeActiveSubtrees bits nodes k hk with h | h
      · left
        simp only [placeActiveSubtrees, activeChunkPos, List.getElem?_cons_succ, h]
      · right
        simpa using h
  | true :: _, n :: ns, 0, _ => by
      left
      simp [placeActiveSubtrees, activeChunkPos]
  | true :: bits, n :: ns, k + 1, hk => by
      rcases getElem?_placeActiveSubtrees bits ns k (by simp at hk; omega) with h | h
      · left
        simp only [placeActiveSubtrees, activeChunkPos, List.getElem?_cons_succ, h]
      · right
        simp only [List.count_cons, beq_self_eq_true, ite_true]
        omega
  | true :: _, [], k, hk => by simp at hk

/-- The placed chunk list holds one chunk per mask bit. -/
theorem length_placeActiveChunks :
    ∀ (active : List Bool) (roots : List ByteArray),
      (placeActiveChunks active roots).length = active.length
  | [], _ => rfl
  | false :: bits, roots => by
      simp only [placeActiveChunks, List.length_cons, length_placeActiveChunks bits roots]
  | true :: bits, _ :: rs => by
      simp only [placeActiveChunks, List.length_cons, length_placeActiveChunks bits rs]
  | true :: bits, [] => by
      simp only [placeActiveChunks, List.length_cons, length_placeActiveChunks bits []]

/-! ### The progressive shelves -/

/-- One shelf of a non-empty sub-tree list: the equation the proofs
rewrite with. The builder's third arm needs the list to be non-empty,
which a cons supplies. -/
theorem ofProgressiveSubtreesAux_succ_cons (H : Type) [Hasher H]
    (fuel : Nat) (s : Node) (ss : List Node) (w : Nat) :
    Node.ofProgressiveSubtreesAux H (fuel + 1) (s :: ss) w
      = Node.pair (Node.ofSubtrees H ((s :: ss).take (max w 1)) (chunkDepth (max w 1)))
          (Node.ofProgressiveSubtreesAux H fuel ((s :: ss).drop (max w 1)) (max w 1 * 4))
          (some (SizzLean.Hasher.combine (H := H)
            (Node.rootOf H (Node.ofSubtrees H ((s :: ss).take (max w 1))
              (chunkDepth (max w 1))))
            (Node.rootOf H (Node.ofProgressiveSubtreesAux H fuel
              ((s :: ss).drop (max w 1)) (max w 1 * 4))))) := by
  rw [Node.ofProgressiveSubtreesAux]
  exact List.cons_ne_nil _ _

/-- The progressive sub-tree builder roots to the spec's
`merkleize_progressive` over the sub-trees' roots, and it is coherent,
given coherent sub-trees. Induction on the fuel, the same recursion both
sides run. -/
theorem ofProgressiveSubtreesAux_root_coherent (H : Type) [Hasher H] :
    ∀ (fuel : Nat) (subs : List Node) (w : Nat), (∀ s ∈ subs, s.Coherent H) →
      (Node.ofProgressiveSubtreesAux H fuel subs w).root H
          = merkleizeProgressiveAux H fuel (subs.map (Node.root H)) w
        ∧ (Node.ofProgressiveSubtreesAux H fuel subs w).Coherent H := by
  intro fuel
  induction fuel with
  | zero =>
      intro subs w _
      cases subs with
      | nil =>
          simp only [Node.ofProgressiveSubtreesAux, List.map_nil, merkleizeProgressiveAux,
            Node.root]
          exact ⟨rfl, Node.Coherent.leaf _⟩
      | cons s ss =>
          simp only [Node.ofProgressiveSubtreesAux, List.map_cons, merkleizeProgressiveAux,
            Node.root]
          exact ⟨rfl, Node.Coherent.leaf _⟩
  | succ fuel ih =>
      intro subs w hc
      cases subs with
      | nil =>
          simp only [Node.ofProgressiveSubtreesAux, List.map_nil, merkleizeProgressiveAux,
            Node.root]
          exact ⟨rfl, Node.Coherent.leaf _⟩
      | cons s ss =>
          have hL := ofSubtrees_coherent H (chunkDepth (max w 1))
            ((s :: ss).take (max w 1)) (fun x hx => hc x (List.mem_of_mem_take hx))
          obtain ⟨hRroot, hRcoh⟩ := ih ((s :: ss).drop (max w 1)) (max w 1 * 4)
            (fun x hx => hc x (List.mem_of_mem_drop hx))
          have hlen : ((s :: ss).take (max w 1)).length ≤ 2 ^ chunkDepth (max w 1) := by
            rw [List.length_take]
            exact Nat.le_trans (Nat.min_le_left _ _) (le_two_pow_chunkDepth _)
          have espec : merkleizeProgressiveAux H (fuel + 1) ((s :: ss).map (Node.root H)) w
              = SizzLean.Hasher.combine (H := H)
                  (merkleize H (((s :: ss).map (Node.root H)).take (max w 1))
                    (chunkDepth (max w 1)))
                  (merkleizeProgressiveAux H fuel
                    (((s :: ss).map (Node.root H)).drop (max w 1)) (max w 1 * 4)) := by
            rw [List.map_cons, merkleizeProgressiveAux]
            exact List.cons_ne_nil _ _
          rw [ofProgressiveSubtreesAux_succ_cons, rootOf_eq_root hL, rootOf_eq_root hRcoh]
          refine ⟨?_, Node.Coherent.pair_some hL hRcoh⟩
          rw [Node.root, espec, ofSubtrees_root H _ _ hlen, hRroot, List.map_take,
            List.map_drop]

/-! ### Paths into the shelves -/

/-- The `d` low bits of `i`, most significant first, reach sub-tree `i`
of a balanced `ofSubtrees` tree of depth `d`. -/
theorem getAtBits_ofSubtrees (H : Type) [Hasher H] :
    ∀ (d : Nat) (subs : List Node) (i : Nat), i < subs.length → subs.length ≤ 2 ^ d →
      (Node.ofSubtrees H subs d).getAtBits ((List.range d).reverse.map (i.testBit ·))
        = subs[i]? := by
  intro d
  induction d with
  | zero =>
      intro subs i hi hlen
      match subs, i with
      | [s], 0 => simp [Node.ofSubtrees, Node.getAtBits]
      | [], _ => simp at hi
      | [_], _ + 1 => simp at hi
      | _ :: _ :: _, _ => simp at hlen
  | succ d ih =>
      intro subs i hi hlen
      rw [Nat.pow_succ] at hlen
      have hbits : (List.range (d + 1)).reverse.map (i.testBit ·)
          = i.testBit d :: (List.range d).reverse.map (i.testBit ·) := by
        rw [List.range_succ, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.map_cons]
      rw [Node.ofSubtrees, hbits]
      simp only [List.splitAt_eq]
      by_cases hlt : i < 2 ^ d
      · -- Left half: bit `d` of `i` is clear.
        rw [Nat.testBit_lt_two_pow hlt]
        have hL : (subs.take (2 ^ d)).length ≤ 2 ^ d := by
          rw [List.length_take]; exact Nat.min_le_left _ _
        have hiL : i < (subs.take (2 ^ d)).length := by
          rw [List.length_take]; omega
        simp only [Node.getAtBits]
        rw [ih _ i hiL hL, List.getElem?_take, ite_eq_left hlt]
      · -- Right half: `i = 2 ^ d + r` with `r` inside the half.
        obtain ⟨r, rfl⟩ : ∃ r, i = 2 ^ d + r := ⟨i - 2 ^ d, by omega⟩
        have hr : r < 2 ^ d := by omega
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr, Bool.not_false]
        have hne : (subs.drop (2 ^ d)).isEmpty = false := by
          rw [List.isEmpty_eq_false_iff_exists_mem]
          exact ⟨subs[2 ^ d + r], List.mem_drop_iff_getElem.mpr ⟨r, by omega, rfl⟩⟩
        have hR : (subs.drop (2 ^ d)).length ≤ 2 ^ d := by
          rw [List.length_drop]; omega
        have hiR : r < (subs.drop (2 ^ d)).length := by
          rw [List.length_drop]; omega
        have hmap : (List.range d).reverse.map ((2 ^ d + r).testBit ·)
            = (List.range d).reverse.map (r.testBit ·) := by
          apply List.map_congr_left
          intro j hj
          rw [List.mem_reverse, List.mem_range] at hj
          exact Nat.testBit_two_pow_add_gt hj r
        simp only [hne, Bool.false_eq_true, ite_false, Node.getAtBits]
        rw [hmap, ih _ r hiR hR, List.getElem?_drop]

/-- The progressive path reaches chunk `p` of the progressive builder.
The tree's fuel and the path's fuel are separate, and each only has to
cover the shelves that hold `p`. -/
theorem getAtBits_ofProgressiveSubtreesAux (H : Type) [Hasher H] :
    ∀ (fuel fuelB : Nat) (subs : List Node) (w p : Nat),
      p < subs.length → subs.length ≤ fuel → p < fuelB →
      (Node.ofProgressiveSubtreesAux H fuel subs w).getAtBits
          (progressiveChunkBitsAux fuelB p w) = subs[p]? := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ hp hlen _; omega
  | succ fuel ih =>
      intro fuelB subs w p hp hlen hpB
      match fuelB, subs, hpB, hp with
      | fuelB + 1, s :: ss, _, _ =>
          rw [ofProgressiveSubtreesAux_succ_cons, progressiveChunkBitsAux]
          by_cases hlt : p < max w 1
          · rw [ite_eq_left hlt]
            simp only [Node.getAtBits]
            have hL : ((s :: ss).take (max w 1)).length ≤ 2 ^ chunkDepth (max w 1) := by
              rw [List.length_take]
              exact Nat.le_trans (Nat.min_le_left _ _) (le_two_pow_chunkDepth _)
            have hpL : p < ((s :: ss).take (max w 1)).length := by
              rw [List.length_take]; omega
            rw [getAtBits_ofSubtrees H _ _ p hpL hL, List.getElem?_take, ite_eq_left hlt]
          · rw [ite_eq_right hlt]
            simp only [Node.getAtBits]
            have hpR : p - max w 1 < ((s :: ss).drop (max w 1)).length := by
              rw [List.length_drop]; omega
            have hlenR : ((s :: ss).drop (max w 1)).length ≤ fuel := by
              rw [List.length_drop]; omega
            rw [ih fuelB _ (max w 1 * 4) (p - max w 1) hpR hlenR (by omega),
              List.getElem?_drop, Nat.add_sub_cancel' (by omega)]

/-- `progressiveChunkBits p` reaches chunk `p` of
`Node.ofProgressiveSubtrees`. -/
theorem getAtBits_ofProgressiveSubtrees (H : Type) [Hasher H] (subs : List Node) (p : Nat)
    (hp : p < subs.length) :
    (Node.ofProgressiveSubtrees H subs).getAtBits (progressiveChunkBits p) = subs[p]? :=
  getAtBits_ofProgressiveSubtreesAux H subs.length (p + 1) subs 1 p hp (Nat.le_refl _)
    (Nat.lt_succ_self p)

/-! ### The `ofShape` arm -/

/-- The progressive container arm roots to the spec's `hashTreeRoot` and
is coherent, given field sub-trees that are coherent and root to the
spec's field roots. -/
theorem ofShape_progressiveContainer_root_coherent (H : Type) [Hasher H]
    (active : List Bool) (fs : List SSZType)
    (vs : (SSZType.progressiveContainer active fs).interp)
    (hc : ∀ n ∈ Node.subtreesForFields H fs vs, n.Coherent H)
    (hr : (Node.subtreesForFields H fs vs).map (Node.root H)
      = SSZType.hashTreeRootFields H fs vs) :
    (Node.ofShape H (.progressiveContainer active fs) vs).root H
        = SSZType.hashTreeRoot H (.progressiveContainer active fs) vs
      ∧ (Node.ofShape H (.progressiveContainer active fs) vs).Coherent H := by
  simp only [Node.ofShape, SSZType.hashTreeRoot]
  obtain ⟨hbody, hbodyc⟩ := ofProgressiveSubtreesAux_root_coherent H
    (placeActiveSubtrees active (Node.subtreesForFields H fs vs)).length
    (placeActiveSubtrees active (Node.subtreesForFields H fs vs)) 1
    (placeActiveSubtrees_coherent H active _ hc)
  have e : Node.mixInActiveFields H
      (Node.ofProgressiveSubtrees H (placeActiveSubtrees active (Node.subtreesForFields H fs vs)))
      active
      = Node.pair
          (Node.ofProgressiveSubtrees H
            (placeActiveSubtrees active (Node.subtreesForFields H fs vs)))
          (Node.leaf (padToChunk (packBitsLE active)))
          (some (SizzLean.Hasher.combine (H := H)
            (Node.rootOf H (Node.ofProgressiveSubtrees H
              (placeActiveSubtrees active (Node.subtreesForFields H fs vs))))
            (Node.rootOf H (Node.leaf (padToChunk (packBitsLE active)))))) := rfl
  rw [e, Node.ofProgressiveSubtrees, rootOf_eq_root hbodyc,
    rootOf_eq_root (Node.Coherent.leaf _)]
  refine ⟨?_, Node.Coherent.pair_some hbodyc (Node.Coherent.leaf _)⟩
  simp only [Node.root]
  rw [hbody, placeActiveSubtrees_roots, hr, length_placeActiveSubtrees]
  simp only [merkleizeProgressive, mixInActiveFields, length_placeActiveChunks]

/-- The `sszUpdate` path of field `k` reaches field `k`'s sub-tree in the
progressive container tree. The mask has a `true` bit for every field,
which the deriving handler's `progressiveMask` guarantees. -/
theorem getAtBits_ofShape_progressiveContainer (H : Type) [Hasher H]
    (active : List Bool) (fs : List SSZType)
    (vs : (SSZType.progressiveContainer active fs).interp)
    (k : Nat) (hk : k < fs.length) (hmask : fs.length ≤ active.count true) :
    (Node.ofShape H (.progressiveContainer active fs) vs).getAtBits
        (progressiveFieldBits active k)
      = (Node.subtreesForFields H fs vs)[k]? := by
  have hkn : k < (Node.subtreesForFields H fs vs).length := by
    rw [length_subtreesForFields]; exact hk
  have hpos : activeChunkPos active k
      < (placeActiveSubtrees active (Node.subtreesForFields H fs vs)).length := by
    rw [length_placeActiveSubtrees]; exact activeChunkPos_lt active k (by omega)
  simp only [Node.ofShape, Node.mixInActiveFields, progressiveFieldBits, Node.getAtBits]
  rw [getAtBits_ofProgressiveSubtrees H _ _ hpos]
  rcases getElem?_placeActiveSubtrees active (Node.subtreesForFields H fs vs) k hkn with h | h
  · exact h
  · omega

end SizzLean.Proofs.Merkle
