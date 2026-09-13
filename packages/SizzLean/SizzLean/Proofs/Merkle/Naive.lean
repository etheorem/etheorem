import SizzLean.Spec.HashTreeRoot

/-!
# `SizzLean.Proofs.Merkle.Naive`: the naive depth-first Merkle tree

The spec's merkleizer (`SizzLean.Spec.merkleize`) folds
breadth-first, pairing the chunk list level by level and padding an
odd tail with the zero tower at the *current level*
(`zeroHashAt H lvl`). The textbook fold is depth-first: split the
leaf list at the midpoint, recurse into the halves. This file
defines the depth-first reference (`naiveRootAt`, `naiveRoot`) and
proves the two folds agree,

    merkleize H chunks depth = naiveRoot H chunks depth

whenever `chunks.length ≤ 2 ^ depth`. That equation is the
reference step every merkleization row in the ledger reduces to.
The spec's overflow arm (levels exhausted with more than one chunk
left) sits outside the hypothesis, and `chunkDepth` of the type's
own cap always satisfies the bound, which `Proofs/Merkle/Chunk.lean`
proves.

## The level-aware naive tree

`naiveRootAt H cs lvl remaining` reads: `cs` are the leaf values of
a tree whose leaves sit `lvl` levels above the chunk level, and
`remaining` levels are still to build. An *empty* subtree at
`(lvl, remaining)` misses `2 ^ remaining` leaves, each a zero
subtree of depth `lvl`, so its root is `zeroHashAt H (lvl +
remaining)`. The spec's `merkleizeAt` answers
`zeroHashAt H remaining` for an empty list, which agrees at
`lvl = 0` where `merkleize` starts; at `lvl > 0` the empty arm
never fires on either side (pairing never empties a non-empty
list), so the main theorem carries `chunks ≠ []` and works at
level 0.

The induction needs one bridge, `naiveRootAt_eq_pairLayer`: one
depth-first midpoint split equals one breadth-first pairing step.
Its proof is an induction on `remaining` over the tree shapes: the
two-element core `naiveRootAt_two`, the one-element promotion step
`naiveRootAt_one`, and the list bookkeeping in `pairLayer_take` /
`pairLayer_drop`, the latter needing the even boundary
`2 * k ≤ cs.length` (an odd tail pairs with a zero, so pairing does
not distribute past an odd cut). `naiveRootAt_one` itself is the
promote lemma `promoteThroughZeros_eq_naiveRootAt` read sideways:
a singleton's split puts the empty half, the built-from-leaves
tower, on the right.

## What the reference borrows

Nothing. `naiveZero` builds the zero subtrees from bare `zero32`
leaves, `naiveRootAt` pads only with `naiveZero`, and the tower
agreement (`naiveZero_eq_zeroHashAt`, `naiveRootAt_nil`) is proved
here. The spec's `zeroHashAt` and `promoteThroughZeros` are
what the theorems transfer the reference TO.

Lean idiom, annotated once: every `Hasher.combine` here takes the
explicit `(H := H)`. `Hasher`'s parameter is a phantom tag the
method's types do not mention, so instance synthesis cannot recover
it from the value arguments.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Spec

/-! ### The breadth-first pairing layer, as a plain recursion -/

/-- One pairing layer at level `lvl`, the natural (non-tail)
spelling: adjacent chunks combine pairwise, an odd tail pairs with
`zeroHashAt H lvl`. `Spec.combineLayerAt` computes the same list in
accumulator form; `combineLayerAt_eq_pairLayer` says so. -/
def pairLayer (H : Type) [Hasher H] (lvl : Nat) :
    List ByteArray → List ByteArray
  | []           => []
  | [x]          => [Hasher.combine (H := H) x (zeroHashAt H lvl)]
  | x :: y :: rs => Hasher.combine (H := H) x y :: pairLayer H lvl rs

/-- The accumulator form computes the same layer. Length induction,
because `pairLayer`'s recursion skips one cons. -/
theorem combineLayerAtAux_eq_pairLayer (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (n : Nat) (cs : List ByteArray), cs.length ≤ n →
      ∀ acc : List ByteArray,
        Spec.combineLayerAtAux H lvl cs acc = acc.reverse ++ pairLayer H lvl cs := by
  intro n
  induction n with
  | zero =>
      intro cs hcs acc
      match cs, hcs with
      | [], _ => simp [Spec.combineLayerAtAux, pairLayer]
  | succ n ih =>
      intro cs hcs acc
      cases cs with
      | nil => simp [Spec.combineLayerAtAux, pairLayer]
      | cons x cs' =>
          cases cs' with
          | nil =>
              simp only [Spec.combineLayerAtAux, pairLayer, List.reverse_cons]
          | cons y rs =>
              have hrs : rs.length ≤ n := by
                simp only [List.length_cons] at hcs; omega
              rw [Spec.combineLayerAtAux,
                  ih rs hrs (Hasher.combine (H := H) x y :: acc)]
              simp [pairLayer, List.reverse_cons, List.append_assoc]

/-- `Spec.combineLayerAt` is the plain pairing layer. -/
theorem combineLayerAt_eq_pairLayer (H : Type) [Hasher H] (lvl : Nat)
    (cs : List ByteArray) :
    Spec.combineLayerAt H lvl cs = pairLayer H lvl cs := by
  show Spec.combineLayerAtAux H lvl cs [] = _
  have hgen := combineLayerAtAux_eq_pairLayer H lvl cs.length cs (Nat.le_refl _) []
  rw [hgen]
  simp

/-- One pairing step halves the length, rounding up. Length
induction, because `pairLayer`'s own recursion skips one cons. -/
theorem length_pairLayer (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (n : Nat) (cs : List ByteArray), cs.length ≤ n →
      (pairLayer H lvl cs).length = (cs.length + 1) / 2 := by
  intro n
  induction n with
  | zero =>
      intro cs hcs
      match cs, hcs with
      | [], _ => simp [pairLayer]
  | succ n ih =>
      intro cs hcs
      cases cs with
      | nil => simp [pairLayer]
      | cons x cs' =>
          cases cs' with
          | nil => simp [pairLayer]
          | cons y rs =>
              have hrs : rs.length ≤ n := by
                simp only [List.length_cons] at hcs; omega
              simp only [pairLayer, List.length_cons, ih rs hrs]
              omega

/-- Pairing distributes over a take: the first `k` paired values
pair the first `2 * k` chunks. Unconditional, because a short
`cs.take (2 * k)` pairs its own odd tail with a zero on both sides
alike. -/
theorem pairLayer_take (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (k : Nat) (cs : List ByteArray),
      (pairLayer H lvl cs).take k = pairLayer H lvl (cs.take (2 * k)) := by
  intro k
  induction k with
  | zero => intro cs; simp [pairLayer]
  | succ k ih =>
      intro cs
      cases cs with
      | nil => simp [pairLayer]
      | cons x cs =>
          cases cs with
          | nil =>
              have hl1 : (pairLayer H lvl [x]).length ≤ k + 1 := by
                simp [pairLayer]
              have hl2 : List.length [x] ≤ 2 * (k + 1) := by
                simp only [List.length_cons, List.length_nil]; omega
              rw [List.take_of_length_le hl1, List.take_of_length_le hl2]
          | cons y rs =>
              show (Hasher.combine (H := H) x y :: pairLayer H lvl rs).take (k + 1) = _
              simp only [List.take_cons (i := k + 1) (by omega),
                         Nat.add_sub_cancel]
              rw [ih rs]
              simp [Nat.mul_succ, pairLayer]

/-- Pairing distributes over a drop past an even boundary: past
`2 * k` chunks, the remaining paired values pair the remaining
chunks. The even bound is what makes the boundary pair close on
the take side instead of on a zero. -/
theorem pairLayer_drop (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (k : Nat) (cs : List ByteArray), 2 * k ≤ cs.length →
      (pairLayer H lvl cs).drop k = pairLayer H lvl (cs.drop (2 * k)) := by
  intro k
  induction k with
  | zero => intro cs _; simp
  | succ k ih =>
      intro cs h
      cases cs with
      | nil =>
          have h0 : List.length ([] : List ByteArray) = 0 := rfl
          omega
      | cons x cs =>
          cases cs with
          | nil =>
              have h1' : List.length [x] = 1 := by
                simp only [List.length_cons, List.length_nil]
              omega
          | cons y rs =>
              show (Hasher.combine (H := H) x y :: pairLayer H lvl rs).drop (k + 1) = _
              simp only [List.drop_cons (i := k + 1) (by omega),
                         Nat.add_sub_cancel]
              rw [ih rs (by simp only [List.length_cons] at h; omega)]
              simp [Nat.mul_succ]

/-! ### The naive tree -/

/-- The all-zero subtree of depth `lvl`, built bottom-up from bare
`zero32` leaves: the textbook padding, no memoisation and no
borrowed tower. `naiveRootAt` pads with this, so the reference is
measured against nothing but the hasher and the leaf. -/
def naiveZero (H : Type) [Hasher H] : Nat → ByteArray
  | 0     => Spec.zero32
  | lvl + 1 => Hasher.combine (H := H) (naiveZero H lvl) (naiveZero H lvl)

/-- The textbook depth-first Merkle tree, level-aware and honest
about its padding: `cs` are the values at level `lvl`; an *empty*
subtree at `(lvl, remaining)` is built by recursion, `zero32`
leaves at level `lvl` combined pairwise, with no call to the
spec's zero tower. A single chunk at `(lvl, remaining + 1)` is the
plain split: the chunk on the left, the whole empty right half.
The overflow arm (more than one chunk, no levels left) mirrors
`Spec.merkleizeAt`'s own overflow arm and sits outside every
hypothesis below. The recursion descends on `remaining`
structurally; no fuel, no well-founded measure. -/
def naiveRootAt (H : Type) [Hasher H] :
    List ByteArray → (lvl : Nat) → (remaining : Nat) → ByteArray
  | [],   lvl,    0         => naiveZero H lvl
  | [],   lvl,    remaining + 1 =>
      Hasher.combine (H := H)
        (naiveRootAt H [] lvl remaining)
        (naiveRootAt H [] lvl remaining)
  | cs,   _,      0         => cs.head?.getD Spec.zero32
  | cs,   lvl,    remaining + 1 =>
      let (l, r) := cs.splitAt (2 ^ remaining)
      Hasher.combine (H := H)
        (naiveRootAt H l lvl remaining)
        (naiveRootAt H r lvl remaining)

/-- The textbook tree, stated at the chunk level: pad to `2 ^
depth` leaves with zero leaves and combine pairwise, depth-first.
The reference every merkleizer is measured against. -/
def naiveRoot (H : Type) [Hasher H] (cs : List ByteArray) (depth : Nat) : ByteArray :=
  naiveRootAt H cs 0 depth

/-- The honest padding builds the zero tower: `naiveZero`'s
bottom-up recurrence is the spec tower's recurrence, one induction
on the depth. This is where the reference earns its zero padding;
nothing upstream hands it a memoised tower. -/
theorem naiveZero_eq_zeroHashAt (H : Type) [Hasher H] :
    ∀ lvl : Nat, naiveZero H lvl = Spec.zeroHashAt H lvl := by
  intro lvl
  induction lvl with
  | zero => rfl
  | succ lvl ih =>
      show Hasher.combine (H := H) (naiveZero H lvl) (naiveZero H lvl) = _
      rw [ih, Spec.zeroHashAt]

/-- An empty naive subtree at `(lvl, remaining)` is the zero tower
of depth `lvl + remaining`: the built-from-leaves recursion meets
the memoised tower, one induction on `remaining` generalised over
`lvl`. -/
theorem naiveRootAt_nil (H : Type) [Hasher H] :
    ∀ (rem lvl : Nat), naiveRootAt H [] lvl rem
      = Spec.zeroHashAt H (lvl + rem) := by
  intro rem
  induction rem with
  | zero => intro lvl; show naiveZero H lvl = _; exact naiveZero_eq_zeroHashAt H lvl
  | succ rem ih =>
      intro lvl
      show Hasher.combine (H := H)
        (naiveRootAt H [] lvl rem)
        (naiveRootAt H [] lvl rem) = _
      rw [ih, show lvl + (rem + 1) = (lvl + rem) + 1 from by omega,
        Spec.zeroHashAt]

/-- The empty tree roots to the zero tower. -/
theorem naiveRoot_nil (H : Type) [Hasher H] (d : Nat) :
    naiveRoot H [] d = zeroHashAt H d := by
  show naiveRootAt H [] 0 d = _
  rw [naiveRootAt_nil, Nat.zero_add]

/-- One promotion step: promoting through one more level pairs the
current value with the level's zero tower, on top of the rest of
the chain. Stated the way the split arm composes with it. -/
theorem promoteThroughZeros_succ (H : Type) [Hasher H] :
    ∀ (c : ByteArray) (lvl rem : Nat),
      Spec.promoteThroughZeros H c lvl (rem + 1) =
        Hasher.combine (H := H) (Spec.promoteThroughZeros H c lvl rem)
          (zeroHashAt H (lvl + rem)) := by
  intro c lvl rem
  induction rem generalizing c lvl with
  | zero => simp [Spec.promoteThroughZeros]
  | succ k ih =>
      have hL : Spec.promoteThroughZeros H c lvl (k + 1 + 1)
          = Spec.promoteThroughZeros H
              (Hasher.combine (H := H) c (zeroHashAt H lvl)) (lvl + 1) (k + 1) :=
        by rfl
      have hR : Spec.promoteThroughZeros H c lvl (k + 1)
          = Spec.promoteThroughZeros H
              (Hasher.combine (H := H) c (zeroHashAt H lvl)) (lvl + 1) k :=
        by rfl
      show Spec.promoteThroughZeros H c lvl (k + 1 + 1)
          = Hasher.combine (H := H)
              (Spec.promoteThroughZeros H c lvl (k + 1))
              (zeroHashAt H (lvl + (k + 1)))
      rw [hL, hR, ih (Hasher.combine (H := H) c (zeroHashAt H lvl)) (lvl + 1),
          show lvl + (k + 1) = lvl + 1 + k from by omega]

/-- The plan's promotion lemma, with content: promoting a single
chunk through `rem` zero levels equals the naive tree over that one
chunk, because the naive side splits the singleton into the chunk
and an empty half, and the empty half is the tower. -/
theorem promoteThroughZeros_eq_naiveRootAt (H : Type) [Hasher H] :
    ∀ (rem lvl : Nat) (c : ByteArray),
      Spec.promoteThroughZeros H c lvl rem = naiveRootAt H [c] lvl rem := by
  intro rem
  induction rem with
  | zero => intro lvl c; rfl
  | succ rem ih =>
      intro lvl c
      have h1 : List.length [c] ≤ 2 ^ rem := by
        have := Nat.one_le_two_pow (n := rem)
        simpa using this
      rw [naiveRootAt.eq_def]
      simp only [List.splitAt_eq, List.take_of_length_le h1,
        List.drop_of_length_le h1]
      rw [← ih, naiveRootAt_nil]
      exact promoteThroughZeros_succ H c lvl rem

theorem naiveRootAt_one (H : Type) [Hasher H] (z : ByteArray) (lvl rem : Nat) :
    naiveRootAt H [z] lvl (rem + 1) =
      naiveRootAt H [Hasher.combine (H := H) z (zeroHashAt H lvl)] (lvl + 1) rem := by
  rw [← promoteThroughZeros_eq_naiveRootAt H (rem + 1) lvl z,
    ← promoteThroughZeros_eq_naiveRootAt H rem (lvl + 1)
      (Hasher.combine (H := H) z (zeroHashAt H lvl))]
  rfl


/-- The two-element core of the bridge: a two-chunk tree one level
deeper is the paired chunk's tree one level up. -/
theorem naiveRootAt_two (H : Type) [Hasher H] :
    ∀ (rem : Nat) (x y : ByteArray) (lvl : Nat),
      naiveRootAt H [x, y] lvl (rem + 1) =
        naiveRootAt H [Hasher.combine (H := H) x y] (lvl + 1) rem := by
  intro rem
  induction rem with
  | zero =>
      intro x y lvl
      simp only [Nat.zero_add]
      show naiveRootAt H [x, y] lvl 1 = _
      simp [naiveRootAt, List.splitAt_eq]
  | succ rem ih =>
      intro x y lvl
      -- Both sides, one depth-first step at a time. The pair is a
      -- singleton at the next level, so each right half is the empty
      -- tower, and `ih` runs the left halves in step.
      have h1 : 1 ≤ 2 ^ rem := Nat.one_le_two_pow
      have e1 : naiveRootAt H [x, y] lvl (rem + 1 + 1)
          = Hasher.combine (H := H)
              (naiveRootAt H [x, y] lvl (rem + 1))
              (naiveRootAt H ([] : List ByteArray) lvl (rem + 1)) := by
        have h2 : List.length [x, y] ≤ 2 ^ (rem + 1) := by
          simp only [List.length_cons, List.length_nil]
          have := Nat.one_le_two_pow (n := rem + 1)
          omega
        rw [naiveRootAt.eq_def]
        simp only [List.splitAt_eq, List.take_of_length_le h2,
          List.drop_of_length_le h2]
      have e2 : naiveRootAt H [Hasher.combine (H := H) x y] (lvl + 1) (rem + 1)
          = Hasher.combine (H := H)
              (naiveRootAt H [Hasher.combine (H := H) x y] (lvl + 1) rem)
              (naiveRootAt H ([] : List ByteArray) (lvl + 1) rem) := by
        have h2 : List.length [Hasher.combine (H := H) x y] ≤ 2 ^ rem := by
          simp only [List.length_cons, List.length_nil]
          have := Nat.one_le_two_pow (n := rem)
          omega
        rw [naiveRootAt.eq_def]
        simp only [List.splitAt_eq, List.take_of_length_le h2,
          List.drop_of_length_le h2]
      rw [e1, e2, ih x y lvl, naiveRootAt_nil, naiveRootAt_nil,
        show lvl + (rem + 1) = lvl + 1 + rem from by omega]

/-! ### The bridge: one split equals one pairing step -/

/-- One depth-first midpoint split equals one breadth-first pairing
step: the naive tree of `cs` at `(lvl, remaining + 1)` is the naive
tree of the paired layer at `(lvl + 1, remaining)`. Induction on
`remaining`; the two-element case is `naiveRootAt_two`, the full-
left-half case distributes the pairing over the split by
`pairLayer_take` / `pairLayer_drop`, and the short right-half cases
(`|r| ∈ {0, 1}`) close through the definitions. -/
theorem naiveRootAt_eq_pairLayer (H : Type) [Hasher H] :
    ∀ (rem : Nat) (cs : List ByteArray) (lvl : Nat),
      2 ≤ cs.length → cs.length ≤ 2 ^ (rem + 1) →
      naiveRootAt H cs lvl (rem + 1) =
        naiveRootAt H (pairLayer H lvl cs) (lvl + 1) rem := by
  intro rem
  induction rem with
  | zero =>
      intro cs lvl h2 hle
      simp only [Nat.zero_add, Nat.reducePow] at hle
      cases cs with
      | nil => simp at h2
      | cons x cs =>
          cases cs with
          | nil => simp at h2
          | cons y cs =>
              cases cs with
              | nil => exact naiveRootAt_two H 0 x y lvl
              | cons z cs => simp at hle
  | succ rem ih =>
      intro cs lvl h2 hle
      rw [Nat.pow_succ, Nat.pow_succ] at hle
      have hpow : 2 ^ (rem + 1) = 2 * 2 ^ rem := by
        rw [Nat.pow_succ, Nat.mul_comm]
      -- `cs` peels two conses: it is `x :: y :: z :: rs` (length ≥ 3;
      -- the length-2 case is `naiveRootAt_two`).
      cases cs with
      | nil => simp at h2
      | cons x cs =>
          cases cs with
          | nil => simp at h2
          | cons y cs =>
              cases cs with
              | nil => exact naiveRootAt_two H (rem + 1) x y lvl
              | cons z rs =>
                  have h3 : 3 ≤ (x :: y :: z :: rs).length := by
                    simp only [List.length_cons]; omega
                  by_cases hfull : 2 ^ (rem + 1) ≤ (x :: y :: z :: rs).length
                  · -- The left half is full: exactly `2 ^ (rem + 1)` chunks.
                    have hl :
                        ((x :: y :: z :: rs).take (2 ^ (rem + 1))).length
                          = 2 ^ (rem + 1) := by
                      rw [List.length_take, List.length_cons]
                      simp only [List.length_cons]
                      exact Nat.min_eq_left hfull
                    have h2full : 2 ≤ 2 ^ (rem + 1) := by
                      rw [hpow]
                      have h1' : 1 ≤ 2 ^ rem := Nat.one_le_two_pow
                      omega
                    have hdropH : 2 * 2 ^ rem ≤ (x :: y :: z :: rs).length := by
                      rw [← hpow]
                      exact hfull
                    -- The paired layer splits the same way.
                    have htake :
                        (pairLayer H lvl (x :: y :: z :: rs)).take (2 ^ rem)
                          = pairLayer H lvl
                              ((x :: y :: z :: rs).take (2 ^ (rem + 1))) := by
                      rw [pairLayer_take, ← hpow]
                    have hdrop :
                        (pairLayer H lvl (x :: y :: z :: rs)).drop (2 ^ rem)
                          = pairLayer H lvl
                              ((x :: y :: z :: rs).drop (2 ^ (rem + 1))) := by
                      rw [pairLayer_drop _ _ _ _ hdropH, ← hpow]
                    -- The paired layer holds at least two values, so the
                    -- target's split arm fires; give it its cons-cons shape.
                    have hps2 :
                        2 ≤ (pairLayer H lvl (x :: y :: z :: rs)).length := by
                      rw [length_pairLayer H lvl _ _ (Nat.le_refl _)]
                      show 2 ≤ (((rs.length + 1) + 1) + 1 + 1) / 2
                      omega
                    obtain ⟨u, v, t2, hps⟩ :
                        ∃ u v tl, pairLayer H lvl (x :: y :: z :: rs)
                          = u :: v :: tl := by
                      cases hps : pairLayer H lvl (x :: y :: z :: rs) with
                      | nil => rw [hps] at hps2; simp at hps2
                      | cons a t' =>
                          cases t' with
                          | nil => rw [hps] at hps2; simp at hps2
                          | cons b tl => exact ⟨a, b, tl, rfl⟩
                    rw [hps] at htake hdrop
                    simp only [naiveRootAt, List.splitAt_eq, hps]
                    rw [htake, hdrop]
                    have hRbound :
                        ((x :: y :: z :: rs).drop (2 ^ (rem + 1))).length
                          ≤ 2 ^ (rem + 1) := by
                      rw [List.length_drop]
                      omega
                    by_cases hr2 :
                        2 ≤ ((x :: y :: z :: rs).drop (2 ^ (rem + 1))).length
                    · -- Both halves non-trivial: the induction hypothesis twice.
                      rw [ih ((x :: y :: z :: rs).take (2 ^ (rem + 1))) lvl
                            (by rw [hl]; exact h2full)
                            (by rw [hl]; exact Nat.le_refl _),
                          ih ((x :: y :: z :: rs).drop (2 ^ (rem + 1))) lvl hr2
                            hRbound]
                    · -- `|r| ∈ {0, 1}`: the right child is the empty tower or
                      -- one promotion step.
                      cases hdropp :
                          (x :: y :: z :: rs).drop (2 ^ (rem + 1)) with
                      | nil =>
                          rw [ih ((x :: y :: z :: rs).take (2 ^ (rem + 1))) lvl
                                (by rw [hl]; exact h2full)
                                (by rw [hl]; exact Nat.le_refl _)]
                          simp only [pairLayer, naiveRootAt_nil]
                          rw [show lvl + (rem + 1) = lvl + 1 + rem from by omega]
                      | cons w t' =>
                          cases t' with
                          | nil =>
                              rw [ih ((x :: y :: z :: rs).take (2 ^ (rem + 1))) lvl
                                    (by rw [hl]; exact h2full)
                                    (by rw [hl]; exact Nat.le_refl _),
                                  naiveRootAt_one]
                              simp only [pairLayer]
                          | cons b tl =>
                              rw [hdropp] at hr2
                              simp only [List.length_cons, List.length_cons] at hr2
                              omega
                  · -- Short list: the whole `cs` is the left half.
                    have htakeAll :
                        (x :: y :: z :: rs).take (2 ^ (rem + 1)) = x :: y :: z :: rs :=
                      List.take_of_length_le (by omega)
                    have hdropNil :
                        (x :: y :: z :: rs).drop (2 ^ (rem + 1)) = [] :=
                      List.drop_of_length_le (by omega)
                    have hps2 :
                        2 ≤ (pairLayer H lvl (x :: y :: z :: rs)).length := by
                      rw [length_pairLayer H lvl _ _ (Nat.le_refl _)]
                      show 2 ≤ (((rs.length + 1) + 1) + 1 + 1) / 2
                      omega
                    have hpsLen :
                        (pairLayer H lvl (x :: y :: z :: rs)).length ≤ 2 ^ rem := by
                      have hb : (x :: y :: z :: rs).length + 1 ≤ 2 * 2 ^ rem := by
                        have hn := hfull
                        simp only [Nat.pow_succ] at hn
                        omega
                      rw [length_pairLayer H lvl _ _ (Nat.le_refl _)]
                      omega
                    obtain ⟨u, v, t2, hps⟩ :
                        ∃ u v tl, pairLayer H lvl (x :: y :: z :: rs)
                          = u :: v :: tl := by
                      cases hps : pairLayer H lvl (x :: y :: z :: rs) with
                      | nil => rw [hps] at hps2; simp at hps2
                      | cons a t' =>
                          cases t' with
                          | nil => rw [hps] at hps2; simp at hps2
                          | cons b tl => exact ⟨a, b, tl, rfl⟩
                    rw [hps] at hpsLen
                    -- Both sides, one depth-first step at a time. The
                    -- induction hypothesis's bound comes from `hfull`'s
                    -- negation: `cs.length < 2 ^ (rem + 1)`.
                    have hn := hfull
                    have e1 : naiveRootAt H (x :: y :: z :: rs) lvl (rem + 1 + 1)
                        = Hasher.combine (H := H)
                            (naiveRootAt H (x :: y :: z :: rs) lvl (rem + 1))
                            (zeroHashAt H (lvl + (rem + 1))) := by
                      rw [naiveRootAt.eq_def]
                      simp only [List.splitAt_eq, htakeAll, hdropNil]
                      rw [naiveRootAt_nil]
                    have e2 : naiveRootAt H (pairLayer H lvl (x :: y :: z :: rs))
                          (lvl + 1) (rem + 1)
                        = Hasher.combine (H := H)
                            (naiveRootAt H (u :: v :: t2) (lvl + 1) rem)
                            (zeroHashAt H (lvl + 1 + rem)) := by
                      rw [hps, naiveRootAt.eq_def]
                      simp only [List.splitAt_eq, List.take_of_length_le hpsLen,
                                 List.drop_of_length_le hpsLen]
                      rw [naiveRootAt_nil]
                    rw [e1, e2,
                        ih (x :: y :: z :: rs) lvl h2
                          (Nat.le_of_lt (Nat.lt_of_not_le hn)), hps,
                        show lvl + (rem + 1) = lvl + 1 + rem from by omega]

/-! ### The two folds agree -/

/-- The level-aware agreement: from two chunks on, one
`merkleizeAt` step is one pairing step, so the two folds walk the
same tree. Induction on `remaining`; the one-chunk and empty cases
are the same promote arm on both sides, and the step is
`naiveRootAt_eq_pairLayer` plus `combineLayerAt_eq_pairLayer`. -/
theorem merkleizeAt_eq_naiveRootAt (H : Type) [Hasher H] :
    ∀ (rem : Nat) (cs : List ByteArray) (lvl : Nat),
      2 ≤ cs.length → cs.length ≤ 2 ^ rem →
      Spec.merkleizeAt H cs lvl rem = naiveRootAt H cs lvl rem := by
  intro rem
  induction rem with
  | zero =>
      intro cs lvl h2 hle
      simp only [Nat.reducePow] at hle
      omega
  | succ rem ih =>
      intro cs lvl h2 hle
      rw [Nat.pow_succ] at hle
      have hpow : 2 ^ (rem + 1) = 2 * 2 ^ rem := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hle2 : cs.length ≤ 2 * 2 ^ rem := by omega
      -- Both sides, one step at a time. `merkleizeAt`'s step arm
      -- needs `cs` to hold two or more chunks, which `h2` gives.
      have e1 : Spec.merkleizeAt H cs lvl (rem + 1)
          = Spec.merkleizeAt H (Spec.combineLayerAt H lvl cs) (lvl + 1) rem := by
        cases cs with
        | nil => simp at h2
        | cons c cs' =>
            cases cs' with
            | nil => simp at h2
            | cons d rs => rfl
      have e2 : naiveRootAt H cs lvl (rem + 1)
          = naiveRootAt H (pairLayer H lvl cs) (lvl + 1) rem :=
        naiveRootAt_eq_pairLayer H rem cs lvl h2 hle
      rw [e1, e2, combineLayerAt_eq_pairLayer]
      -- The paired layer holds one to `2 ^ rem` values. One value is
      -- the promote arm on both sides; two or more take the
      -- induction hypothesis.
      have hplen : (pairLayer H lvl cs).length = (cs.length + 1) / 2 :=
        length_pairLayer H lvl cs.length cs (Nat.le_refl _)
      have hp1 : 1 ≤ (pairLayer H lvl cs).length := by
        rw [hplen]
        omega
      match hp : pairLayer H lvl cs with
      | [] =>
          rw [hp] at hp1
          simp at hp1
      | [c] =>
          simp only [Spec.merkleizeAt]
          exact promoteThroughZeros_eq_naiveRootAt H rem (lvl + 1) c
      | c :: d :: rs =>
          have h2' : 2 ≤ (c :: d :: rs : List ByteArray).length := by simp
          have hle' : (c :: d :: rs : List ByteArray).length ≤ 2 ^ rem := by
            rw [← hp, hplen]
            have h1' : 1 ≤ 2 ^ rem := Nat.one_le_two_pow
            omega
          exact ih _ _ h2' hle'

/-- The textbook fold and the spec's merkleizer agree whenever the
tree is deep enough for its own leaves, `chunks.length ≤ 2 ^
depth`. The overflow arm of `merkleizeAt`, which answers where the
spec refuses to, sits outside the hypothesis. The empty and
one-chunk lists are the promote arm on both sides; longer lists
take the level-aware agreement at level 0. -/
theorem merkleize_eq_naiveRoot (H : Type) [Hasher H] (chunks : List ByteArray)
    (depth : Nat) (h : chunks.length ≤ 2 ^ depth) :
    Spec.merkleize H chunks depth = naiveRoot H chunks depth := by
  show Spec.merkleizeAt H chunks 0 depth = naiveRootAt H chunks 0 depth
  match chunks with
  | [] =>
      simp only [Spec.merkleizeAt]
      rw [naiveRootAt_nil, Nat.zero_add]
  | [c] =>
      simp only [Spec.merkleizeAt]
      exact promoteThroughZeros_eq_naiveRootAt H depth 0 c
  | c :: d :: rs => exact merkleizeAt_eq_naiveRootAt H depth _ 0 (by simp) h
