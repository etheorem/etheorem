import SizzLean.Cache.MerkleTree.SetAt
import SizzLean.Proofs.Merkle.Chunk
import SizzLean.Spec.GeneralizedIndex

/-!
# `SizzLean.Proofs.Merkle.Gindex`: the bit-path ↔ index bridge

`Cache.MerkleTree.gindexBits` turns a generalized index into the
root-to-target path of bits; `gindexOfBits` (next to `gindexBits`
in `Cache/MerkleTree/SetAt.lean`) turns a path back into an index.
The theorems:

* `gindexBits_pow_add`: for `r < 2 ^ depth`, the path of
  `2 ^ depth + r` is exactly the `depth` bits of `r`, most
  significant bit first. This is the shape every field-addressed
  write uses: a container field `k` sits at index
  `2 ^ chunkDepth + k`, and this theorem turns that index into the
  bit walk `setAtBits` consumes.
* `gindexBits_cons_pow_add`: the first-bit split of the same
  address, the step lemma behind the field-addressed writes.
* `gindexOfBits_gindexBits` / `gindexBits_gindexOfBits`: the round
  trips, closing the Nimbus-class off-by-one at the type level.
* `gindexBits_append_step`: one path step appends. Descending one
  level multiplies the index by the block width and adds the slot,
  and the index's bit path is the parent's path followed by the
  slot's own bits.
* `gindexBits_generalizedIndex`: the whole decomposition. The
  index `Spec.SSZType.generalizedIndex` builds by folding a path of
  `PathStep`s has `Spec.SSZType.pathBits` as its bit path, one
  step's low bits at a time, outermost step first. The per-step
  corollaries `pathBits_container_field`, `pathBits_vector_elem`,
  and `pathBits_list_elem` spell the composite cases in the form
  the `sszUpdate` elaborator's `walkPath` emits.
-/

set_option autoImplicit false

namespace SizzLean.Proofs.Merkle

open SizzLean.Cache.MerkleTree
open SizzLean.Spec

/-- The log2 of a leading power plus a smaller tail is the
exponent. -/
theorem log2_two_pow_add {n i : Nat} (hi : i < 2 ^ n) :
    Nat.log2 (2 ^ n + i) = n := by
  rw [Nat.log2_eq_iff (by omega)]
  exact ⟨by omega, by omega⟩

/-- The path of `2 ^ depth + r`, for `r` inside the level: the
`depth` bits of `r`, most significant bit first. -/
theorem gindexBits_pow_add (depth r : Nat) (hr : r < 2 ^ depth) :
    Cache.MerkleTree.gindexBits (2 ^ depth + r)
      = (List.range depth).reverse.map (fun i => r.testBit i) := by
  show (List.range (Nat.log2 (2 ^ depth + r))).reverse.map
        ((2 ^ depth + r).testBit ·)
      = (List.range depth).reverse.map (fun i => r.testBit i)
  rw [log2_two_pow_add hr]
  exact List.map_congr_left fun i hi => by
    have h := Nat.testBit_two_pow_mul_add 1 hr i
    rw [Nat.mul_one, if_pos (List.mem_range.mp (List.mem_reverse.mp hi))] at h
    exact h

/-- The first-bit split of a field address one level down: the bit
at `d` picks the child, the remaining path addresses
`r % 2 ^ d` inside that child. -/
theorem gindexBits_cons_pow_add (d r : Nat) (hr : r < 2 ^ (d + 1)) :
    Cache.MerkleTree.gindexBits (2 ^ (d + 1) + r)
      = r.testBit d :: Cache.MerkleTree.gindexBits (2 ^ d + r % 2 ^ d) := by
  have hr' : r % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
  show (List.range (Nat.log2 (2 ^ (d + 1) + r))).reverse.map
        ((2 ^ (d + 1) + r).testBit ·)
      = r.testBit d :: Cache.MerkleTree.gindexBits (2 ^ d + r % 2 ^ d)
  rw [log2_two_pow_add (by omega : r < 2 ^ (d + 1)),
    gindexBits_pow_add d (r % 2 ^ d) hr',
    List.range_succ, List.reverse_append, List.reverse_singleton,
    List.map_append, List.map_cons]
  have hfirst := Nat.testBit_two_pow_mul_add 1 hr d
  simp only [Nat.mul_one, if_pos (Nat.lt_succ_self d)] at hfirst
  rw [hfirst]
  exact congrArg _ (List.map_congr_left fun i hi => by
    have him : i < d := List.mem_range.mp (List.mem_reverse.mp hi)
    have h2 := Nat.testBit_two_pow_mul_add 1 hr i
    simp only [Nat.mul_one, if_pos (Nat.lt_succ_of_lt him)] at h2
    rw [h2, Nat.testBit_mod_two_pow, decide_eq_true him, Bool.true_and])

/-- The fold the pending-map's `gindexOfBits` performs, over a
nonempty accumulator: accumulator times the width plus the value of
the bits. -/
theorem foldl_bits_acc (bs : List Bool) (acc : Nat) :
    bs.foldl (fun acc b => 2 * acc + b.toNat) acc
      = acc * 2 ^ bs.length + bs.foldl (fun acc b => 2 * acc + b.toNat) 0 := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
      have h1 := ih (2 * acc + b.toNat)
      have h2 := ih b.toNat
      simp only [Nat.mul_zero, Nat.zero_add, List.foldl_cons] at h2 ⊢
      rw [h1, h2, List.length_cons, Nat.pow_succ]
      simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
        Nat.add_assoc]

/-- The bits of the path reconstruct the tail value: the path of
`2 ^ depth + r`, read back as a number, is `r` itself. -/
theorem bitsValue_gindexBits_pow_add (depth r : Nat) (hr : r < 2 ^ depth) :
    (Cache.MerkleTree.gindexBits (2 ^ depth + r)).foldl
      (fun acc b => 2 * acc + b.toNat) 0 = r := by
  induction depth generalizing r with
  | zero =>
      cases r with
      | zero => rfl
      | succ _ => omega
  | succ d ih =>
      have hr' : r % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
      have hbit : r.testBit d = decide (2 ^ d ≤ r) := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hbound : r / 2 ^ d < 2 := Nat.div_lt_of_lt_mul
          (show r < 2 ^ d * 2 from by have := Nat.pow_succ 2 d; omega)
        cases Nat.lt_or_ge r (2 ^ d) with
        | inl hlt =>
            have hd : r / 2 ^ d = 0 := Nat.div_eq_of_lt hlt
            rw [hd]
            simp [hlt]
        | inr hge =>
            have hd1 : 1 ≤ r / 2 ^ d :=
              (Nat.le_div_iff_mul_le (Nat.two_pow_pos d)).mpr
                (show 1 * 2 ^ d ≤ r from by rwa [Nat.one_mul])
            have hd : r / 2 ^ d = 1 := by omega
            rw [hd]
            simp [hge]
      rw [gindexBits_cons_pow_add d r (by omega : r < 2 ^ (d + 1))]
      cases Nat.lt_or_ge r (2 ^ d) with
      | inl hlt =>
          have hbit' : r.testBit d = false := by
            rw [hbit]; simp [hlt]
          have hstep : (Cache.MerkleTree.gindexBits (2 ^ d + r % 2 ^ d)).foldl
              (fun acc b => 2 * acc + b.toNat) 0 = r := by
            rw [Nat.mod_eq_of_lt hlt]
            exact ih r hlt
          rw [hbit']
          show (Cache.MerkleTree.gindexBits (2 ^ d + r % 2 ^ d)).foldl
            (fun acc b => 2 * acc + b.toNat) 0 = r
          exact hstep
      | inr hge =>
          have hbit' : r.testBit d = true := by
            rw [hbit]; simp [hge]
          have hsplit : 2 ^ d + r % 2 ^ d = r := by
            have hd1 : 1 ≤ r / 2 ^ d :=
              (Nat.le_div_iff_mul_le (Nat.two_pow_pos d)).mpr
                (show 1 * 2 ^ d ≤ r from by rwa [Nat.one_mul])
            have hd2 : r / 2 ^ d < 2 := Nat.div_lt_of_lt_mul
              (show r < 2 ^ d * 2 from by have := Nat.pow_succ 2 d; omega)
            have hq : r / 2 ^ d = 1 := by omega
            have hdm := Nat.div_add_mod r (2 ^ d)
            simp only [hq, Nat.mul_one] at hdm
            omega
          have hrec := ih (r % 2 ^ d) hr'
          have hlen : (Cache.MerkleTree.gindexBits (2 ^ d + r % 2 ^ d)).length = d := by
            rw [gindexBits_pow_add d (r % 2 ^ d) hr']
            simp [List.length_reverse, List.length_range]
          have hstep : (Cache.MerkleTree.gindexBits (2 ^ d + r % 2 ^ d)).foldl
              (fun acc b => 2 * acc + b.toNat) 1 = r := by
            rw [foldl_bits_acc, hlen, Nat.one_mul, hrec]
            omega
          rw [hbit']
          show (Cache.MerkleTree.gindexBits (2 ^ d + r % 2 ^ d)).foldl
            (fun acc b => 2 * acc + b.toNat) 1 = r
          exact hstep

/-! ### The round trips -/

/-- The bit list read as a binary number, most significant bit
first: the fold `2 * acc + bit` puts the first bit on top. The
round-trip theorems below read `gindexBits`' output back through
this fold. -/
def bitsValueBE (bs : List Bool) : Nat := bs.foldl (fun acc b => 2 * acc + b.toNat) 0

/-- Consing a bit shifts the tail up one place and puts the new bit
on top: the head bit carries weight `2 ^ bs.length`. -/
theorem bitsValueBE_cons (b : Bool) (bs : List Bool) :
    bitsValueBE (b :: bs) = b.toNat * 2 ^ bs.length + bitsValueBE bs := by
  have h := foldl_bits_acc bs (2 * 0 + b.toNat)
  show bs.foldl _ (2 * 0 + b.toNat) = _
  rw [h]
  simp [bitsValueBE]

/-- A bit list's value is smaller than its own width: the head bit
contributes at most `2 ^ bs.length` and the tail is `bitsValueBE_lt`
of the rest. -/
theorem bitsValueBE_lt (bs : List Bool) : bitsValueBE bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsValueBE]
  | cons b bs ih =>
      rw [bitsValueBE_cons, List.length_cons]
      cases b with
      | false =>
          rw [show (false : Bool).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add]
          have heq : 2 ^ (bs.length + 1) = 2 ^ bs.length + 2 ^ bs.length := by
            rw [Nat.pow_succ, Nat.mul_comm]
            exact Nat.two_mul _
          have hle : 2 ^ bs.length ≤ 2 ^ (bs.length + 1) := by
            rw [heq]
            omega
          exact Nat.lt_of_lt_of_le ih hle
      | true =>
          rw [show (true : Bool).toNat = 1 from rfl, Nat.one_mul]
          have hp : 2 ^ (bs.length + 1) = 2 ^ bs.length + 2 ^ bs.length := by
            rw [Nat.pow_succ]; omega
          rw [hp]
          exact Nat.add_lt_add_left ih (2 ^ bs.length)

/-- The path of `2 ^ length + value` is the bit list itself. -/
theorem gindexBits_of_bitsValueBE (bs : List Bool) :
    Cache.MerkleTree.gindexBits (2 ^ bs.length + bitsValueBE bs) = bs := by
  induction bs with
  | nil =>
      simp only [bitsValueBE]
      rfl
  | cons b bs ih =>
      have hlen : b.toNat * 2 ^ bs.length + bitsValueBE bs
          < 2 ^ (bs.length + 1) := by
        have hlt := bitsValueBE_lt bs
        have h1 : b.toNat ≤ 1 := by cases b <;> simp
        have hp : 2 ^ (bs.length + 1) = 2 ^ bs.length + 2 ^ bs.length := by
          rw [Nat.pow_succ]; omega
        have h3 : b.toNat * 2 ^ bs.length ≤ 1 * 2 ^ bs.length :=
          Nat.mul_le_mul_right (2 ^ bs.length) h1
        rw [hp]
        omega
      rw [bitsValueBE_cons (b := b), List.length_cons,
        gindexBits_cons_pow_add bs.length _ hlen]
      have hhead : (b.toNat * 2 ^ bs.length + bitsValueBE bs).testBit bs.length = b := by
        have h := Nat.testBit_two_pow_mul_add b.toNat (bitsValueBE_lt bs) bs.length
        cases b with
        | false => simpa using h
        | true => simpa using h
      have hmod : (b.toNat * 2 ^ bs.length + bitsValueBE bs)
          % 2 ^ bs.length = bitsValueBE bs := by
        rw [Nat.add_comm (b.toNat * 2 ^ bs.length),
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (bitsValueBE_lt bs)]
      rw [hhead, hmod, ih]

/-- The two fold functions agree pointwise. -/
theorem foldl_boolIf_eq_toNat (bs : List Bool) (acc : Nat) :
    bs.foldl (fun acc b => if b = true then 2 * acc + 1 else 2 * acc) acc
      = bs.foldl (fun acc b => 2 * acc + b.toNat) acc := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
      show bs.foldl _ (if b = true then 2 * acc + 1 else 2 * acc)
        = bs.foldl _ (2 * acc + b.toNat)
      cases b with
      | false =>
          rw [if_neg (by decide), show (false : Bool).toNat = 0 from rfl,
            Nat.add_zero]
          exact ih _
      | true =>
          rw [if_pos rfl, show (true : Bool).toNat = 1 from rfl, Nat.add_zero]
          exact ih _

/-- The pending-map round trip: bits to index and back. -/
theorem gindexBits_gindexOfBits (bits : List Bool) :
    Cache.MerkleTree.gindexBits (Cache.MerkleTree.gindexOfBits bits) = bits := by
  have hval : Cache.MerkleTree.gindexOfBits bits
      = 2 ^ bits.length + bitsValueBE bits := by
    have hfun := foldl_boolIf_eq_toNat bits 1
    unfold Cache.MerkleTree.gindexOfBits
    rw [hfun, foldl_bits_acc, Nat.one_mul]
    rfl
  rw [hval, gindexBits_of_bitsValueBE]

/-- The index round trip: index to bits and back. -/
theorem gindexOfBits_gindexBits (g : Nat) (h : 1 ≤ g) :
    Cache.MerkleTree.gindexOfBits (Cache.MerkleTree.gindexBits g) = g := by
  have hspec1 : 2 ^ Nat.log2 g ≤ g := Nat.log2_self_le (by omega)
  have hspec2 : g < 2 ^ (Nat.log2 g + 1) :=
    (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
  have hr' : g % 2 ^ Nat.log2 g < 2 ^ Nat.log2 g := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsub : g % 2 ^ Nat.log2 g = g - 2 ^ Nat.log2 g := by
    rw [Nat.mod_eq_sub_mod hspec1]
    exact Nat.mod_eq_of_lt (by
      have := Nat.pow_succ 2 (Nat.log2 g)
      omega)
  have hdecomp : 2 ^ Nat.log2 g + g % 2 ^ Nat.log2 g = g := by omega
  have hbits := bitsValue_gindexBits_pow_add (Nat.log2 g) (g % 2 ^ Nat.log2 g) hr'
  have hlen : (Cache.MerkleTree.gindexBits (2 ^ Nat.log2 g + g % 2 ^ Nat.log2 g)).length
      = Nat.log2 g := by
    rw [gindexBits_pow_add _ _ hr']
    simp [List.length_reverse, List.length_range]
  unfold Cache.MerkleTree.gindexOfBits
  rw [foldl_boolIf_eq_toNat, ← hdecomp, foldl_bits_acc _ 1, hlen, Nat.one_mul,
    hbits]

/-! ### Appending one path step

Descending one level of a container multiplies the generalized
index by `2 ^ d`, the child block's width, and adds the slot. The
path bits of the result are the parent's bits followed by the
slot's `d` bits. -/

/-- The reversed `range` of a sum splits into the reversed mapped
high block and the reversed low block, both descending. -/
private theorem reverse_range_add_map (m d : Nat) :
    (List.range (m + d)).reverse
      = ((List.range m).map (fun y => y + d)).reverse ++ (List.range d).reverse := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hshift : m + 1 + d = m + d + 1 := by omega
      rw [hshift]
      show (List.range (m + d + 1)).reverse
        = ((List.range (m+1)).map (fun y => y + d)).reverse
            ++ (List.range d).reverse
      rw [List.range_succ, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.map_append, List.map_singleton,
        List.reverse_append, List.reverse_singleton, ih]
      rfl

/-- The log2 of `g * 2 ^ d + k` with `k` inside the block: the
parent's log2 plus the block depth. -/
theorem log2_mul_pow_add {g d k : Nat} (hg : 0 < g) (hk : k < 2 ^ d) :
    Nat.log2 (g * 2 ^ d + k) = Nat.log2 g + d := by
  rw [Nat.log2_eq_iff (by
    have hpos := Nat.mul_pos hg (Nat.two_pow_pos d)
    omega)]
  have h1 : 2 ^ Nat.log2 g ≤ g := Nat.log2_self_le (by omega)
  have h2 : g < 2 ^ (Nat.log2 g + 1) := by
    rw [← Nat.log2_lt (by omega)]
    exact Nat.lt_succ_self _
  constructor
  · calc 2 ^ (Nat.log2 g + d) = 2 ^ Nat.log2 g * 2 ^ d := by
          rw [Nat.pow_add]
      _ ≤ g * 2 ^ d := Nat.mul_le_mul_right _ h1
      _ ≤ g * 2 ^ d + k := Nat.le_add_right _ _
  · calc g * 2 ^ d + k < (g + 1) * 2 ^ d := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
      _ ≤ 2 ^ (Nat.log2 g + 1) * 2 ^ d := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (Nat.log2 g + d + 1) := by
          rw [Nat.pow_succ, Nat.pow_add, Nat.pow_one, Nat.pow_add,
            Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ d)]

/-- The path bits of `g * 2 ^ d + k`: the parent's path followed by
the slot's `d` bits. This is the per-step decomposition the branch
rows take: a generalized index built step by step has the steps'
bit paths concatenated, outermost step first. -/
theorem gindexBits_append_step {g d k : Nat} (hg : 0 < g) (hk : k < 2 ^ d) :
    Cache.MerkleTree.gindexBits (g * 2 ^ d + k)
      = Cache.MerkleTree.gindexBits g
        ++ (List.range d).reverse.map (k.testBit ·) := by
  show (List.range (Nat.log2 (g * 2 ^ d + k))).reverse.map
        ((g * 2 ^ d + k).testBit ·) = _
  rw [log2_mul_pow_add hg hk, reverse_range_add_map, List.map_append]
  have hhigh : List.map ((g * 2 ^ d + k).testBit ·)
        (((List.range (Nat.log2 g)).map (fun y => y + d)).reverse)
      = List.map (g.testBit ·) (List.range (Nat.log2 g)).reverse := by
    rw [List.map_reverse, List.map_map]
    have hinner : List.map
          ((fun x => (g * 2 ^ d + k).testBit x) ∘ fun y => y + d)
          (List.range (Nat.log2 g))
        = List.map (g.testBit ·) (List.range (Nat.log2 g)) :=
      List.map_congr_left fun y _ => by
        show (g * 2 ^ d + k).testBit (y + d) = g.testBit y
        rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add g hk (y + d),
          if_neg (by omega), Nat.add_sub_cancel_right]
    rw [hinner, ← List.map_reverse]
  rw [hhigh]
  congr 1
  exact List.map_congr_left fun x hx => by
    have hx' : x < d := by
      have := List.mem_range.mp (List.mem_reverse.mp hx)
      omega
    show (g * 2 ^ d + k).testBit x = k.testBit x
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add g hk x, if_pos hx']

/-! ### The decomposition of `get_generalized_index`

`Spec.SSZType.generalizedIndex` folds a path of `PathStep`s from
the root; `Spec.SSZType.pathBits` spells the same fold at the bit
level. The bridge: a returned index's `gindexBits` path *is*
`pathBits`, one step's low bits appended per step, outermost step
first. Every step's slot is inside its own block, which is the one
fact the induction needs beyond `gindexBits_append_step`. -/

/-- A step's slot lands inside its own block, the side condition
`gindexBits_append_step` needs per step. The basic-packed case
splits on whether the element occupies any bytes: a zero-width
element has slot `0`, inside every block. -/
theorem stepInto_pos_lt {s : SSZType} {step : PathStep} {pos d : Nat} {s' : SSZType}
    (h : s.stepInto step = some (pos, d, s')) : pos < 2 ^ d := by
  revert h
  cases s with
  | uintN n => intro h; simp [SSZType.stepInto, SSZType.isBasicType] at h
  | bool => intro h; simp [SSZType.stepInto, SSZType.isBasicType] at h
  | bitvector n => intro h; simp [SSZType.stepInto, SSZType.isBasicType] at h
  | bitlist cap => intro h; simp [SSZType.stepInto, SSZType.isBasicType] at h
  | container fs =>
      intro h
      cases step with
      | field k =>
          simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true,
            if_false] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            have hle := le_two_pow_chunkDepth fs.length
            omega
          · exact absurd h (by simp)
      | elem i => simp [SSZType.stepInto, SSZType.isBasicType] at h
      | length => simp [SSZType.stepInto, SSZType.isBasicType] at h
  | vector t n =>
      intro h
      cases step with
      | elem i =>
          simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true,
            if_false] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            by_cases hL0 : SSZType.itemLength t = 0
            · have hpos0 : i * SSZType.itemLength t / BYTES_PER_CHUNK = 0 := by
                  rw [hL0, Nat.mul_zero, Nat.zero_div]
              rw [hpos0]
              exact Nat.two_pow_pos _
            · have hLpos : 0 < SSZType.itemLength t := Nat.pos_of_ne_zero hL0
              have h1 : i * SSZType.itemLength t < n * SSZType.itemLength t :=
                Nat.mul_lt_mul_of_pos_right ‹i < n› hLpos
              have h2 : i * SSZType.itemLength t / BYTES_PER_CHUNK
                  < (n * SSZType.itemLength t + 31) / 32 := by
                show i * SSZType.itemLength t / 32 < (n * SSZType.itemLength t + 31) / 32
                omega
              exact Nat.lt_of_lt_of_le h2
                (le_two_pow_chunkDepth (bytesToChunkCount (n * SSZType.itemLength t)))
          · exact absurd h (by simp)
      | field k => simp [SSZType.stepInto, SSZType.isBasicType] at h
      | length => simp [SSZType.stepInto, SSZType.isBasicType] at h
  | list t cap =>
      intro h
      cases step with
      | elem i =>
          simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true,
            if_false] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            by_cases hL0 : SSZType.itemLength t = 0
            · have hpos0 : i * SSZType.itemLength t / BYTES_PER_CHUNK = 0 := by
                  rw [hL0, Nat.mul_zero, Nat.zero_div]
              rw [hpos0]
              exact Nat.two_pow_pos _
            · have hLpos : 0 < SSZType.itemLength t := Nat.pos_of_ne_zero hL0
              have h1 : i * SSZType.itemLength t < cap * SSZType.itemLength t :=
                Nat.mul_lt_mul_of_pos_right ‹i < cap› hLpos
              have h2 : i * SSZType.itemLength t / BYTES_PER_CHUNK
                  < (cap * SSZType.itemLength t + 31) / 32 := by
                show i * SSZType.itemLength t / 32 < (cap * SSZType.itemLength t + 31) / 32
                omega
              have hdeep : i * SSZType.itemLength t / BYTES_PER_CHUNK
                  < 2 ^ chunkDepth (SSZType.chunkCount (SSZType.list t cap)) :=
                Nat.lt_of_lt_of_le h2
                  (le_two_pow_chunkDepth (bytesToChunkCount (cap * SSZType.itemLength t)))
              rw [Nat.pow_succ]
              exact Nat.lt_of_lt_of_le hdeep
                (Nat.le_mul_of_pos_right _ (by decide : (0 : Nat) < 2))
          · exact absurd h (by simp)
      | field k => simp [SSZType.stepInto, SSZType.isBasicType] at h
      | length =>
          simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true,
            if_false] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          decide

/-- One cons step of `pathBits`, the mirror of
`generalizedIndex_step`. -/
theorem pathBits_cons (s : SSZType) (step : PathStep) (rest : List PathStep) :
    s.pathBits (step :: rest)
      = match s.stepInto step with
        | none => []
        | some (pos, d, s') =>
            (List.range d).reverse.map (pos.testBit ·) ++ s'.pathBits rest := rfl

theorem pathBits_nil (s : SSZType) : s.pathBits [] = [] := rfl

/-- The whole decomposition: a generalized index built by folding a
path of steps has the steps' bit paths, concatenated outermost step
first, as its `gindexBits` path. Induction on the path with the
accumulator generalized; each step applies `gindexBits_append_step`
with `stepInto_pos_lt` as its side condition. -/
theorem gindexBits_generalizedIndexAux :
    ∀ (path : List PathStep) (s : SSZType) (acc g : Nat), 0 < acc →
      s.generalizedIndexAux path acc = some g →
        Cache.MerkleTree.gindexBits g
          = Cache.MerkleTree.gindexBits acc ++ s.pathBits path := by
  intro path
  induction path with
  | nil =>
      intro s acc g _ h
      rw [generalizedIndexAux_nil] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [pathBits_nil, List.append_nil]
  | cons step rest ih =>
      intro s acc g hacc h
      rw [generalizedIndex_step] at h
      cases hs : s.stepInto step with
      | none => simp only [hs] at h; exact absurd h (by simp)
      | some w =>
          obtain ⟨pos, d, s'⟩ := w
          simp only [hs] at h
          have hpos := stepInto_pos_lt hs
          have hacc' : 0 < acc * 2 ^ d + pos := by
            have h := Nat.mul_pos hacc (Nat.two_pow_pos d)
            omega
          have hrec := ih s' (acc * 2 ^ d + pos) g hacc' h
          have hstep := gindexBits_append_step (g := acc) (d := d) (k := pos) hacc hpos
          rw [hstep, List.append_assoc] at hrec
          rw [pathBits_cons]
          simp only [hs]
          exact hrec

/-- The decomposition at the top level, accumulator 1. -/
theorem gindexBits_generalizedIndex (s : SSZType) (path : List PathStep) (g : Nat)
    (hg : s.generalizedIndex path = some g) :
    Cache.MerkleTree.gindexBits g = s.pathBits path := by
  have h := gindexBits_generalizedIndexAux path s 1 g (by decide) (by
    show s.generalizedIndexAux path 1 = some g
    exact hg)
  rw [show Cache.MerkleTree.gindexBits 1 = [] from rfl, List.nil_append] at h
  exact h

/-! ### The composite paths, against `walkPath`

The `sszUpdate` elaborator's `walkPath` addresses a container field
with `gindexBits (2 ^ chunkDepth fs.length + k)`, a composite-element
vector with `gindexBits (2 ^ chunkDepth n + i)`, and a
composite-element list with `false` prepended to the element's path
for the mix-in-length pair. These corollaries read `pathBits` in
exactly those forms. -/

/-- A container field's path is the field block's slot path. -/
theorem pathBits_container_field (fs : List SSZType) (k : Nat) (hk : k < fs.length) :
    (SSZType.container fs).pathBits [.field k]
      = Cache.MerkleTree.gindexBits (2 ^ chunkDepth fs.length + k) := by
  show (match (SSZType.container fs).stepInto (.field k) with
    | none => []
    | some (pos, d, s') =>
        (List.range d).reverse.map (pos.testBit ·) ++ s'.pathBits []) = _
  simp only [stepInto_field fs k hk, pathBits_nil, List.append_nil]
  exact (gindexBits_pow_add (chunkDepth fs.length) k
    (Nat.lt_of_lt_of_le hk (le_two_pow_chunkDepth fs.length))).symm

/-- A composite-element vector's element path is the element block's
slot path. -/
theorem pathBits_vector_elem (t : SSZType) (n i : Nat) (hi : i < n)
    (hc : ¬ t.isBasicType) :
    (SSZType.vector t n).pathBits [.elem i]
      = Cache.MerkleTree.gindexBits (2 ^ chunkDepth n + i) := by
  have hstep := stepInto_elem_vector t n i hi
  have hcount := chunkCount_vector_composite t n hc
  have hpos : i * SSZType.itemLength t / BYTES_PER_CHUNK = i := by
    rw [itemLength_of_not_isBasicType t hc]
    show i * 32 / 32 = i
    omega
  show (match (SSZType.vector t n).stepInto (.elem i) with
    | none => []
    | some (pos, d, s') =>
        (List.range d).reverse.map (pos.testBit ·) ++ s'.pathBits []) = _
  simp only [hstep, hpos, hcount, pathBits_nil, List.append_nil]
  exact (gindexBits_pow_add (chunkDepth n) i
    (Nat.lt_of_lt_of_le hi (le_two_pow_chunkDepth n))).symm

/-- A composite-element list's element path is the element block's
slot path under the mix-in-length pair's left branch: one `false` in
front. -/
theorem pathBits_list_elem (t : SSZType) (cap i : Nat) (hi : i < cap)
    (hc : ¬ t.isBasicType) :
    (SSZType.list t cap).pathBits [.elem i]
      = false :: Cache.MerkleTree.gindexBits (2 ^ chunkDepth cap + i) := by
  have hstep := stepInto_elem_list t cap i hi
  have hcount := chunkCount_list_composite t cap hc
  have hpos : i * SSZType.itemLength t / BYTES_PER_CHUNK = i := by
    rw [itemLength_of_not_isBasicType t hc]
    show i * 32 / 32 = i
    omega
  have hicd : i < 2 ^ chunkDepth cap :=
    Nat.lt_of_lt_of_le hi (le_two_pow_chunkDepth cap)
  show (match (SSZType.list t cap).stepInto (.elem i) with
    | none => []
    | some (pos, d, s') =>
        (List.range d).reverse.map (pos.testBit ·) ++ s'.pathBits []) = _
  simp only [hstep, hpos, hcount, pathBits_nil, List.append_nil]
  rw [List.range_succ, List.reverse_append, List.reverse_singleton,
    List.map_append, List.map_singleton, Nat.testBit_lt_two_pow hicd,
    gindexBits_pow_add _ _ hicd]
  rfl

end SizzLean.Proofs.Merkle
