import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SimpAttrs

/-!
# `SizzLean.Proofs.BitPack`: the bit-packing inverse and the bit-shape arms

Proves that LSB-first bit packing (`Spec/Serialize.lean`) and
unpacking (`Spec/Deserialize.lean`) are mutual inverses, then
closes `decode_encode` and `encode_size_le_max` for the
`.bitvector n` and `.bitlist cap` arms. This is the file that
`Serialize.lean:211` and `Deserialize.lean:169` promised when they
made `bitsToByte`, `packBitsLE`, `byteToBits`, and
`unpackBitsLEAux` public.

## Lemma path

1. **Single-byte inverse** (`byteToBits_bitsToByte`): reading the
   8 LSB-first bits of a packed byte returns the packed chunk plus
   zero padding. Bit-level facts about one byte are finite, so the
   whole family closes by `decide` after case analysis on the
   chunk shape: `bitsToByte_shiftRight_length` (bits at or above
   the chunk length are unset) and `msbPos_bitsToByte_append_true`
   (a trailing `true` bit is the most significant set bit) follow
   the same recipe.
2. **Byte-stream lift** (`packBitsLE_unpackBitsLEAux_inverse`):
   the single-byte inverse lifted over `packBitsLE`'s
   8-bits-per-byte recursion, with the padding characterised as
   `List.replicate _ false` so consumers can strip it with
   `List.take_left'`. Companions: `size_packBitsLE` (exact output
   size) and `packBitsLE_last_byte` (the final byte is the packed
   final chunk, which the decoders' padding / delimiter checks
   inspect).
3. **Numeric bridge** (`bitsToNat_range_testBit`): the decoder
   rebuilds a `BitVec` by folding unpacked bits into a `Nat`;
   this identifies that fold with `Nat.testBit`, so
   `BitVec.ofNat_toNat` closes the value roundtrip.
4. **Arm closure**: `decode_encode_bitvector`,
   `decode_encode_bitlist`, and the two `encode_size_le_max_*`
   bounds, walking the decoders' guard branches with the
   lemmas above. `Proofs/Roundtrip.lean` and `Proofs/SizeBound.lean`
   dispatch to these.

## Proof style notes

* The list matches enumerate chunk shapes of length 0 through 7
  plus the 8-cons shape, mirroring `packBitsLE`'s own match
  structure, so each equation of the spec function applies
  directly and the recursive arm descends on a strict subterm
  (`rest`), which the structural checker accepts.
* `revert … ; decide`: `decide` needs a closed decidable
  proposition; reverting the pattern-bound `Bool` variables turns
  the per-shape goal into `∀ (b₀ … : Bool), …`, a finite
  conjunction the kernel evaluates. No `native_decide`, so no
  compiler axiom enters the proof path (per CLAUDE.md's tactic
  guidance for non-hash decidable goals).
* `ByteArray.get!` (used by `unpackBitsLEAux`) and the
  bounds-checked `b[i]'h` (used by the decoders) are bridged once
  in `get!_eq_getElem`; everything downstream works with the
  total `get!` form.
-/

set_option autoImplicit false
-- The `decide` families below evaluate up to 2⁸ byte-level cases
-- per shape; give the elaborator room.
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-! ### ByteArray indexing bridges -/

/-- `get!` agrees with the bounds-checked `b[i]` when in range.
`get!` unfolds to `b.data[i]!`, whose panicking branch is
irrelevant here; `getElem!_pos` (core) discharges it against the
supplied bound. -/
theorem get!_eq_getElem (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.get! i = b[i] := by
  show b.data[i]! = b[i]
  rw [ByteArray.getElem_eq_getElem_data]
  exact getElem!_pos b.data i h

/-- Reading index 0 of a single-byte array returns that byte. -/
theorem get!_push_zero (x : UInt8) : (ByteArray.empty.push x).get! 0 = x := by
  rw [get!_eq_getElem _ _ (by simp [ByteArray.size_push, ByteArray.size_empty])]
  rfl

/-! ### Single-byte inverses (the `decide` family)

Every lemma in this section quantifies over one packed chunk of
at most 8 booleans, a finite domain the kernel can enumerate. -/

/-- Unpacking a packed chunk of at most 8 bits returns the chunk,
zero-padded to the full byte width. The padding is `false` bits
because `bitsToByte` never sets a position at or beyond the chunk
length. -/
theorem byteToBits_bitsToByte : ∀ (bs : List Bool), bs.length ≤ 8 →
    byteToBits (bitsToByte bs 0 0) = bs ++ List.replicate (8 - bs.length) false
  | [], _ => by decide
  | [b0], _ => by revert b0; decide
  | [b0, b1], _ => by revert b0 b1; decide
  | [b0, b1, b2], _ => by revert b0 b1 b2; decide
  | [b0, b1, b2, b3], _ => by revert b0 b1 b2 b3; decide
  | [b0, b1, b2, b3, b4], _ => by revert b0 b1 b2 b3 b4; decide
  | [b0, b1, b2, b3, b4, b5], _ => by revert b0 b1 b2 b3 b4 b5; decide
  | [b0, b1, b2, b3, b4, b5, b6], _ => by revert b0 b1 b2 b3 b4 b5 b6; decide
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => by
      revert b0 b1 b2 b3 b4 b5 b6 b7; decide
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest, h => by
      simp only [List.length_cons] at h
      omega

/-- Exact-width corollary of `byteToBits_bitsToByte`: a full
8-bit chunk roundtrips with no padding. Kept as its own `decide`
so the 8-cons arm of the stream lift can cite it without
`List.append_nil` cleanup. -/
theorem byteToBits_bitsToByte_eight (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    byteToBits (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  revert b0 b1 b2 b3 b4 b5 b6 b7; decide

/-- Bits at or above the chunk length are unset: shifting the
packed byte right by the chunk length yields zero. This is the
fact behind the bitvector decoder's zero-padding validation.
Restricted to `length < 8` because a `UInt8` shift by 8 wraps to
a shift by 0. -/
theorem bitsToByte_shiftRight_length : ∀ (bs : List Bool), bs.length < 8 →
    bitsToByte bs 0 0 >>> Nat.toUInt8 bs.length = 0
  | [], _ => by decide
  | [b0], _ => by revert b0; decide
  | [b0, b1], _ => by revert b0 b1; decide
  | [b0, b1, b2], _ => by revert b0 b1 b2; decide
  | [b0, b1, b2, b3], _ => by revert b0 b1 b2 b3; decide
  | [b0, b1, b2, b3, b4], _ => by revert b0 b1 b2 b3 b4; decide
  | [b0, b1, b2, b3, b4, b5], _ => by revert b0 b1 b2 b3 b4 b5; decide
  | [b0, b1, b2, b3, b4, b5, b6], _ => by revert b0 b1 b2 b3 b4 b5 b6; decide
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h => by
      simp only [List.length_cons] at h
      omega

/-- A packed chunk ending in a `true` bit has its most significant
set bit exactly at the chunk's data length. This is the bitlist
delimiter-recovery fact: `msbPos` on the final byte finds the
delimiter, whatever the data bits below it are. -/
theorem msbPos_bitsToByte_append_true : ∀ (bs : List Bool), bs.length ≤ 7 →
    msbPos (bitsToByte (bs ++ [true]) 0 0) = some bs.length
  | [], _ => by decide
  | [b0], _ => by revert b0; decide
  | [b0, b1], _ => by revert b0 b1; decide
  | [b0, b1, b2], _ => by revert b0 b1 b2; decide
  | [b0, b1, b2, b3], _ => by revert b0 b1 b2 b3; decide
  | [b0, b1, b2, b3, b4], _ => by revert b0 b1 b2 b3 b4; decide
  | [b0, b1, b2, b3, b4, b5], _ => by revert b0 b1 b2 b3 b4 b5; decide
  | [b0, b1, b2, b3, b4, b5, b6], _ => by revert b0 b1 b2 b3 b4 b5 b6; decide
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h => by
      simp only [List.length_cons] at h
      omega

/-! ### The byte-stream lift -/

/-- `packBitsLE` emits exactly `⌈length/8⌉` bytes. The match
enumerates the same shapes as `packBitsLE` itself so each spec
equation applies directly; the 8-cons arm recurses on `rest`. -/
theorem size_packBitsLE : ∀ (bs : List Bool),
    (packBitsLE bs).size = (bs.length + 7) / 8
  | [] => by simp [packBitsLE]
  | [b0] => by simp [packBitsLE, ByteArray.size_push]
  | [b0, b1] => by simp [packBitsLE, ByteArray.size_push]
  | [b0, b1, b2] => by simp [packBitsLE, ByteArray.size_push]
  | [b0, b1, b2, b3] => by simp [packBitsLE, ByteArray.size_push]
  | [b0, b1, b2, b3, b4] => by simp [packBitsLE, ByteArray.size_push]
  | [b0, b1, b2, b3, b4, b5] => by simp [packBitsLE, ByteArray.size_push]
  | [b0, b1, b2, b3, b4, b5, b6] => by simp [packBitsLE, ByteArray.size_push]
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => by
      have ih := size_packBitsLE rest
      simp only [packBitsLE, List.length_cons]
      rw [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty, ih]
      omega

/-- Unpacking one pushed byte reads it back through `byteToBits`. -/
theorem unpackBitsLEAux_single (byte : UInt8) :
    unpackBitsLEAux (ByteArray.empty.push byte) 1 0 = byteToBits byte := by
  simp only [unpackBitsLEAux, get!_push_zero, List.append_nil]

/-- Unpacking is insensitive to an already-consumed prefix:
reading `k` bytes of `a ++ b` starting at `a.size + off` reads
them from `b` at `off`. The bound `off + k ≤ b.size` keeps every
`get!` in range so the two sides read the same bytes. -/
theorem unpackBitsLEAux_append_shift (a b : ByteArray) :
    ∀ (k off : Nat), off + k ≤ b.size →
      unpackBitsLEAux (a ++ b) k (a.size + off) = unpackBitsLEAux b k off
  | 0, _, _ => by simp [unpackBitsLEAux]
  | k + 1, off, h => by
      have h_off : off < b.size := by omega
      have h_tot : a.size + off < (a ++ b).size := by
        rw [ByteArray.size_append]; omega
      have h_byte : (a ++ b).get! (a.size + off) = b.get! off := by
        rw [get!_eq_getElem _ _ h_tot, get!_eq_getElem _ _ h_off,
            ByteArray.getElem_append_right (by omega)]
        simp [Nat.add_sub_cancel_left]
      have h_rec := unpackBitsLEAux_append_shift a b k (off + 1) (by omega)
      simp only [unpackBitsLEAux, h_byte]
      rw [show a.size + off + 1 = a.size + (off + 1) from Nat.add_assoc a.size off 1,
          h_rec]

/-- Shared closing step for the sub-byte shapes of the stream
inverse: one packed byte, unpacked and identified with the chunk
plus padding. -/
private theorem unpack_pack_small (bs : List Bool) (h_le : bs.length ≤ 7)
    (h_pack : packBitsLE bs = ByteArray.empty.push (bitsToByte bs 0 0)) :
    unpackBitsLEAux (packBitsLE bs) ((bs.length + 7) / 8) 0 =
      bs ++ List.replicate ((bs.length + 7) / 8 * 8 - bs.length) false := by
  by_cases h_nil : bs = []
  · subst h_nil
    simp [packBitsLE, unpackBitsLEAux]
  · have h_pos : 0 < bs.length := List.length_pos_iff.mpr h_nil
    have h_count : (bs.length + 7) / 8 = 1 := by omega
    rw [h_count, show 1 * 8 - bs.length = 8 - bs.length from by omega,
        h_pack, unpackBitsLEAux_single, byteToBits_bitsToByte bs (by omega)]

/-- **The core inverse** (issue #9, deliverable 1): unpacking
`⌈length/8⌉` bytes of a packed bit list recovers the bits, plus
`false` padding filling the final byte. Consumers strip the
padding with `List.take_left'` since the data length is theirs to
know (bitvector: the schema's `n`; bitlist: the recovered
delimiter position). -/
theorem packBitsLE_unpackBitsLEAux_inverse : ∀ (bs : List Bool),
    unpackBitsLEAux (packBitsLE bs) ((bs.length + 7) / 8) 0 =
      bs ++ List.replicate ((bs.length + 7) / 8 * 8 - bs.length) false
  | [] => by simp [packBitsLE, unpackBitsLEAux]
  | [b0] => unpack_pack_small _ (by simp) (by simp [packBitsLE])
  | [b0, b1] => unpack_pack_small _ (by simp) (by simp [packBitsLE])
  | [b0, b1, b2] => unpack_pack_small _ (by simp) (by simp [packBitsLE])
  | [b0, b1, b2, b3] => unpack_pack_small _ (by simp) (by simp [packBitsLE])
  | [b0, b1, b2, b3, b4] => unpack_pack_small _ (by simp) (by simp [packBitsLE])
  | [b0, b1, b2, b3, b4, b5] => unpack_pack_small _ (by simp) (by simp [packBitsLE])
  | [b0, b1, b2, b3, b4, b5, b6] => unpack_pack_small _ (by simp) (by simp [packBitsLE])
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => by
      have ih := packBitsLE_unpackBitsLEAux_inverse rest
      have h_size_rest := size_packBitsLE rest
      have h_pack : packBitsLE (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
          (ByteArray.empty.push (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0)) ++
            packBitsLE rest := by
        simp [packBitsLE]
      have h_count :
          ((b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest).length + 7) / 8 =
            (rest.length + 7) / 8 + 1 := by
        simp only [List.length_cons]; omega
      rw [h_pack, h_count]
      -- One step of `unpackBitsLEAux` (count matches the `k + 1` equation).
      simp only [unpackBitsLEAux]
      -- The first byte of the append is the packed head chunk.
      have h_get :
          ((ByteArray.empty.push (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0)) ++
              packBitsLE rest).get! 0 =
            bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0 := by
        rw [get!_eq_getElem _ _
              (by rw [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty]
                  omega),
            ByteArray.getElem_append_left
              (by simp [ByteArray.size_push, ByteArray.size_empty])]
        rfl
      rw [h_get, byteToBits_bitsToByte_eight]
      -- The remaining count reads entirely from `packBitsLE rest`;
      -- shift the offset past the head byte and apply the IH.
      have h_shift :
          unpackBitsLEAux
              ((ByteArray.empty.push (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0)) ++
                packBitsLE rest)
              ((rest.length + 7) / 8) (0 + 1) =
            unpackBitsLEAux (packBitsLE rest) ((rest.length + 7) / 8) 0 := by
        have h := unpackBitsLEAux_append_shift
          (ByteArray.empty.push (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0))
          (packBitsLE rest) ((rest.length + 7) / 8) 0 (by rw [h_size_rest]; omega)
        simpa [ByteArray.size_push, ByteArray.size_empty] using h
      rw [h_shift, ih]
      -- Reconcile the cons chain and the two padding widths.
      have h_pad : ((rest.length + 7) / 8 + 1) * 8 -
            (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest).length =
          (rest.length + 7) / 8 * 8 - rest.length := by
        simp only [List.length_cons]; omega
      rw [h_pad]
      simp [List.cons_append]

/-- The final byte of a packed stream is the packed final chunk.
The decoders inspect this byte: the bitvector decoder validates
its padding bits, the bitlist decoder locates the delimiter in
it. -/
theorem packBitsLE_last_byte : ∀ (bs : List Bool), bs ≠ [] →
    (packBitsLE bs).get! ((bs.length + 7) / 8 - 1) =
      bitsToByte (bs.drop (8 * ((bs.length + 7) / 8 - 1))) 0 0
  | [], h => absurd rfl h
  | [b0], _ => by revert b0; decide
  | [b0, b1], _ => by revert b0 b1; decide
  | [b0, b1, b2], _ => by revert b0 b1 b2; decide
  | [b0, b1, b2, b3], _ => by revert b0 b1 b2 b3; decide
  | [b0, b1, b2, b3, b4], _ => by revert b0 b1 b2 b3 b4; decide
  | [b0, b1, b2, b3, b4, b5], _ => by revert b0 b1 b2 b3 b4 b5; decide
  | [b0, b1, b2, b3, b4, b5, b6], _ => by revert b0 b1 b2 b3 b4 b5 b6; decide
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ => by
      have h_pack : packBitsLE (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
          (ByteArray.empty.push (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0)) ++
            packBitsLE rest := by
        simp [packBitsLE]
      cases rest with
      | nil =>
          -- Exactly one full byte: index 0, the whole list is the chunk.
          revert b0 b1 b2 b3 b4 b5 b6 b7; decide
      | cons r rs =>
          have ih := packBitsLE_last_byte (r :: rs) (by simp)
          have h_size_rest := size_packBitsLE (r :: rs)
          -- Index arithmetic: the head byte shifts everything by one.
          have h_idx :
              ((b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r :: rs).length + 7) / 8 - 1 =
                (((r :: rs).length + 7) / 8 - 1) + 1 := by
            simp only [List.length_cons]; omega
          have h_pos : 0 < ((r :: rs).length + 7) / 8 := by
            simp only [List.length_cons]; omega
          rw [h_pack, h_idx]
          -- Reading past the singleton prefix lands in `packBitsLE (r :: rs)`.
          have h_read :
              ((ByteArray.empty.push (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0)) ++
                  packBitsLE (r :: rs)).get! ((((r :: rs).length + 7) / 8 - 1) + 1) =
                (packBitsLE (r :: rs)).get! (((r :: rs).length + 7) / 8 - 1) := by
            have h_in : (((r :: rs).length + 7) / 8 - 1) + 1 <
                ((ByteArray.empty.push (bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0)) ++
                  packBitsLE (r :: rs)).size := by
              rw [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
                  h_size_rest]
              omega
            have h_in' : ((r :: rs).length + 7) / 8 - 1 < (packBitsLE (r :: rs)).size := by
              rw [h_size_rest]; omega
            rw [get!_eq_getElem _ _ h_in, get!_eq_getElem _ _ h_in',
                ByteArray.getElem_append_right
                  (by simp [ByteArray.size_push, ByteArray.size_empty])]
            simp [ByteArray.size_push, ByteArray.size_empty]
          rw [h_read, ih]
          -- The dropped prefix on the right shrinks by the 8 head bits.
          have h_drop :
              (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r :: rs).drop
                  (8 * ((((r :: rs).length + 7) / 8 - 1) + 1)) =
                (r :: rs).drop (8 * (((r :: rs).length + 7) / 8 - 1)) := by
            rw [show 8 * ((((r :: rs).length + 7) / 8 - 1) + 1) =
                  8 * (((r :: rs).length + 7) / 8 - 1) + 8 by omega]
            rw [Nat.add_comm, ← List.drop_drop]
            simp
          rw [h_drop]

/-! ### Bits-to-Nat bridge -/

/-- The decoder's bit fold agrees with `Nat.testBit` sampling:
folding the low `n` test bits of `m` rebuilds `m mod 2ⁿ`. The
step case rewrites `List.range (n+1)` head-first
(`List.range_succ_eq_map`) so the fold's LSB-first orientation
lines up with `testBit`'s, then `Nat.mod_mul` splits the modulus
`2·2ⁿ` into low bit plus shifted remainder. -/
theorem bitsToNat_range_testBit : ∀ (n m : Nat),
    bitsToNat ((List.range n).map (fun i => Nat.testBit m i)) = m % 2 ^ n
  | 0, m => by simp [bitsToNat, Nat.mod_one]
  | n + 1, m => by
      rw [List.range_succ_eq_map]
      have h_fun : ((fun i => Nat.testBit m i) ∘ Nat.succ) =
          (fun i => Nat.testBit (m / 2) i) := by
        funext i
        simp [Function.comp, Nat.succ_eq_add_one, Nat.testBit_add_one]
      simp only [List.map_cons, List.map_map, h_fun]
      show (if Nat.testBit m 0 then 1 else 0) + 2 * _ = _
      rw [bitsToNat_range_testBit n (m / 2),
          Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mod_mul]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [Nat.testBit_zero, h]

/-- Specialisation to a bitvector's LSB-first bit samples:
`BitVec.getLsbD` is `Nat.testBit` on `toNat` by definition, and
`toNat < 2ⁿ` collapses the modulus. -/
theorem bitsToNat_getLsbD_range (n : Nat) (bv : BitVec n) :
    bitsToNat ((List.range n).map (fun i => bv.getLsbD i)) = bv.toNat := by
  have h : (fun i => bv.getLsbD i) = (fun i => Nat.testBit bv.toNat i) := rfl
  rw [h, bitsToNat_range_testBit, Nat.mod_eq_of_lt bv.isLt]

/-! ### The bitvector arm -/

/-- Exact serialized size of a bitvector: `⌈n/8⌉` bytes. Cited by
the `bitvector` arm of `size_serialize_eq_fixedByteSize`
(`Proofs/SerializeSize.lean`) since `.bitvector` is a fixed-size
shape admissible inside vectors, lists, and containers. -/
theorem size_serialize_bitvector (n : Nat) (bv : BitVec n) :
    (SSZType.serialize (.bitvector n) bv).size = (n + 7) / 8 := by
  unfold SSZType.serialize bitvecToBytes
  rw [size_packBitsLE]
  simp

/-- Roundtrip for `.bitvector n`, `n > 0` (issue #9, deliverable
2). The proof walks `deserializeBitvector`'s branches: the size
check closes by `size_packBitsLE`; the zero-padding guard closes
by `packBitsLE_last_byte` + `bitsToByte_shiftRight_length`; the
value rebuild closes by the core inverse +
`bitsToNat_getLsbD_range` + `BitVec.ofNat_toNat`. -/
theorem decode_encode_bitvector (n : Nat) (h_pos : 0 < n) (bv : BitVec n) :
    SSZType.deserialize (.bitvector n) (SSZType.serialize (.bitvector n) bv) =
      .ok (bv, (SSZType.serialize (.bitvector n) bv).size) := by
  -- Fix the encoder output and its size once.
  have h_len : ((List.range n).map (fun i => bv.getLsbD i)).length = n := by simp
  have h_ser : SSZType.serialize (.bitvector n) bv =
      packBitsLE ((List.range n).map (fun i => bv.getLsbD i)) := by
    unfold SSZType.serialize bitvecToBytes
    rfl
  have h_size : (packBitsLE ((List.range n).map (fun i => bv.getLsbD i))).size =
      (n + 7) / 8 := by
    rw [size_packBitsLE, h_len]
  -- The decoded bit prefix is exactly the encoder's input bits.
  have h_take : (unpackBitsLEAux (packBitsLE ((List.range n).map (fun i => bv.getLsbD i)))
        ((n + 7) / 8) 0).take n =
      (List.range n).map (fun i => bv.getLsbD i) := by
    have h_inv := packBitsLE_unpackBitsLEAux_inverse
      ((List.range n).map (fun i => bv.getLsbD i))
    rw [h_len] at h_inv
    rw [h_inv, List.take_left' h_len]
  have h_val : BitVec.ofNat n (bitsToNat ((List.range n).map (fun i => bv.getLsbD i))) =
      bv := by
    rw [bitsToNat_getLsbD_range, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [h_ser, h_size]
  unfold SSZType.deserialize
  rw [deserializeBitvector, dif_neg (by omega : ¬ n = 0), dif_pos h_size]
  by_cases h_u : (n + 7) / 8 * 8 - n > 0
  · -- Partial final byte: the zero-padding guard runs. Identify the
    -- last byte with the packed final chunk, whose high bits are unset.
    rw [if_pos h_u]
    have h_ne : (List.range n).map (fun i => bv.getLsbD i) ≠ [] := by
      intro h_con
      have := congrArg List.length h_con
      rw [h_len] at this
      simp at this
      omega
    have h_last := packBitsLE_last_byte _ h_ne
    rw [h_len] at h_last
    have h_chunk_len :
        (((List.range n).map (fun i => bv.getLsbD i)).drop (8 * ((n + 7) / 8 - 1))).length =
          n - 8 * ((n + 7) / 8 - 1) := by
      rw [List.length_drop, h_len]
    -- The guard's shift amount is the final chunk's length.
    have h_shift0 :
        bitsToByte (((List.range n).map (fun i => bv.getLsbD i)).drop
            (8 * ((n + 7) / 8 - 1))) 0 0 >>>
          Nat.toUInt8 (8 - ((n + 7) / 8 * 8 - n)) = 0 := by
      rw [show 8 - ((n + 7) / 8 * 8 - n) =
            (((List.range n).map (fun i => bv.getLsbD i)).drop
              (8 * ((n + 7) / 8 - 1))).length by rw [h_chunk_len]; omega]
      exact bitsToByte_shiftRight_length _ (by rw [h_chunk_len]; omega)
    -- Convert the goal's bounds-checked read into `get!` form and rewrite.
    have h_lastByte : ∀ (hlt : (packBitsLE ((List.range n).map (fun i => bv.getLsbD i))).size - 1 <
          (packBitsLE ((List.range n).map (fun i => bv.getLsbD i))).size),
        (packBitsLE ((List.range n).map (fun i => bv.getLsbD i)))[
            (packBitsLE ((List.range n).map (fun i => bv.getLsbD i))).size - 1]'hlt =
          bitsToByte (((List.range n).map (fun i => bv.getLsbD i)).drop
            (8 * ((n + 7) / 8 - 1))) 0 0 := by
      intro hlt
      rw [← get!_eq_getElem _ _ hlt, h_size]
      exact h_last
    simp only [h_lastByte, h_shift0]
    simp only [ne_eq, UInt8.zero_and, not_true_eq_false, ite_false]
    simp only [h_take, h_val]
  · -- The bit width fills its bytes exactly: no guard.
    rw [if_neg h_u]
    simp only [h_take, h_val]

/-! ### The bitlist arm -/

/-- Roundtrip for `.bitlist cap` (issue #9, deliverable 3). The
encoder appends the delimiter bit and packs;
`msbPos_bitsToByte_append_true` recovers its position from the
final byte, which pins the decoded data length to the original
`size`, and the core inverse returns the data bits. -/
theorem decode_encode_bitlist (cap : Nat) (xs : { bs : Array Bool // bs.size ≤ cap }) :
    SSZType.deserialize (.bitlist cap) (SSZType.serialize (.bitlist cap) xs) =
      .ok (xs, (SSZType.serialize (.bitlist cap) xs).size) := by
  have h_len : xs.val.toList.length = xs.val.size := Array.length_toList
  have h_ser : SSZType.serialize (.bitlist cap) xs =
      packBitsLE (xs.val.toList ++ [true]) := by
    unfold SSZType.serialize bitlistToBytes
    rfl
  have h_bits_len : (xs.val.toList ++ [true]).length = xs.val.size + 1 := by
    simp [h_len]
  have h_size : (packBitsLE (xs.val.toList ++ [true])).size = (xs.val.size + 8) / 8 := by
    rw [size_packBitsLE, h_bits_len]
  have h_size_pos : 0 < (xs.val.size + 8) / 8 := by omega
  rw [h_ser, h_size]
  unfold SSZType.deserialize
  rw [deserializeBitlist, dif_neg (by rw [h_size]; omega)]
  -- Identify the final byte: the packed final data chunk plus the
  -- delimiter bit.
  have h_ne : xs.val.toList ++ [true] ≠ [] := by simp
  have h_last := packBitsLE_last_byte _ h_ne
  rw [h_bits_len] at h_last
  have h_prefix_le : 8 * ((xs.val.size + 1 + 7) / 8 - 1) ≤ xs.val.toList.length := by
    rw [h_len]; omega
  have h_drop : (xs.val.toList ++ [true]).drop (8 * ((xs.val.size + 1 + 7) / 8 - 1)) =
      xs.val.toList.drop (8 * ((xs.val.size + 1 + 7) / 8 - 1)) ++ [true] :=
    List.drop_append_of_le_length h_prefix_le
  rw [h_drop] at h_last
  have h_chunk_len : (xs.val.toList.drop (8 * ((xs.val.size + 1 + 7) / 8 - 1))).length =
      xs.val.size % 8 := by
    rw [List.length_drop, h_len]; omega
  have h_msb := msbPos_bitsToByte_append_true
    (xs.val.toList.drop (8 * ((xs.val.size + 1 + 7) / 8 - 1)))
    (by rw [h_chunk_len]; omega)
  rw [h_chunk_len] at h_msb
  -- Read the goal's bounds-checked last byte through `get!`.
  have h_lastByte : ∀ (hlt : (packBitsLE (xs.val.toList ++ [true])).size - 1 <
        (packBitsLE (xs.val.toList ++ [true])).size),
      (packBitsLE (xs.val.toList ++ [true]))[
          (packBitsLE (xs.val.toList ++ [true])).size - 1]'hlt =
        bitsToByte (xs.val.toList.drop (8 * ((xs.val.size + 1 + 7) / 8 - 1)) ++ [true]) 0 0 := by
    intro hlt
    rw [← get!_eq_getElem _ _ hlt, h_size,
        show (xs.val.size + 8) / 8 - 1 = (xs.val.size + 1 + 7) / 8 - 1 by omega]
    exact h_last
  simp only [h_lastByte, h_msb]
  -- The recovered total bit count is the original data length.
  have h_total : ((packBitsLE (xs.val.toList ++ [true])).size - 1) * 8 + xs.val.size % 8 =
      xs.val.size := by
    rw [h_size]; omega
  rw [h_total, if_neg (by omega : ¬ xs.val.size > cap)]
  -- Unpack and take back the data bits.
  have h_take : (unpackBitsLEAux (packBitsLE (xs.val.toList ++ [true]))
        (packBitsLE (xs.val.toList ++ [true])).size 0).take xs.val.size =
      xs.val.toList := by
    have h_inv := packBitsLE_unpackBitsLEAux_inverse (xs.val.toList ++ [true])
    rw [h_bits_len] at h_inv
    rw [h_size, show (xs.val.size + 8) / 8 = (xs.val.size + 1 + 7) / 8 by omega, h_inv,
        List.append_assoc, List.take_left' h_len]
  rw [h_take]
  simp only [Array.toArray_toList]
  rw [dif_pos xs.property, h_size]

/-! ### Size bounds for the two arms -/

/-- Size bound for `.bitvector n`: the serialized size *is* the
schema bound `⌈n/8⌉`. -/
theorem encode_size_le_max_bitvector (n : Nat) (bv : BitVec n) :
    (SSZType.serialize (.bitvector n) bv).size ≤
      SSZType.maxByteLength (.bitvector n) := by
  rw [size_serialize_bitvector]
  unfold SSZType.maxByteLength
  exact Nat.le_refl _

/-- Size bound for `.bitlist cap`: `size ≤ cap` data bits plus the
delimiter fit inside the schema bound `⌈(cap+1)/8⌉`. -/
theorem encode_size_le_max_bitlist (cap : Nat) (xs : { bs : Array Bool // bs.size ≤ cap }) :
    (SSZType.serialize (.bitlist cap) xs).size ≤
      SSZType.maxByteLength (.bitlist cap) := by
  have h_ser : SSZType.serialize (.bitlist cap) xs =
      packBitsLE (xs.val.toList ++ [true]) := by
    unfold SSZType.serialize bitlistToBytes
    rfl
  have h_len : xs.val.toList.length = xs.val.size := Array.length_toList
  have h_le := xs.property
  rw [h_ser, size_packBitsLE]
  unfold SSZType.maxByteLength
  simp only [List.length_append, List.length_cons, List.length_nil, h_len]
  omega

end SizzLean.Proofs
