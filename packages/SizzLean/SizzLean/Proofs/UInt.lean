import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Proofs.SimpAttrs
import SizzLean.Proofs.Util
import SizzLean.Proofs.UIntWide

/-!
# `SizzLean.Proofs.UInt`: `decode_encode` and size bound for the four `uintN` arms

Per-shape lemmas for `.uintN 8 / 16 / 32 / 64`. The `.uintN 8` arm
closes by `unfold` + `rfl`. The three multi-byte arms route through
the same `Nat`-digit codec `Proofs/UIntWide.lean` proves for the
wide widths: each hand-spelled encoder equals `natToLEBytes w x.toNat`
(`serialize_uintN16_eq_natToLEBytes` and friends), each reader folds
the digits back (`readUInt16LE_append_natToLEBytes` and friends), and
the digit-combine identities (`digits16`, `digits32`, `digits64`)
turn the byte OR/shift lattice into a Horner value over `Nat`.
`decode_encode` carries only the standard kernel axioms.

## Tactics used in this file (annotated on first appearance)

* `unfold f`: replace every occurrence of `f` in the goal by its
  definition's right-hand side. Pure beta/delta reduction; no
  computation is performed.
* `rfl`: close a goal of the form `a = a` after Lean has reduced
  both sides definitionally.
* `omega`: linear integer arithmetic over `Nat`, including `mod` and
  `div` by literals. Every nonlinear product is rewritten into atom
  form (`2 ^ k` reified to its numeral) before `omega` runs.
* `intro x`: move the `∀ x, …` quantifier into the hypothesis
  context so the rest of the proof reasons about a fixed `x`.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Spec
-- `natToLEBytes` is `protected` in `Spec/Serialize.lean` (proof-internal,
-- kept off the general `SizzLean.Spec` surface), so the wildcard `open`
-- above does not bring it into scope; request it explicitly.
open SizzLean.Spec (natToLEBytes)

/-! ### Digit machinery

The little-endian byte lattice, one lemma per width: bytes `b₀ … bₖ`
combine into `UIntN.ofNat (b₀ + 256·(b₁ + …))`. Proved by pushing
both sides through `.toNat` (the `toNat_or` / `toNat_shiftLeft` simp
lemmas from core), peeling the high digit off with
`Nat.two_pow_add_eq_or_of_lt` (a `2^k`-scaled digit has its low bits
zero, so the bitwise OR is the sum), and finishing with `omega`. -/

/-- A `2^k`-scaled digit has its low `k` bits zero, so OR-ing it onto
a value below `2^k` is plain addition. -/
theorem lor_hi (v d k : Nat) (hv : v < 2 ^ k) :
    v ||| d * 2 ^ k = v + d * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm d (2 ^ k), ← Nat.two_pow_add_eq_or_of_lt hv d,
      Nat.add_comm]

/-- Every `UInt8` reads below one byte. -/
theorem u8_lt (b : UInt8) : b.toNat < 256 := by
  have hsz : (UInt8.size : Nat) = 256 := rfl
  have h := b.toNat_lt_size
  rw [hsz] at h
  exact h

/-- Every `UInt16` reads below two bytes. -/
theorem u16_lt (x : UInt16) : x.toNat < 65536 := by
  have h := x.toNat_lt_size
  have hsz : (UInt16.size : Nat) = 65536 := rfl
  rw [hsz] at h
  exact h

/-- Every `UInt32` reads below four bytes. -/
theorem u32_lt (x : UInt32) : x.toNat < 4294967296 := by
  have h := x.toNat_lt_size
  have hsz : (UInt32.size : Nat) = 4294967296 := rfl
  rw [hsz] at h
  exact h

/-- Every `UInt64` reads below eight bytes. -/
theorem u64_lt (x : UInt64) : x.toNat < 18446744073709551616 := by
  have h := x.toNat_lt_size
  have hsz : (UInt64.size : Nat) = 18446744073709551616 := rfl
  rw [hsz] at h
  exact h

/-- Two digits rebuild a `UInt16`. -/
theorem digits16 (b0 b1 : UInt8) :
    (b0.toUInt16 ||| (b1.toUInt16 <<< 8)) = UInt16.ofNat (b0.toNat + 256 * b1.toNat) := by
  refine UInt16.toNat_inj.mp ?_
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  have h16 : (2 : Nat) ^ 16 = 65536 := by decide
  have h0 : b0.toNat < 2 ^ 8 := by rw [h8]; exact u8_lt b0
  have b0' := u8_lt b0
  have b1' := u8_lt b1
  have hshift : (UInt16.toNat 8 % 16) = 8 := by simp
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
    Nat.shiftLeft_eq, UInt16.toNat_ofNat', hshift]
  rw [Nat.mod_eq_of_lt (by rw [h8, h16]; omega),
      Nat.or_comm, Nat.mul_comm b1.toNat (2 ^ 8),
      ← Nat.two_pow_add_eq_or_of_lt h0 b1.toNat,
      Nat.add_comm,
      ← h8,
      Nat.mod_eq_of_lt (by rw [h16]; omega)]

/-- Four digits rebuild a `UInt32`. -/
theorem digits32 (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))
      = UInt32.ofNat (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) := by
  refine UInt32.toNat_inj.mp ?_
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  have h16 : (2 : Nat) ^ 16 = 65536 := by decide
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  have hs8 : (UInt32.toNat 8 % 32) = 8 := by simp
  have hs16 : (UInt32.toNat 16 % 32) = 16 := by simp
  have hs24 : (UInt32.toNat 24 % 32) = 24 := by simp
  have b0' := u8_lt b0
  have b1' := u8_lt b1
  have b2' := u8_lt b2
  have b3' := u8_lt b3
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    Nat.shiftLeft_eq, UInt32.toNat_ofNat', hs8, hs16, hs24]
  rw [Nat.mod_eq_of_lt (by rw [h32]; omega),
      Nat.mod_eq_of_lt (by rw [h16, h32]; omega),
      Nat.mod_eq_of_lt (by rw [h24, h32]; omega)]
  rw [lor_hi b0.toNat b1.toNat 8 b0',
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8) b2.toNat 16 (by rw [h16]; omega),
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) b3.toNat 24
        (by rw [h24]; omega)]
  rw [h8, h16, h24, h32,
      Nat.mod_eq_of_lt (by omega)]
  omega

/-- Eight digits rebuild a `UInt64`. -/
theorem digits64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
      (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))
      = UInt64.ofNat (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
            256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat))))))) := by
  refine UInt64.toNat_inj.mp ?_
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  have h16 : (2 : Nat) ^ 16 = 65536 := by decide
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  have h40 : (2 : Nat) ^ 40 = 1099511627776 := by decide
  have h48 : (2 : Nat) ^ 48 = 281474976710656 := by decide
  have h56 : (2 : Nat) ^ 56 = 72057594037927936 := by decide
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have hs8 : (UInt64.toNat 8 % 64) = 8 := by simp
  have hs16 : (UInt64.toNat 16 % 64) = 16 := by simp
  have hs24 : (UInt64.toNat 24 % 64) = 24 := by simp
  have hs32 : (UInt64.toNat 32 % 64) = 32 := by simp
  have hs40 : (UInt64.toNat 40 % 64) = 40 := by simp
  have hs48 : (UInt64.toNat 48 % 64) = 48 := by simp
  have hs56 : (UInt64.toNat 56 % 64) = 56 := by simp
  have b0' := u8_lt b0
  have b1' := u8_lt b1
  have b2' := u8_lt b2
  have b3' := u8_lt b3
  have b4' := u8_lt b4
  have b5' := u8_lt b5
  have b6' := u8_lt b6
  have b7' := u8_lt b7
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    Nat.shiftLeft_eq, UInt64.toNat_ofNat', hs8, hs16, hs24, hs32, hs40, hs48, hs56]
  rw [Nat.mod_eq_of_lt (by rw [h64]; omega),
      Nat.mod_eq_of_lt (by rw [h16, h64]; omega),
      Nat.mod_eq_of_lt (by rw [h24, h64]; omega),
      Nat.mod_eq_of_lt (by rw [h32, h64]; omega),
      Nat.mod_eq_of_lt (by rw [h40, h64]; omega),
      Nat.mod_eq_of_lt (by rw [h48, h64]; omega),
      Nat.mod_eq_of_lt (by rw [h56, h64]; omega)]
  rw [lor_hi b0.toNat b1.toNat 8 b0',
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8) b2.toNat 16 (by rw [h16]; omega),
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) b3.toNat 24
        (by rw [h24]; omega),
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24) b4.toNat 32
        (by rw [h32]; omega),
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
        b4.toNat * 2 ^ 32) b5.toNat 40 (by rw [h40]; omega),
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
        b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40) b6.toNat 48 (by rw [h48]; omega),
      lor_hi (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
        b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48) b7.toNat 56
        (by rw [h56]; omega)]
  rw [h8, h16, h24, h32, h40, h48, h56, h64,
      Nat.mod_eq_of_lt (by omega)]
  omega

/-! ### Per-byte encoder facts

Each hand-spelled shift byte is the corresponding little-endian
digit, and each lemma is its own one-line lift through `toNat`
(`UInt8.toNat_inj` plus `Nat.shiftRight_eq_div_pow`). The lift
stays per byte because the fixed-width shift operators take a
value of their own width on the right, so a `Nat`-indexed shift
parameter does not typecheck against the `HShiftRight` instances;
one lemma per width and shift position is the smallest form the
elaborator accepts. -/

/-- The `uintN 16` writer's byte 1 is digit 1. -/
theorem u16_byte1 (x : UInt16) : (x >>> 8).toUInt8 = Nat.toUInt8 (x.toNat / 256 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

/-- The `uintN 32` writer's byte `k` is digit `k`, for the three
shifted positions. -/
theorem u32_byte1 (x : UInt32) : (x >>> 8).toUInt8 = Nat.toUInt8 (x.toNat / 256 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u32_byte2 (x : UInt32) : (x >>> 16).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 2 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u32_byte3 (x : UInt32) : (x >>> 24).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 3 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

/-- The `uintN 64` writer's byte `k` is digit `k`, for the seven
shifted positions. -/
theorem u64_byte1 (x : UInt64) : (x >>> 8).toUInt8 = Nat.toUInt8 (x.toNat / 256 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u64_byte2 (x : UInt64) : (x >>> 16).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 2 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u64_byte3 (x : UInt64) : (x >>> 24).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 3 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u64_byte4 (x : UInt64) : (x >>> 32).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 4 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u64_byte5 (x : UInt64) : (x >>> 40).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 5 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u64_byte6 (x : UInt64) : (x >>> 48).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 6 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

theorem u64_byte7 (x : UInt64) : (x >>> 56).toUInt8 = Nat.toUInt8 (x.toNat / 256 ^ 7 % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp [Nat.shiftRight_eq_div_pow]

/-- The unshifted first byte is digit 0, one line per width. -/
theorem u16_byte0 (x : UInt16) : x.toUInt8 = Nat.toUInt8 (x.toNat % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp

theorem u32_byte0 (x : UInt32) : x.toUInt8 = Nat.toUInt8 (x.toNat % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp

theorem u64_byte0 (x : UInt64) : x.toUInt8 = Nat.toUInt8 (x.toNat % 256) := by
  refine UInt8.toNat_inj.mp ?_
  simp

/-- Peeling one more little-endian digit divides by one more 256.
The one division-chain fact the multi-byte encoder bridges need:
`simp only [div_digit_succ, Nat.pow_one]` turns every
`n / 256 ^ k` digit into the `/ 256` chain the codec loop builds. -/
theorem div_digit_succ (n k : Nat) : n / 256 ^ (k + 1) = n / 256 ^ k / 256 := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- The `uintN 16` encoder is `natToLEBytes` at width 2. -/
theorem serialize_uintN16_eq_natToLEBytes (x : UInt16) :
    SSZType.serialize (.uintN 16) x = natToLEBytes 2 x.toNat .empty := by
  have h : SSZType.serialize (.uintN 16) x = uint16LE x := by
    unfold SSZType.serialize; rfl
  rw [h]
  unfold uint16LE
  rw [u16_byte0, u16_byte1]
  rfl

/-- The `uintN 32` encoder is `natToLEBytes` at width 4. -/
theorem serialize_uintN32_eq_natToLEBytes (x : UInt32) :
    SSZType.serialize (.uintN 32) x = natToLEBytes 4 x.toNat .empty := by
  have h : SSZType.serialize (.uintN 32) x = uint32LE x := by
    unfold SSZType.serialize; rfl
  rw [h]
  unfold uint32LE
  rw [u32_byte0, u32_byte1, u32_byte2, u32_byte3]
  simp only [div_digit_succ, Nat.pow_one, natToLEBytes]

/-- The `uint32` writer is the digit codec, the shape the
offset-table bridge in `Proofs/ContainerVar.lean` reads. -/
theorem uint32LE_eq_natToLEBytes (x : UInt32) :
    uint32LE x = natToLEBytes 4 x.toNat .empty := by
  have h := serialize_uintN32_eq_natToLEBytes x
  unfold SSZType.serialize at h
  exact h

/-- The `uintN 64` encoder is `natToLEBytes` at width 8. -/
theorem serialize_uintN64_eq_natToLEBytes (x : UInt64) :
    SSZType.serialize (.uintN 64) x = natToLEBytes 8 x.toNat .empty := by
  have h : SSZType.serialize (.uintN 64) x = uint64LE x := by
    unfold SSZType.serialize; rfl
  rw [h]
  unfold uint64LE
  rw [u64_byte0, u64_byte1, u64_byte2, u64_byte3,
      u64_byte4, u64_byte5, u64_byte6, u64_byte7]
  simp only [div_digit_succ, Nat.pow_one, natToLEBytes]

/-! ### Decoder bridges: the readers fold the digits back

Each reader's byte-OR lattice is first restated as an equation over
the raw bytes (`readUInt16LE_digits` and friends), the bytes are
identified with the digits of `x.toNat`, and the digit lemma turns
the lattice into `UIntN.ofNat` of the Horner value. Stated with an
arbitrary suffix `b` so the offset-table bridge in
`Proofs/ContainerVar.lean` reads its placeholder off the front of a
longer buffer. -/

/-- Byte `i` of `natToLEBytes w n .empty ++ b` is the `i`-th digit,
for `i < w`. Internal stepping stone for the three reader bridges. -/
theorem getElem_natToLEBytes_append (w n i : Nat) (hi : i < w) (b : ByteArray) :
    (natToLEBytes w n .empty ++ b)[i]'(by
        rw [ByteArray.size_append, size_natToLEBytes]; omega) =
      Nat.toUInt8 ((n / 256 ^ i) % 256) := by
  rw [ByteArray.getElem_append_left (by rw [size_natToLEBytes]; omega),
      ← get!_eq_getElem _ _ (by rw [size_natToLEBytes]; omega),
      get!_natToLEBytes_empty w n i hi]

/-- The `uintN 16` reader over raw bytes. -/
theorem readUInt16LE_digits (b : ByteArray) (off : Nat) (h : off + 2 ≤ b.size) :
    readUInt16LE b off =
      some ((b[off]'(by omega)).toUInt16 ||| (b[off + 1]'(by omega)).toUInt16 <<< 8) := by
  unfold readUInt16LE
  rw [dif_pos h]

/-- The `uintN 32` reader over raw bytes. -/
theorem readUInt32LE_digits (b : ByteArray) (off : Nat) (h : off + 4 ≤ b.size) :
    readUInt32LE b off =
      some ((b[off]'(by omega)).toUInt32 ||| (b[off + 1]'(by omega)).toUInt32 <<< 8 |||
        (b[off + 2]'(by omega)).toUInt32 <<< 16 ||| (b[off + 3]'(by omega)).toUInt32 <<< 24) := by
  unfold readUInt32LE
  rw [dif_pos h]

/-- The `uintN 64` reader over raw bytes. The index arithmetic keeps
the definition's own `off + i` shape so the final `rfl` closes the
let-and-beta reduction. -/
theorem readUInt64LE_digits (b : ByteArray) (off : Nat) (h : off + 8 ≤ b.size) :
    readUInt64LE b off =
      some ((b[off + 0]'(by omega)).toUInt64 ||| (b[off + 1]'(by omega)).toUInt64 <<< 8 |||
        (b[off + 2]'(by omega)).toUInt64 <<< 16 ||| (b[off + 3]'(by omega)).toUInt64 <<< 24 |||
        (b[off + 4]'(by omega)).toUInt64 <<< 32 ||| (b[off + 5]'(by omega)).toUInt64 <<< 40 |||
        (b[off + 6]'(by omega)).toUInt64 <<< 48 ||| (b[off + 7]'(by omega)).toUInt64 <<< 56) := by
  unfold readUInt64LE
  rw [dif_pos h]

/-- `(Nat.toUInt8 n).toNat = n % 256`, as a rewrite rule. -/
theorem toUInt8_toNat_digit (n : Nat) : (Nat.toUInt8 n).toNat = n % 256 := by
  simp

/-- Reading a `uintN 16` value back off its own `natToLEBytes` output,
possibly followed by more bytes. -/
theorem readUInt16LE_append_natToLEBytes (x : UInt16) (b : ByteArray) :
    readUInt16LE (natToLEBytes 2 x.toNat .empty ++ b) 0 = some x := by
  have hsize : (natToLEBytes 2 x.toNat .empty).size = 2 := by
    rw [size_natToLEBytes]; simp
  have hlt := u16_lt x
  rw [readUInt16LE_digits _ 0 (by rw [ByteArray.size_append, hsize]; omega),
      getElem_natToLEBytes_append 2 x.toNat 0 (by omega) b,
      getElem_natToLEBytes_append 2 x.toNat 1 (by omega) b,
      digits16]
  congr 1
  rw [UInt16.ofNat_eq_iff_mod_eq_toNat, toUInt8_toNat_digit, toUInt8_toNat_digit]
  omega

/-- Reading a `uintN 32` value back off its own `natToLEBytes` output. -/
theorem readUInt32LE_append_natToLEBytes (x : UInt32) (b : ByteArray) :
    readUInt32LE (natToLEBytes 4 x.toNat .empty ++ b) 0 = some x := by
  have hsize : (natToLEBytes 4 x.toNat .empty).size = 4 := by
    rw [size_natToLEBytes]; simp
  have hlt := u32_lt x
  rw [readUInt32LE_digits _ 0 (by rw [ByteArray.size_append, hsize]; omega),
      getElem_natToLEBytes_append 4 x.toNat 0 (by omega) b,
      getElem_natToLEBytes_append 4 x.toNat 1 (by omega) b,
      getElem_natToLEBytes_append 4 x.toNat 2 (by omega) b,
      getElem_natToLEBytes_append 4 x.toNat 3 (by omega) b,
      digits32]
  congr 1
  rw [UInt32.ofNat_eq_iff_mod_eq_toNat, toUInt8_toNat_digit, toUInt8_toNat_digit,
      toUInt8_toNat_digit, toUInt8_toNat_digit]
  omega

/-- Reading a `uintN 64` value back off its own `natToLEBytes` output. -/
theorem readUInt64LE_append_natToLEBytes (x : UInt64) (b : ByteArray) :
    readUInt64LE (natToLEBytes 8 x.toNat .empty ++ b) 0 = some x := by
  have hsize : (natToLEBytes 8 x.toNat .empty).size = 8 := by
    rw [size_natToLEBytes]; simp
  have hlt := u64_lt x
  rw [readUInt64LE_digits _ 0 (by rw [ByteArray.size_append, hsize]; omega),
      getElem_natToLEBytes_append 8 x.toNat 0 (by omega) b,
      getElem_natToLEBytes_append 8 x.toNat 1 (by omega) b,
      getElem_natToLEBytes_append 8 x.toNat 2 (by omega) b,
      getElem_natToLEBytes_append 8 x.toNat 3 (by omega) b,
      getElem_natToLEBytes_append 8 x.toNat 4 (by omega) b,
      getElem_natToLEBytes_append 8 x.toNat 5 (by omega) b,
      getElem_natToLEBytes_append 8 x.toNat 6 (by omega) b,
      getElem_natToLEBytes_append 8 x.toNat 7 (by omega) b,
      digits64]
  congr 1
  rw [UInt64.ofNat_eq_iff_mod_eq_toNat, toUInt8_toNat_digit, toUInt8_toNat_digit,
      toUInt8_toNat_digit, toUInt8_toNat_digit, toUInt8_toNat_digit, toUInt8_toNat_digit,
      toUInt8_toNat_digit, toUInt8_toNat_digit]
  omega

/-- Suffix-free specialisations used by the roundtrip arms. -/
theorem readUInt16LE_natToLEBytes (x : UInt16) :
    readUInt16LE (natToLEBytes 2 x.toNat .empty) 0 = some x := by
  have h := readUInt16LE_append_natToLEBytes x ByteArray.empty
  rwa [ByteArray.append_empty] at h

theorem readUInt32LE_natToLEBytes (x : UInt32) :
    readUInt32LE (natToLEBytes 4 x.toNat .empty) 0 = some x := by
  have h := readUInt32LE_append_natToLEBytes x ByteArray.empty
  rwa [ByteArray.append_empty] at h

theorem readUInt64LE_natToLEBytes (x : UInt64) :
    readUInt64LE (natToLEBytes 8 x.toNat .empty) 0 = some x := by
  have h := readUInt64LE_append_natToLEBytes x ByteArray.empty
  rwa [ByteArray.append_empty] at h

/-! ### The roundtrip arms -/

/-- Roundtrip for `.uintN 8`.

`serialize (.uintN 8) x = ByteArray.empty.push x` (single byte);
`deserialize (.uintN 8) b = readUInt8At b 0` (reads byte 0, returns
`.ok (·, 1)`). The composition reduces to `.ok (x, 1) = .ok (x, 1)`
after one `unfold`, closed by `rfl`. -/
theorem decode_encode_uintN8 : ∀ (x : UInt8),
    SSZType.deserialize (.uintN 8) (SSZType.serialize (.uintN 8) x) =
      .ok (x, (SSZType.serialize (.uintN 8) x).size) := by
  intro x
  unfold SSZType.deserialize SSZType.serialize
  rfl

/-- Roundtrip for `.uintN 16`. The encoder is the digit codec
(`serialize_uintN16_eq_natToLEBytes`), the reader folds the digits
back (`readUInt16LE_natToLEBytes`), and the residual `UInt16.ofNat`
identity closes by `x.toNat < 65536`. -/
theorem decode_encode_uintN16 : ∀ (x : UInt16),
    SSZType.deserialize (.uintN 16) (SSZType.serialize (.uintN 16) x) =
      .ok (x, (SSZType.serialize (.uintN 16) x).size) := by
  intro x
  rw [serialize_uintN16_eq_natToLEBytes]
  unfold SSZType.deserialize
  rw [readUInt16LE_natToLEBytes, size_natToLEBytes]
  simp

/-- Roundtrip for `.uintN 32`. Same digit-codec recipe as `uintN16`
at width 4. -/
theorem decode_encode_uintN32 : ∀ (x : UInt32),
    SSZType.deserialize (.uintN 32) (SSZType.serialize (.uintN 32) x) =
      .ok (x, (SSZType.serialize (.uintN 32) x).size) := by
  intro x
  rw [serialize_uintN32_eq_natToLEBytes]
  unfold SSZType.deserialize
  rw [readUInt32LE_natToLEBytes, size_natToLEBytes]
  simp

/-- Roundtrip for `.uintN 64`. Same digit-codec recipe as `uintN16`
at width 8. -/
theorem decode_encode_uintN64 : ∀ (x : UInt64),
    SSZType.deserialize (.uintN 64) (SSZType.serialize (.uintN 64) x) =
      .ok (x, (SSZType.serialize (.uintN 64) x).size) := by
  intro x
  rw [serialize_uintN64_eq_natToLEBytes]
  unfold SSZType.deserialize
  rw [readUInt64LE_natToLEBytes, size_natToLEBytes]
  simp

/-! ### Size bounds: each `(serialize …).size = (N+7)/8 = maxByteLength` -/

/-- Per-`UInt8` size bound. Both sides reduce to `1`. -/
theorem encode_size_le_max_uintN8 : ∀ (x : UInt8),
    (SSZType.serialize (.uintN 8) x).size ≤ SSZType.maxByteLength (.uintN 8) := by
  intro x
  simp [SSZType.serialize, SSZType.maxByteLength, ByteArray.size_push,
        ByteArray.size_empty]

/-- Per-`UInt16` size bound. Both sides reduce to `2`. -/
theorem encode_size_le_max_uintN16 : ∀ (x : UInt16),
    (SSZType.serialize (.uintN 16) x).size ≤ SSZType.maxByteLength (.uintN 16) := by
  intro x
  rw [serialize_uintN16_eq_natToLEBytes, size_natToLEBytes]
  simp [SSZType.maxByteLength, ByteArray.size_empty]

/-- Per-`UInt32` size bound. Both sides reduce to `4`. -/
theorem encode_size_le_max_uintN32 : ∀ (x : UInt32),
    (SSZType.serialize (.uintN 32) x).size ≤ SSZType.maxByteLength (.uintN 32) := by
  intro x
  rw [serialize_uintN32_eq_natToLEBytes, size_natToLEBytes]
  simp [SSZType.maxByteLength, ByteArray.size_empty]

/-- Per-`UInt64` size bound. Both sides reduce to `8`. -/
theorem encode_size_le_max_uintN64 : ∀ (x : UInt64),
    (SSZType.serialize (.uintN 64) x).size ≤ SSZType.maxByteLength (.uintN 64) := by
  intro x
  rw [serialize_uintN64_eq_natToLEBytes, size_natToLEBytes]
  simp [SSZType.maxByteLength, ByteArray.size_empty]

end SizzLean.Proofs
