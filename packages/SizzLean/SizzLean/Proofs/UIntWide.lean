import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SimpAttrs

/-!
# `SizzLean.Proofs.UIntWide`: `decode_encode` and size bound for `uintN 128 / 256`

The four narrow integer widths (`uintN 8/16/32/64`, in
`Proofs/UInt.lean`) serialise through fully-unrolled fixed-width
LE writers/readers (`uint16LE`, `readUInt16LE`, …) and close by
`bv_decide`, which bit-blasts the residual `UInt N` identity and
adds one `Lean.ofReduceBool` axiom per arm.

The two wide widths take a different route. Their `interp` is
`BitVec 128` / `BitVec 256`, and the codec passes through the
`Nat`-based helpers `natToLEBytes` (encode, `Spec/Serialize.lean`)
and `readNatLE` / `readNatLEAux` (decode, `Spec/Deserialize.lean`),
which recurse on the *width* rather than unrolling. So the natural
proof is a `Nat` induction on the little-endian digit expansion,

  `readNatLE (natToLEBytes w n .empty) 0 w = some (n % 256 ^ w)`,

and it closes with **no `bv_decide` / `native_decide`**: the only
axioms are the three standard kernel ones. The wide-integer arms
are therefore axiom-cleaner than the narrow ones.

## Lemma path

1. **Codec size** (`size_natToLEBytes`): `natToLEBytes` appends
   exactly `w` bytes to its accumulator.
2. **Byte characterisation** (`get!_natToLEBytes`): byte `i` of
   `natToLEBytes w n acc` (past the accumulator) is the `i`-th
   little-endian digit `⌊n / 256ⁱ⌋ mod 256`. Proved by induction
   on `w`, threading `acc` and reading `push` back through
   `Array.getElem_push_{lt,eq}`.
3. **Reader value** (`readNatLEAux_value`): folding the Horner
   reader over any buffer whose bytes are the digits of `n`
   rebuilds `n mod 256 ^ w`. One induction on `w` with the
   accumulator universally generalised; the digit step is
   `Nat.mod_mul` (`x % (a·b) = x % a + a · (x / a % b)`).
4. **Codec inverse** (`readNatLE_natToLEBytes`): compose 1–3.
5. **Arm closure**: `decode_encode_uintN128 / 256`,
   `size_serialize_uintN{128,256}`, and the two
   `encode_size_le_max_*` bounds. `Proofs/{Roundtrip,SizeBound,
   SerializeSize}.lean` dispatch to these.

## Lean idioms used here (annotated on first appearance)

* `ByteArray.get!`: total indexing (`0` on out-of-range). The
  characterisation lemmas state their facts in `get!` form to
  avoid carrying bounds proofs; `get!_eq_getElem` bridges to the
  bounds-checked `b[i]'h` that `readNatLEAux` uses, exactly where
  the fold needs a concrete byte.
* `dif_pos h`: reduce a `if h : p then … else …` (dependent-if)
  along the `p`-true branch, given `h : p`. `readNatLEAux`'s
  recursion is guarded by `if h : off + k < b.size`, always true
  under our size hypotheses.
* Nonlinear `Nat` arithmetic (`a·256ⁿ` terms) is finished by
  `omega` *after* every nonlinear product is turned into an atom
  by explicit `Nat.mul_assoc` / `Nat.mul_comm` rewrites; `omega`
  itself treats each maximal product as an opaque variable.
-/

set_option autoImplicit false
-- `decide` on `256 ^ 16 = 2 ^ 128` (and the 256-bit twin) reduces
-- 39-digit `Nat` literals in the kernel; give the elaborator room.
set_option maxHeartbeats 2000000

namespace SizzLean.Proofs

open SizzLean.Spec
-- `natToLEBytes` / `readNatLE` / `readNatLEAux` are `protected` in
-- `Spec/{Serialize,Deserialize}.lean` (proof-internal, kept off the
-- general `SizzLean.Spec` surface), so the wildcard `open` above does
-- not bring them into scope; request the three helpers explicitly.
open SizzLean.Spec (natToLEBytes readNatLE readNatLEAux)

/-! ### ByteArray indexing bridges

`get!` (total) is convenient for stating byte facts without bounds
proofs; the reader fold uses the bounds-checked `b[i]'h`. These three
bridge the two forms and read a pushed byte back. -/

/-- `get!` agrees with the bounds-checked `b[i]` when in range.
`get!` unfolds to `b.data[i]!`, whose panic branch is discharged by
`getElem!_pos` against the supplied bound. -/
theorem get!_eq_getElem (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.get! i = b[i] := by
  show b.data[i]! = b[i]
  rw [ByteArray.getElem_eq_getElem_data]
  exact getElem!_pos b.data i h

/-- Reading a pushed byte below the push point ignores it. -/
theorem get!_push_lt (a : ByteArray) (b : UInt8) (i : Nat) (h : i < a.size) :
    (a.push b).get! i = a.get! i := by
  rw [get!_eq_getElem _ _ (by rw [ByteArray.size_push]; omega), get!_eq_getElem _ _ h]
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_push]
  exact Array.getElem_push_lt h

/-- Reading the pushed byte at the push point returns it. -/
theorem get!_push_eq (a : ByteArray) (b : UInt8) :
    (a.push b).get! a.size = b := by
  rw [get!_eq_getElem _ _ (by rw [ByteArray.size_push]; omega)]
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_push]
  exact Array.getElem_push_eq

/-! ### The little-endian byte codec -/

/-- `natToLEBytes` appends exactly `width` bytes to its accumulator. -/
theorem size_natToLEBytes (w : Nat) : ∀ (n : Nat) (acc : ByteArray),
    (natToLEBytes w n acc).size = acc.size + w := by
  induction w with
  | zero => intro n acc; simp [natToLEBytes]
  | succ k ih =>
      intro n acc
      show (natToLEBytes (k + 1) n acc).size = acc.size + (k + 1)
      simp only [natToLEBytes]
      rw [ih (n / 256) (acc.push (Nat.toUInt8 (n % 256))), ByteArray.size_push]
      omega

/-- Byte `i` of `natToLEBytes w n acc`: bytes below `acc.size` are
the accumulator's; the `j`-th appended byte (`j = i - acc.size`) is
the `j`-th little-endian digit `⌊n / 256ʲ⌋ mod 256`. Induct on `w`,
threading `acc`; a `push` step splits into "below / at / above" the
push point. -/
theorem get!_natToLEBytes (w : Nat) : ∀ (n : Nat) (acc : ByteArray) (i : Nat),
    i < acc.size + w →
    (natToLEBytes w n acc).get! i =
      if i < acc.size then acc.get! i
      else Nat.toUInt8 ((n / 256 ^ (i - acc.size)) % 256) := by
  induction w with
  | zero =>
      intro n acc i hi
      simp only [Nat.add_zero] at hi
      simp only [natToLEBytes, if_pos hi]
  | succ k ih =>
      intro n acc i hi
      show (natToLEBytes (k + 1) n acc).get! i = _
      simp only [natToLEBytes]
      have hsz : (acc.push (Nat.toUInt8 (n % 256))).size = acc.size + 1 :=
        ByteArray.size_push
      rw [ih (n / 256) (acc.push (Nat.toUInt8 (n % 256))) i (by rw [hsz]; omega), hsz]
      by_cases h1 : i < acc.size
      · rw [if_pos (by omega : i < acc.size + 1), if_pos h1, get!_push_lt _ _ _ h1]
      · by_cases h2 : i = acc.size
        · subst h2
          rw [if_pos (Nat.lt_succ_self acc.size), if_neg (Nat.lt_irrefl acc.size),
              get!_push_eq]
          simp [Nat.sub_self]
        · rw [if_neg (by omega : ¬ i < acc.size + 1), if_neg h1]
          have hk : i - acc.size = (i - (acc.size + 1)) + 1 := by omega
          have hexp : (n / 256) / 256 ^ (i - (acc.size + 1)) = n / 256 ^ (i - acc.size) := by
            rw [Nat.div_div_eq_div_mul, hk, Nat.pow_succ,
                Nat.mul_comm (256 ^ (i - (acc.size + 1))) 256]
          rw [hexp]

/-- Specialisation to the `.empty` accumulator: byte `i` of
`natToLEBytes w n .empty` is the `i`-th little-endian digit. -/
theorem get!_natToLEBytes_empty (w n i : Nat) (hi : i < w) :
    (natToLEBytes w n .empty).get! i = Nat.toUInt8 ((n / 256 ^ i) % 256) := by
  rw [get!_natToLEBytes w n .empty i (by rw [ByteArray.size_empty]; omega),
      ByteArray.size_empty, if_neg (Nat.not_lt_zero i), Nat.sub_zero]

/-! ### The Horner reader -/

/-- Folding the Horner reader over any buffer whose byte `off + i`
is the `i`-th little-endian digit of `n` rebuilds `n mod 256 ^ w`,
with the accumulator scaled by `256 ^ w`. Induction on `w` with
`acc` universally generalised: the top byte contributes
`digit · 256 ^ w`, the recursive tail rebuilds `n mod 256 ^ w`, and
`Nat.mod_mul` splits `n mod 256 ^ (w+1)` into exactly those two
pieces. -/
theorem readNatLEAux_value (b : ByteArray) (off n : Nat) : ∀ (w : Nat),
    (∀ i, i < w → off + i < b.size) →
    (∀ i, i < w → (b.get! (off + i)).toNat = (n / 256 ^ i) % 256) →
    ∀ (acc : Nat), readNatLEAux b off w acc = acc * 256 ^ w + n % 256 ^ w := by
  intro w
  induction w with
  | zero => intro _ _ acc; simp [readNatLEAux, Nat.mod_one]
  | succ w ih =>
      intro hlt hval acc
      have hw_lt : off + w < b.size := hlt w (Nat.lt_succ_self w)
      have hstep : readNatLEAux b off (w + 1) acc =
          readNatLEAux b off w (acc * 256 + (b[off + w]'hw_lt).toNat) := by
        simp only [readNatLEAux]
        rw [dif_pos hw_lt]
      have hbridge : (b[off + w]'hw_lt).toNat = (n / 256 ^ w) % 256 := by
        rw [← get!_eq_getElem b (off + w) hw_lt]
        exact hval w (Nat.lt_succ_self w)
      have hlt' : ∀ i, i < w → off + i < b.size :=
        fun i hi => hlt i (Nat.lt_succ_of_lt hi)
      have hval' : ∀ i, i < w → (b.get! (off + i)).toNat = (n / 256 ^ i) % 256 :=
        fun i hi => hval i (Nat.lt_succ_of_lt hi)
      rw [hstep, hbridge, ih hlt' hval' (acc * 256 + (n / 256 ^ w) % 256)]
      -- Digit step: n % 256^(w+1) = n % 256^w + 256^w · (n / 256^w % 256).
      have hmod : n % 256 ^ (w + 1) = n % 256 ^ w + 256 ^ w * ((n / 256 ^ w) % 256) := by
        rw [Nat.pow_succ, Nat.mod_mul]
      rw [hmod, Nat.pow_succ]
      -- Turn every nonlinear product into an atom, then `omega`.
      generalize hp : 256 ^ w = p
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 p, Nat.mul_comm ((n / p) % 256) p]
      omega

/-- **Codec inverse**: reading `w` little-endian bytes back off the
`w`-byte encoding of `n` returns `n mod 256 ^ w`. The buffer has
size exactly `w` (so the `off + width > size` guard is false), and
its bytes are the digits of `n` (`get!_natToLEBytes_empty`), so
`readNatLEAux_value` at `acc = 0` closes it. -/
theorem readNatLE_natToLEBytes (w n : Nat) :
    readNatLE (natToLEBytes w n .empty) 0 w = some (n % 256 ^ w) := by
  have hsize : (natToLEBytes w n .empty).size = w := by
    rw [size_natToLEBytes]; simp [ByteArray.size_empty]
  unfold readNatLE
  rw [if_neg (by rw [hsize]; omega)]
  have hval := readNatLEAux_value (natToLEBytes w n .empty) 0 n w
    (fun i hi => by rw [hsize]; omega)
    (fun i hi => by
      rw [Nat.zero_add, get!_natToLEBytes_empty w n i hi]
      exact UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)))
    0
  rw [hval]
  simp

/-! ### uintN 128 / 256 arms -/

/-- Exact serialized size of a `uintN 128`: 16 bytes. -/
theorem size_serialize_uintN128 (x : BitVec 128) :
    (SSZType.serialize (.uintN 128) x).size = 16 := by
  have h_ser : SSZType.serialize (.uintN 128) x = natToLEBytes 16 x.toNat .empty := by
    unfold SSZType.serialize; rfl
  rw [h_ser, size_natToLEBytes]
  simp [ByteArray.size_empty]

/-- Exact serialized size of a `uintN 256`: 32 bytes. -/
theorem size_serialize_uintN256 (x : BitVec 256) :
    (SSZType.serialize (.uintN 256) x).size = 32 := by
  have h_ser : SSZType.serialize (.uintN 256) x = natToLEBytes 32 x.toNat .empty := by
    unfold SSZType.serialize; rfl
  rw [h_ser, size_natToLEBytes]
  simp [ByteArray.size_empty]

/-- Roundtrip for `.uintN 128`. The encoder emits 16 LE bytes of
`x.toNat`; the decoder reads them back as `x.toNat mod 256^16`, and
`256^16 = 2^128` with `x.toNat < 2^128` collapses the modulus, so
`BitVec.ofNat 128 x.toNat = x`. No `bv_decide`. -/
theorem decode_encode_uintN128 (x : BitVec 128) :
    SSZType.deserialize (.uintN 128) (SSZType.serialize (.uintN 128) x) =
      .ok (x, (SSZType.serialize (.uintN 128) x).size) := by
  have h_ser : SSZType.serialize (.uintN 128) x = natToLEBytes 16 x.toNat .empty := by
    unfold SSZType.serialize; rfl
  rw [size_serialize_uintN128, h_ser]
  unfold SSZType.deserialize
  simp only [readNatLE_natToLEBytes]
  have h256 : (256 : Nat) ^ 16 = 2 ^ 128 := by decide
  rw [h256, Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Roundtrip for `.uintN 256`. Identical recipe with 32 bytes and
`256^32 = 2^256`. -/
theorem decode_encode_uintN256 (x : BitVec 256) :
    SSZType.deserialize (.uintN 256) (SSZType.serialize (.uintN 256) x) =
      .ok (x, (SSZType.serialize (.uintN 256) x).size) := by
  have h_ser : SSZType.serialize (.uintN 256) x = natToLEBytes 32 x.toNat .empty := by
    unfold SSZType.serialize; rfl
  rw [size_serialize_uintN256, h_ser]
  unfold SSZType.deserialize
  simp only [readNatLE_natToLEBytes]
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  rw [h256, Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Size bound for `.uintN 128`: serialized size `16` equals the
schema bound `⌈128/8⌉`. -/
theorem encode_size_le_max_uintN128 (x : BitVec 128) :
    (SSZType.serialize (.uintN 128) x).size ≤ SSZType.maxByteLength (.uintN 128) := by
  rw [size_serialize_uintN128]
  simp [SSZType.maxByteLength]

/-- Size bound for `.uintN 256`: serialized size `32` equals the
schema bound `⌈256/8⌉`. -/
theorem encode_size_le_max_uintN256 (x : BitVec 256) :
    (SSZType.serialize (.uintN 256) x).size ≤ SSZType.maxByteLength (.uintN 256) := by
  rw [size_serialize_uintN256]
  simp [SSZType.maxByteLength]

end SizzLean.Proofs
