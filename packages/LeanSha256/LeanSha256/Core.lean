/-!
# `LeanSha256`: pure-Lean SHA-256 reference

A *kernel-reducible* SHA-256 implementation. No FFI, no
typeclasses, no SSZ coupling, just `hash : ByteArray → ByteArray`
and `combine : ByteArray → ByteArray → ByteArray` plus a handful of
structural conformance lemmas against FIPS 180-4.

## Why this exists

SHA-256 is general-purpose. Anyone wanting a Lean-kernel-reducible
SHA-256 with empirical NIST coverage should be able to depend on
this library directly, without dragging in any Ethereum SSZ
machinery. The `LeanSha256` lib is independent of the `SizzLean`
library, `SizzLean` uses it through a thin `Hasher Sha256Spec`
instance bridge (in `SizzLean.Hasher.Sha256Spec`), but it has no
reverse dependency.

## Implementation notes

* Constants and state words are `BitVec 32`. Addition in `BitVec 32`
  is mod 2³² by construction, matching FIPS 180-4 §4.1.2.
* `Array (BitVec 32)` (rather than `Vector (BitVec 32) _`) avoids
  size-proof obligations on the message schedule and round state.
  Out-of-bounds indexing via `arr[i]!` is sound by construction,
  every access sits in `[0, 64)` for the schedule and `[0, 8)` for
  the state.
* The compression function is a `Nat.fold` over `[0, 64)` of the
  per-round update. The kernel evaluates it via `decide` /
  `native_decide` without unfolding-recursion blowups.

## NIST acceptance gates

Three `native_decide` examples at the bottom of this file lock the
spec against NIST FIPS 180-4 §B test vectors directly. These three
pass *or* the spec is wrong; CI catches it at build time.

For broader empirical coverage (full NIST CAVP short + long
message vectors), see `Tests/Sha256NistCavp.lean`
in the SSZ side of the repo, 129 vectors validated against both
this implementation and a separate FFI-backed OpenSSL shim.

## Structural conformance lemmas

After the executable definitions, the file ships kernel-checked
theorems documenting that:

* the round helpers (`ch`, `maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁`) compute
  exactly the FIPS §4.1.2 forms;
* the round constants and initial-hash arrays have the right size
  with the right boundary entries (catches a missing line / off-by-
  one in `kConstants` or `h0Constants`);
* per-block helpers preserve the size invariants the next layer
  relies on (`messageSchedule` produces 64 words, `compressBlock`
  produces an 8-word state, `pad` rounds up to a multiple of 64
  bytes);
* the top-level digest is always exactly 32 bytes
  (`hash_size_eq_32`, `combine_size_eq_32`).

These don't claim "computes SHA-256". That's an empirical claim
the NIST asserts settle. They do claim the *shape* matches the
FIPS algorithm, which catches a class of structural-regression
bugs at proof check time.
-/

set_option autoImplicit false

namespace LeanSha256

/-! ## FIPS 180-4 §4.2.2 round constants

64 K constants (cube roots of the first 64 primes) and 8 initial
hash values H₀ (square roots of the first 8 primes). Both literal
arrays of the canonical 32-bit big-endian fractional parts. -/

private def kConstants : Array (BitVec 32) := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def h0Constants : Array (BitVec 32) := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ## §4.1.2 bitwise round functions

Identifiers match FIPS 180-4 (Ch, Maj, Σ₀, Σ₁, σ₀, σ₁). All operate
on `BitVec 32` so `^^^`, `&&&`, `+` are the standard 32-bit XOR /
AND / mod-2³² ADD operations. `rotateRight` and `ushiftRight` are
the built-in Lean `BitVec` primitives, same as the spec's `ROTR`
and `SHR`. -/

private def ch (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ ((~~~ x) &&& z)

private def maj (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

private def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

private def smallSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x.ushiftRight 3

private def smallSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x.ushiftRight 10

/-! ## §5.2 message-schedule expansion

Given 16 message words `M[0..15]` (read big-endian from the
64-byte block), produce 64 round words `W[0..63]`:

* `W[t] = M[t]` for `0 ≤ t < 16`.
* `W[t] = σ₁(W[t−2]) + W[t−7] + σ₀(W[t−15]) + W[t−16]` for
  `16 ≤ t < 64`.

Implemented as an `Array`-pushing fold: start with the 16 message
words, run 48 iterations each appending one new word computed from
the previous four (at offsets `-2`, `-7`, `-15`, `-16`). -/

/-- Structural recursion on `steps`, the kernel sees each step as
one Array-push and a recursive call on a strictly smaller `steps`.
This is intentionally *not* `partial def` so the size-preservation
lemma below can unfold the body during a proof. -/
private def extendSchedule (acc : Array (BitVec 32))
    (steps : Nat) : Array (BitVec 32) :=
  match steps with
  | 0     => acc
  | k + 1 =>
      let t := acc.size
      let next :=
        smallSigma1 acc[t - 2]! + acc[t - 7]! +
        smallSigma0 acc[t - 15]! + acc[t - 16]!
      extendSchedule (acc.push next) k

private def messageSchedule (block : Array (BitVec 32)) :
    Array (BitVec 32) :=
  extendSchedule block 48

/-! ## §6.2 compression function

64 rounds on a working state `(a, b, c, d, e, f, g, h)` carried as
an `Array (BitVec 32)` of size 8, element `i` is the `i`-th state
word. Each round:

```
T1 = h + Σ₁(e) + Ch(e, f, g) + K[t] + W[t]
T2 = Σ₀(a) + Maj(a, b, c)
(a, b, c, d, e, f, g, h) := (T1+T2, a, b, c, d+T1, e, f, g)
```

After 64 rounds, add the working state to the input hash
componentwise (mod 2³²) and return the result. -/

private def oneRound (state : Array (BitVec 32)) (w k : BitVec 32) :
    Array (BitVec 32) :=
  let a := state[0]!
  let b := state[1]!
  let c := state[2]!
  let d := state[3]!
  let e := state[4]!
  let f := state[5]!
  let g := state[6]!
  let h := state[7]!
  let t1 := h + bigSigma1 e + ch e f g + k + w
  let t2 := bigSigma0 a + maj a b c
  #[t1 + t2, a, b, c, d + t1, e, f, g]

private def compressBlock (hIn : Array (BitVec 32))
    (block : Array (BitVec 32)) : Array (BitVec 32) :=
  let schedule := messageSchedule block
  -- 64 rounds, folding the working state.
  let finalState : Array (BitVec 32) :=
    Nat.fold 64 (fun t _ s =>
      oneRound s schedule[t]! kConstants[t]!) hIn
  -- Add working state to input hash componentwise (mod 2³²).
  Array.ofFn (n := 8) (fun i => hIn[i.val]! + finalState[i.val]!)

/-! ## §5.1 padding (Merkle–Damgård)

Append the bit `1` (one `0x80` byte), zero-pad until length ≡ 56
(mod 64), append the original length in *bits* as a 64-bit
big-endian integer. The result is always a multiple of 64 bytes. -/

private def uint64ToBytesBE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    Nat.toUInt8 ((n >>> 56) &&& 0xff),
    Nat.toUInt8 ((n >>> 48) &&& 0xff),
    Nat.toUInt8 ((n >>> 40) &&& 0xff),
    Nat.toUInt8 ((n >>> 32) &&& 0xff),
    Nat.toUInt8 ((n >>> 24) &&& 0xff),
    Nat.toUInt8 ((n >>> 16) &&& 0xff),
    Nat.toUInt8 ((n >>> 8)  &&& 0xff),
    Nat.toUInt8 ( n         &&& 0xff)]

private def pad (input : ByteArray) : ByteArray :=
  let inputLen := input.size
  let bitLen := inputLen * 8
  let withMark := input.push 0x80
  -- Number of zero bytes to bring length ≡ 56 (mod 64).
  let modLen := withMark.size % 64
  let zeroBytes := if modLen ≤ 56 then 56 - modLen else 56 + 64 - modLen
  let withZeros := withMark ++ ByteArray.mk (Array.replicate zeroBytes 0)
  withZeros ++ uint64ToBytesBE bitLen

/-! ## Byte/word conversions

Big-endian: bytes `[b₀, b₁, b₂, b₃]` ↦ word `b₀·2²⁴ + b₁·2¹⁶ + b₂·2⁸ + b₃`.
Inverse used to pack the final 8-word hash state into a 32-byte digest.
-/

private def bytesToWordBE (b0 b1 b2 b3 : UInt8) : BitVec 32 :=
  BitVec.ofNat 32 (
    b0.toNat * 0x1000000 +
    b1.toNat * 0x10000 +
    b2.toNat * 0x100 +
    b3.toNat)

private def wordToBytesBE (w : BitVec 32) : ByteArray :=
  let n := w.toNat
  ByteArray.mk #[
    Nat.toUInt8 ((n >>> 24) &&& 0xff),
    Nat.toUInt8 ((n >>> 16) &&& 0xff),
    Nat.toUInt8 ((n >>> 8)  &&& 0xff),
    Nat.toUInt8 ( n         &&& 0xff)]

/-- Extract the 16 32-bit words of block `blockIdx` from `padded`.
Caller must ensure `padded.size ≥ (blockIdx + 1) * 64`. -/
private def extractBlock (padded : ByteArray) (blockIdx : Nat) :
    Array (BitVec 32) :=
  Array.ofFn (n := 16) (fun j =>
    let off := blockIdx * 64 + j.val * 4
    bytesToWordBE
      padded[off]!
      padded[off + 1]!
      padded[off + 2]!
      padded[off + 3]!)

private def packState (state : Array (BitVec 32)) : ByteArray :=
  state.foldl (fun acc w => acc ++ wordToBytesBE w) ByteArray.empty

/-! ## Top-level digest

`hash` runs the full SHA-256 over an arbitrary `ByteArray`:
pad, parse blocks, fold compression across the blocks, pack the
final state to 32 bytes. `combine` is `hash (left ++ right)`, same
contract as a two-input concatenation primitive. -/

/-- SHA-256 digest of an arbitrary-length `ByteArray`. Returns a
32-byte `ByteArray`. -/
def hash (input : ByteArray) : ByteArray :=
  let padded := pad input
  let numBlocks := padded.size / 64
  let finalState :=
    Nat.fold numBlocks (fun blockIdx _ st =>
      compressBlock st (extractBlock padded blockIdx)) h0Constants
  packState finalState

/-- SHA-256 digest of `left ++ right`. Materialises the
concatenation; an FFI implementation would avoid this for cache
locality, but the spec values clarity over micro-optimisation. -/
def combine (left right : ByteArray) : ByteArray :=
  hash (left ++ right)

/-! ## NIST FIPS 180-4 §B acceptance gates

Three published test vectors, asserted against `hash` via
`native_decide`. Catches any transcription error in the constants,
padding, or round functions.

* §B.0: `SHA-256("")`.
* §B.1: `SHA-256("abc")`.
* §B.2: `SHA-256(56-byte multi-block example)`.
-/

private def fips56 : ByteArray :=
  String.toUTF8 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

private def expectedEmpty : ByteArray := ByteArray.mk #[
  0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
  0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
  0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
  0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55]

private def expectedAbc : ByteArray := ByteArray.mk #[
  0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
  0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
  0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
  0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad]

private def expectedFips56 : ByteArray := ByteArray.mk #[
  0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8,
  0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
  0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67,
  0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1]

example : hash ByteArray.empty = expectedEmpty := by native_decide
example : hash (String.toUTF8 "abc") = expectedAbc := by native_decide
example : hash fips56 = expectedFips56 := by native_decide

/-! ## Structural lemmas (FIPS 180-4 conformance)

Kernel-checked theorems that fix the *shape* of the spec against
FIPS 180-4. They don't claim "computes SHA-256". That's an empirical
question against NIST vectors. They do claim:

* the round helpers compute exactly the FIPS forms (`ch`, `maj`,
  `Σ₀`, `Σ₁`, `σ₀`, `σ₁`);
* the round constants and initial-hash arrays have the right size
  with the right boundary entries (catches a missing line / off-by-
  one in `kConstants` or `h0Constants`);
* each per-block helper preserves the size invariants the next
  layer relies on (`messageSchedule` produces 64 words,
  `compressBlock` produces an 8-word state, `pad` rounds up to a
  multiple of 64 bytes);
* the top-level digest is always exactly 32 bytes.

Bugs *within* a round function (e.g., swapping `y` and `z` in
`ch`) are out of scope for shape lemmas, they're caught by the
NIST asserts above and the FFI-equivalence gate in
`Tests/Sha256Equivalence.lean`.
-/

section Structural

/-! ### §4.1.2 round-function FIPS forms

Each lemma is `rfl` because the implementations are written exactly
in the FIPS form. The theorem ensures any future refactor that
changes the shape is caught at proof check time. -/

theorem ch_eq_fips (x y z : BitVec 32) :
    ch x y z = (x &&& y) ^^^ ((~~~ x) &&& z) := rfl

theorem maj_eq_fips (x y z : BitVec 32) :
    maj x y z = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := rfl

theorem bigSigma0_eq_fips (x : BitVec 32) :
    bigSigma0 x = x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22 :=
  rfl

theorem bigSigma1_eq_fips (x : BitVec 32) :
    bigSigma1 x = x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25 :=
  rfl

theorem smallSigma0_eq_fips (x : BitVec 32) :
    smallSigma0 x = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x.ushiftRight 3 :=
  rfl

theorem smallSigma1_eq_fips (x : BitVec 32) :
    smallSigma1 x = x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x.ushiftRight 10 :=
  rfl

/-! ### §4.2.2 constant sizes + boundary entries

Locks the 64 K constants and 8 H₀ entries by count plus first/last
values. A missing line in either array changes the size; a
miscopied first or last value flips the boundary check. -/

theorem kConstants_size : kConstants.size = 64 := by decide
theorem h0Constants_size : h0Constants.size = 8 := by decide

theorem kConstants_first : kConstants[0]! = (0x428a2f98 : BitVec 32) := by decide
theorem kConstants_last  : kConstants[63]! = (0xc67178f2 : BitVec 32) := by decide

theorem h0Constants_first : h0Constants[0]! = (0x6a09e667 : BitVec 32) := by decide
theorem h0Constants_last  : h0Constants[7]! = (0x5be0cd19 : BitVec 32) := by decide

/-! ### Byte-helper output sizes

`uint64ToBytesBE` emits exactly 8 bytes; `wordToBytesBE` exactly 4.
Both follow by `rfl` because each is `ByteArray.mk` of a fixed-size
`Array UInt8` literal. -/

theorem uint64ToBytesBE_size (n : Nat) :
    (uint64ToBytesBE n).size = 8 := rfl

theorem wordToBytesBE_size (w : BitVec 32) :
    (wordToBytesBE w).size = 4 := rfl

/-! ### `extendSchedule` size

Each step pushes one element, so the result has size `acc.size +
steps`. Proven by structural induction on `steps`. -/

theorem extendSchedule_size (acc : Array (BitVec 32)) (steps : Nat) :
    (extendSchedule acc steps).size = acc.size + steps := by
  induction steps generalizing acc with
  | zero => rfl
  | succ k ih =>
      show (extendSchedule (acc.push _) k).size = acc.size + (k + 1)
      rw [ih (acc.push _), Array.size_push]
      omega

/-! ### `messageSchedule` and `compressBlock` sizes -/

theorem messageSchedule_size (block : Array (BitVec 32))
    (hSz : block.size = 16) :
    (messageSchedule block).size = 64 := by
  show (extendSchedule block 48).size = 64
  rw [extendSchedule_size]; omega

theorem oneRound_size (state : Array (BitVec 32)) (w k : BitVec 32) :
    (oneRound state w k).size = 8 := rfl

theorem compressBlock_size (hIn : Array (BitVec 32))
    (block : Array (BitVec 32)) :
    (compressBlock hIn block).size = 8 := by
  unfold compressBlock
  simp [Array.size_ofFn]

/-! ### Padding ends on a 64-byte boundary

Merkle–Damgård padding emits `0x80`, then enough zeros to land the
message at length ≡ 56 (mod 64), then the 8-byte length suffix.
Total `% 64 = 0` by construction. -/

private theorem byteArray_mk_size_eq {arr : Array UInt8} :
    (ByteArray.mk arr).size = arr.size := rfl

theorem pad_size_multiple_of_64 (input : ByteArray) :
    (pad input).size % 64 = 0 := by
  unfold pad
  simp only [ByteArray.size_append, ByteArray.size_push,
             byteArray_mk_size_eq, Array.size_replicate,
             uint64ToBytesBE_size]
  split <;> omega

/-! ### `packState` size = `state.size * 4`

`Array.foldl_induction` carries the invariant `acc.size = i * 4`
across each iteration: starting from the empty `ByteArray`
(size 0), each step appends 4 bytes (`wordToBytesBE`), so after
`state.size` steps the size is `state.size * 4`. -/

theorem packState_size (state : Array (BitVec 32)) :
    (packState state).size = state.size * 4 := by
  unfold packState
  exact Array.foldl_induction
    (motive := fun i (acc : ByteArray) => acc.size = i * 4)
    (h0 := rfl)
    (hf := by
      intro i acc ih
      simp [ByteArray.size_append, wordToBytesBE_size, ih]
      omega)

/-! ### `hash` output is exactly 32 bytes

The chaining state is initialised at `h0Constants` (size 8), each
`Nat.fold` step replaces it with `compressBlock _ _` (also size 8),
and `packState` of a size-8 array gives `8 * 4 = 32` bytes. -/

/-- Helper: `Nat.fold` over a size-preserving step preserves size. -/
private theorem nat_fold_array_size {α : Type}
    (n : Nat) (f : (i : Nat) → i < n → Array α → Array α)
    (sz : Nat)
    (hf : ∀ i h s, (f i h s).size = sz)
    (init : Array α) (hInit : init.size = sz) :
    (Nat.fold n f init).size = sz := by
  induction n with
  | zero => simpa using hInit
  | succ k _ =>
      simp only [Nat.fold_succ]
      apply hf

theorem hash_size_eq_32 (input : ByteArray) :
    (hash input).size = 32 := by
  unfold hash
  rw [packState_size,
      nat_fold_array_size _ _ 8
        (fun _ _ _ => compressBlock_size _ _) _ h0Constants_size]

theorem combine_size_eq_32 (left right : ByteArray) :
    (combine left right).size = 32 := hash_size_eq_32 _

end Structural

end LeanSha256
