import LeanHazmatSha256

/-!
# `LeanHazmatSha256Tests.Vectors`: anchor KAT for all three primitives

Self-contained Known-Answer-Test gate for the FFI shims. Every
expected digest is a hard-coded constant from FIPS 180-4 / the SSZ
spec, compared against the FFI output via `native_decide`. No
dependency on `LeanSha256` or `SizzLean`, this package validates
*standalone* (the property that lets it ship as a mirror).

The full NIST CAVP byte-oriented suite (129 vectors) for
`sha256Hash` lives in the generated companion
[`Cavp.lean`](Cavp.lean); this file adds the cases CAVP does not
cover, the two-input `sha256Combine` and the level-batched
`sha256BatchCombine`, plus a few `sha256Hash` anchors so the file
reads as a complete primitive-by-primitive smoke test.

## Why `native_decide` here (and not in proofs)

`LeanHazmat.Sha256.sha256Hash` is `@[extern] opaque`, so the kernel cannot
reduce it, only the compiled FFI call produces bytes. `native_decide`
evaluates the (closed) proposition by running that compiled code at
proof-check time, adding one `Lean.ofReduceBool` axiom per call. The
KAT path is exactly where those axioms are acceptable (ARCHITECTURE.md
§10); the proof path is not.

## Lean idioms used here

* `ByteArray.mk #[0xab, 0xcd, …]`: build a `ByteArray` from a literal
  `Array UInt8`; `UInt8` literals support `0x` hex notation.
* `native_decide`: see above; a wrong shim (truncation, byte order,
  padding, length-mismatch in the batch loop) fails at least one case
  with the diverging input visible in the error trace.
-/

set_option autoImplicit false

namespace LeanHazmatSha256Tests.Vectors

open LeanHazmat.Sha256

/-! ### Inputs -/

/-- 32 zero bytes, the SSZ "zero leaf" and the most common
`combine` operand in Merkleization. -/
def zero32 : ByteArray := ByteArray.mk <| Array.replicate 32 0

/-- The 56-byte FIPS 180-4 §B.2 worked-example input
`abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq`. Exactly
this length so padding spans into a second block. -/
def fips56 : ByteArray :=
  String.toUTF8 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

/-! ### Expected digests (FIPS 180-4 §B / SSZ ZERO_HASHES) -/

/-- `SHA-256("")` per FIPS 180-4 §B.0. -/
def expected_empty : ByteArray := ByteArray.mk #[
  0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
  0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
  0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
  0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55]

/-- `SHA-256("abc")` per FIPS 180-4 §B.1. -/
def expected_abc : ByteArray := ByteArray.mk #[
  0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
  0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
  0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
  0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad]

/-- `SHA-256("abcdbcdec...")` per FIPS 180-4 §B.2 (the 56-byte
two-block example). -/
def expected_fips56 : ByteArray := ByteArray.mk #[
  0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8,
  0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
  0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67,
  0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1]

/-- `SHA-256(zero32 ++ zero32)`, the SSZ `ZERO_HASHES[1]` seed:
`f5a5fd42…`. The base of the cache layer's zero-hash tower. -/
def expected_zero_combine : ByteArray := ByteArray.mk #[
  0xf5, 0xa5, 0xfd, 0x42, 0xd1, 0x6a, 0x20, 0x30,
  0x27, 0x98, 0xef, 0x6e, 0xd3, 0x09, 0x97, 0x9b,
  0x43, 0x00, 0x3d, 0x23, 0x20, 0xd9, 0xf0, 0xe8,
  0xea, 0x98, 0x31, 0xa9, 0x27, 0x59, 0xfb, 0x4b]

/-! ### `sha256Hash` anchors -/

/-- `sha256Hash ""` matches FIPS 180-4 §B.0. -/
example : sha256Hash ByteArray.empty = expected_empty := by native_decide

/-- `sha256Hash "abc"` matches FIPS 180-4 §B.1. -/
example : sha256Hash (String.toUTF8 "abc") = expected_abc := by native_decide

/-- `sha256Hash` on the 56-byte multi-block input matches §B.2. -/
example : sha256Hash fips56 = expected_fips56 := by native_decide

/-! ### `sha256Combine`: the two-input concatenation digest -/

/-- `sha256Combine zero32 zero32` matches the SSZ `ZERO_HASHES[1]`. -/
example : sha256Combine zero32 zero32 = expected_zero_combine := by native_decide

/-- Cross-check: `combine` of `(left, right)` equals `hash` of the
concatenation. Catches shim bugs where the two-input path diverges
from the single-input path. -/
example :
    sha256Combine ByteArray.empty (sha256Hash ByteArray.empty) =
      sha256Hash (ByteArray.empty ++ sha256Hash ByteArray.empty) := by
  native_decide

/-! ### `sha256BatchCombine`: the level-batched sibling combine

Validated against `sha256Combine` (already anchored above) rather
than against a separate constant table: a batch is correct iff each
slot equals the scalar combine of the same pair, and the empty-array
edge case returns the empty array. -/

/-- Empty input → empty output. The C loop's zero-trip edge case. -/
example : sha256BatchCombine #[] #[] = #[] := by native_decide

/-- A single pair degenerates to a scalar combine and to the known
`ZERO_HASHES[1]` constant. -/
example : sha256BatchCombine #[zero32] #[zero32] = #[expected_zero_combine] := by
  native_decide

/-- A multi-pair batch agrees pointwise with `sha256Combine` (covers
the loop increment path and per-slot ownership transfer). -/
example :
    sha256BatchCombine #[zero32, fips56] #[fips56, zero32]
      = #[sha256Combine zero32 fips56, sha256Combine fips56 zero32] := by
  native_decide

/-- Order matters: swapping left/right yields a different digest. -/
example :
    sha256BatchCombine #[zero32] #[fips56]
      ≠ sha256BatchCombine #[fips56] #[zero32] := by native_decide

end LeanHazmatSha256Tests.Vectors
