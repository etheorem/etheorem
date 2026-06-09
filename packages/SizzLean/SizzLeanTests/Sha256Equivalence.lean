import LeanHazmatSha256
import LeanSha256.Core

/-!
# `SizzLeanTests.Sha256Equivalence`: FFI ↔ pure-Lean SHA-256

The empirical equivalence gate: the pure-Lean spec (`LeanSha256`) and
the FFI binding (`LeanHazmat.Sha256.sha256Hash` / `sha256Combine`) agree
byte-for-byte on every input class reachable from real workloads. This
is one of the two cross-checks that need *both* packages in scope, so
it lives in `SizzLeanTests` (hazmat-docs/ARCHITECTURE.md §9); it is the
empirical evidence behind the `sha256Hash_eq_spec` /
`sha256Combine_eq_spec` axioms.

## Coverage

* **NIST FIPS 180-4 vectors** (lifted from
  `Conformance/Sha256Vectors.lean`): empty input, `"abc"`,
  56-byte multi-block, `zero32 ++ zero32`, plus a cross-check
  between `combine` and the `hash`-of-concatenation form.
* **Randomised `combine` batch**: 100 PRNG-generated
  `(left, right)` 32-byte pairs run through both
  `LeanSha256.combine` and `sha256Combine`.
* **Randomised `hash` batch**: 10 PRNG cases each at lengths
  0, 32, 55, 56, 64, 96, 128, 256. The 55/56 boundary catches
  single-vs-double-block padding regressions; 64/96/128/256
  exercise multi-block compression.

Total: 5 NIST + 100 combine + 80 hash = 185 byte-equality
assertions, all closed via `native_decide` at build time. A
divergence on any single case fails the build with the diverging
input visible in the error trace.

## Why both directions of cross-check

A bug in `Sha256Spec` (constants, round functions, padding) shows
up either as a divergence from the NIST vectors (caught by the
in-file gates in `Hasher/Sha256Spec.lean`) *or* as a divergence
from the FFI (caught here). Together, the two layers triangulate:
either the spec is wrong (and NIST catches it), or the FFI is
wrong (and the spec catches it; presumably the spec is then
trusted to be right by virtue of also matching NIST).
-/

set_option autoImplicit false

namespace SizzLeanTests.Sha256Equivalence

-- `sha256Hash` / `sha256Combine` resolve to the FFI primitives in the
-- `LeanHazmatSha256` package; `LeanSha256.*` is the pure-Lean spec.
open LeanHazmat.Sha256

/-! ### NIST vectors run through both implementations -/

private def fips56 : ByteArray :=
  String.toUTF8 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

private def zero32 : ByteArray := ByteArray.mk (Array.replicate 32 0)

example : LeanSha256.hash ByteArray.empty = sha256Hash ByteArray.empty := by
  native_decide

example : LeanSha256.hash (String.toUTF8 "abc") = sha256Hash (String.toUTF8 "abc") := by
  native_decide

example : LeanSha256.hash fips56 = sha256Hash fips56 := by
  native_decide

example : LeanSha256.combine zero32 zero32 = sha256Combine zero32 zero32 := by
  native_decide

-- Cross-check: combine ≡ hash-of-concatenation, validated on both
-- implementations independently.
example : LeanSha256.combine zero32 (LeanSha256.hash ByteArray.empty)
        = sha256Hash (zero32 ++ sha256Hash ByteArray.empty) := by
  native_decide

/-! ### Deterministic PRNG (LCG, Numerical Recipes parameters) -/

private def lcgNext (s : Nat) : Nat :=
  (s * 1664525 + 1013904223) % 4294967296

/-- Generate `n` random bytes; thread the PRNG state. -/
private def randBytes (n : Nat) (s : Nat) : ByteArray × Nat :=
  let rec go : Nat → Nat → ByteArray → ByteArray × Nat
    | 0,     st, acc => (acc, st)
    | k + 1, st, acc =>
        let st' := lcgNext st
        go k st' (acc.push (Nat.toUInt8 (st' % 256)))
  go n s ByteArray.empty

/-! ### Randomised `combine` batch: 100 cases over 32-byte pairs -/

private def oneCombineCase (s : Nat) : Bool × Nat :=
  let (l,  s1) := randBytes 32 s
  let (r,  s2) := randBytes 32 s1
  (LeanSha256.combine l r = sha256Combine l r, s2)

private def runCombineCases : Nat → Nat → Bool
  | 0,     _ => true
  | k + 1, s =>
      let (ok, s') := oneCombineCase s
      if ok then runCombineCases k s' else false

example : runCombineCases 100 0xFEEDC0DE = true := by native_decide

/-! ### Randomised `hash` batch: 10 cases at each of 8 lengths

Lengths chosen to exercise SHA-256's padding boundary:

* `0`: empty input (single-block, just padding).
* `32`: short, single-block.
* `55`: max single-block: `55 + 1 + 8 = 64`, exactly one block
  after padding.
* `56`: just over the single-block boundary: padding spills
  into a second block.
* `64`: exactly one block of message; padding is a whole second
  block of zeros.
* `96`, `128`, `256`: multi-block compression. -/

private def oneHashCase (len : Nat) (s : Nat) : Bool × Nat :=
  let (input, s') := randBytes len s
  (LeanSha256.hash input = sha256Hash input, s')

private def runHashCasesAtLen (len : Nat) : Nat → Nat → Bool
  | 0,     _ => true
  | k + 1, s =>
      let (ok, s') := oneHashCase len s
      if ok then runHashCasesAtLen len k s' else false

private def runHashCasesAllLens (s : Nat) : Bool :=
  runHashCasesAtLen 0   10 s        &&
  runHashCasesAtLen 32  10 (s + 1)  &&
  runHashCasesAtLen 55  10 (s + 2)  &&
  runHashCasesAtLen 56  10 (s + 3)  &&
  runHashCasesAtLen 64  10 (s + 4)  &&
  runHashCasesAtLen 96  10 (s + 5)  &&
  runHashCasesAtLen 128 10 (s + 6)  &&
  runHashCasesAtLen 256 10 (s + 7)

example : runHashCasesAllLens 0xBADBEEF = true := by native_decide

end SizzLeanTests.Sha256Equivalence
