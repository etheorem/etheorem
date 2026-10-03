/-!
# `LeanRlp.Spec.Scalar`: `Nat` and minimal big-endian bytes

The scalar layer under the RLP wire format. RLP writes an integer as
the shortest big-endian byte string that holds it, and zero as the
empty string. This module holds the pair of functions that do that
conversion, plus the width arithmetic the header code shares: the
byte count of a minimal big-endian value, and the width of the
long-form length field for a payload.

The encoding is minimal (no leading zero unless the value is zero),
and the decode of an encode gives the value back. Those two facts
are `Proofs.Scalar` lemmas, PLAN.md Stage 3. The decoder already
uses that minimality, through the canonical checks of
`Spec.Decode`.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

/-- `beDigits n` is the byte count of the minimal big-endian form of
`n`: zero for `n = 0`, else one more than for `n / 256`. The
recursion is structural on a step bound, so the kernel can reduce
it; under a well-founded form, every `decide` gate that reads a
long-form header fails. -/
def beDigits (n : Nat) : Nat := beDigitsGo n n
where
  /-- Counts the big-endian digits of `n`, with `k` steps of fuel.
  Each step divides by 256, so the digit count never exceeds `n`,
  and `k = n` always suffices; at `n = 0` the first arm answers 0
  with no step spent, so the bound covers it too. -/
  beDigitsGo : Nat → Nat → Nat
    | 0, _ => 0
    | _ + 1, 0 => 0
    | k + 1, n + 1 => 1 + beDigitsGo k ((n + 1) / 256)

/-- `minimalBE n` is the shortest big-endian byte string that holds
`n`, most significant byte first. Zero gives the empty array. -/
def minimalBE (n : Nat) : ByteArray := minimalBEDigits n (beDigits n)
where
  /-- Pushes the `k` low bytes of `n`, least significant last, so the
  result reads most significant first. -/
  minimalBEDigits : Nat → Nat → ByteArray
    | _, 0 => ByteArray.empty
    | n, k + 1 => (minimalBEDigits (n / 256) k).push (UInt8.ofNat (n % 256))

/-- `beNat input start count` is the big-endian value of `count`
bytes of `input` at `start`, first byte most significant. Reads past
the end contribute zero, so the decoder bounds-checks before it
reads. -/
def beNat (input : ByteArray) (start count : Nat) : Nat :=
  match count with
  | 0 => 0
  | count + 1 => 256 * beNat input start count + input[start + count]!.toNat

/-- `lenOfLen len` is the byte width of the long-form length field
for a payload of `len` bytes: zero for the short form (a payload of
55 bytes or fewer), else the minimal big-endian width of `len`. The
header code of `Spec.Encode` and the size function of `Spec.Item`
share it, so the byte counts have one home. -/
def lenOfLen (len : Nat) : Nat :=
  if len ≤ 55 then 0 else beDigits len

end LeanRlp.Spec
