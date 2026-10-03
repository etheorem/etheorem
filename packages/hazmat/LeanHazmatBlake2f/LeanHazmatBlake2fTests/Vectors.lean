import LeanHazmatBlake2f

/-!
# `LeanHazmatBlake2fTests`: EIP-152 Known-Answer-Test gates

The self-contained KAT suite for the in-repo BLAKE2f shim. Build with:

```
lake build LeanHazmatBlake2fTests
```

BLAKE2f has no third-party library behind it, so these vectors are the
family's entire trust-validation surface (packages/hazmat/docs/ARCHITECTURE.md
§10). Two kinds of case:

* **Ground-truth anchors**: the five published EIP-152 test vectors
  4 through 8, matched byte for byte. Together they cover rounds 0, 1,
  12, and `0xffffffff`, and both values of the final-block flag, so a
  wrong round schedule, sigma indexing, or feed-forward fails against
  published ground truth.
* **Length sentinels**: wrong-length `h` / `m` inputs return the empty
  `ByteArray` (the family's error convention).

Each case is one `native_decide`: the F compression runs as compiled
code at proof-check time (one `Lean.ofReduceBool` axiom per case), the
acceptable regime for a KAT (CLAUDE.md "Proofs involving SSZ hashes"
generalises to all FFI crypto).

## Lean idioms used here

* `hex`: a compile-time hex-string → `ByteArray` decoder, so the
  vectors read as the hex strings the EIP publishes.
* `run`: decodes the EIP-152 precompile input shape
  (`rounds(4, BE) ‖ h ‖ m ‖ t0(8, LE) ‖ t1(8, LE) ‖ f(1)`) and calls
  the raw `blake2fCompress`. The decode lives in the *test*, mirroring
  the LeanHazmat rule that precompile input parsing is the caller's
  concern, not part of the primitive.
-/

set_option autoImplicit false

namespace LeanHazmatBlake2fTests.Vectors

open LeanHazmat.Blake2f

/-! ### Hex helper -/

/-- Value of a single hex digit (`0` for any non-hex char, inputs here
are always well-formed). -/
private def hexVal (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else 0

/-- Pair adjacent hex digits into bytes. Structural recursion on the
char list (each step drops two elements). -/
private def hexBytes : List Char → List UInt8
  | a :: b :: rest => (hexVal a * 16 + hexVal b) :: hexBytes rest
  | _ => []

/-- Decode a hex string (no `0x` prefix) into a `ByteArray`. -/
private def hex (s : String) : ByteArray := ⟨(hexBytes s.toList).toArray⟩

/-! ### EIP-152 input decode -/

/-- Big-endian `UInt32` at byte offset `off`. -/
private def be32 (bs : ByteArray) (off : Nat) : UInt32 :=
  (bs.get! off).toUInt32 <<< 24 ||| (bs.get! (off + 1)).toUInt32 <<< 16 |||
    (bs.get! (off + 2)).toUInt32 <<< 8 ||| (bs.get! (off + 3)).toUInt32

/-- Little-endian `UInt64` at byte offset `off`. -/
private def le64 (bs : ByteArray) (off : Nat) : UInt64 :=
  (bs.get! off).toUInt64 ||| (bs.get! (off + 1)).toUInt64 <<< 8 |||
    (bs.get! (off + 2)).toUInt64 <<< 16 ||| (bs.get! (off + 3)).toUInt64 <<< 24 |||
    (bs.get! (off + 4)).toUInt64 <<< 32 ||| (bs.get! (off + 5)).toUInt64 <<< 40 |||
    (bs.get! (off + 6)).toUInt64 <<< 48 ||| (bs.get! (off + 7)).toUInt64 <<< 56

/-- Decode one EIP-152 precompile input
(`rounds ‖ h ‖ m ‖ t0 ‖ t1 ‖ f`, 213 bytes) and run the raw `F`. -/
private def run (inp : ByteArray) : ByteArray :=
  blake2fCompress (be32 inp 0) (inp.extract 4 68) (inp.extract 68 196)
    (le64 inp 196) (le64 inp 204) (inp.get! 212 != 0)

/-! ### Ground-truth anchors (EIP-152 test vectors 4–8) -/

/-- Test vector 4: rounds=0, final flag 01. -/
private def inputzeroRounds : ByteArray :=
  hex ("0000000048c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
      "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
      "19cde05b61626300000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "000000000300000000000000000000000000000001")

/-- The published Test vector 4 output. -/
private def outputzeroRounds : ByteArray :=
  hex ("08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
      "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b")

/-- `Test vector 4` matches, byte for byte. -/
example : run inputzeroRounds = outputzeroRounds := by native_decide

/-- Test vector 5: rounds=12, final flag 01. -/
private def inputtwelveRounds : ByteArray :=
  hex ("0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
      "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
      "19cde05b61626300000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "000000000300000000000000000000000000000001")

/-- The published Test vector 5 output. -/
private def outputtwelveRounds : ByteArray :=
  hex ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
      "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")

/-- `Test vector 5` matches, byte for byte. -/
example : run inputtwelveRounds = outputtwelveRounds := by native_decide

/-- Test vector 6: rounds=12, final flag 00. -/
private def inputtwelveRoundsNotFinal : ByteArray :=
  hex ("0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
      "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
      "19cde05b61626300000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "000000000300000000000000000000000000000000")

/-- The published Test vector 6 output. -/
private def outputtwelveRoundsNotFinal : ByteArray :=
  hex ("75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752" ++
      "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735")

/-- `Test vector 6` matches, byte for byte. -/
example : run inputtwelveRoundsNotFinal = outputtwelveRoundsNotFinal := by native_decide

/-- Test vector 7: rounds=1, final flag 01. -/
private def inputoneRound : ByteArray :=
  hex ("0000000148c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
      "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
      "19cde05b61626300000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "000000000300000000000000000000000000000001")

/-- The published Test vector 7 output. -/
private def outputoneRound : ByteArray :=
  hex ("b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
      "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421")

/-- `Test vector 7` matches, byte for byte. -/
example : run inputoneRound = outputoneRound := by native_decide

/-- Test vector 8: rounds=4294967295, final flag 01. -/
private def inputmaxRounds : ByteArray :=
  hex ("ffffffff48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
      "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
      "19cde05b61626300000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "000000000300000000000000000000000000000001")

/-- The published Test vector 8 output. -/
private def outputmaxRounds : ByteArray :=
  hex ("fc59093aafa9ab43daae0e914c57635c5402d8e3d2130eb9b3cc181de7f0ecf9" ++
      "b22bf99a7815ce16419e200e01846e6b5df8cc7703041bbceb571de6631d2615")

/-- `Test vector 8` matches, byte for byte. -/
example : run inputmaxRounds = outputmaxRounds := by native_decide

/-! ### Nonzero counter vectors

The published EIP-152 vectors all use `t0 = 3, t1 = 0`; a shim that
dropped `t1` (or the high bytes of `t0`) would pass them. These two
cases use both counter words set to nonzero values, on the same `h` /
`m` block as vector 5. Ground truth from `scripts/gen_vectors.py`, an
independent Python implementation of RFC 7693 section 3.2; the script
self-checks against the published EIP-152 vectors before it emits, and
running it re-checks the committed values below. -/

/-- 12 rounds, final block, `t0 = 0x1122334455667788`,
`t1 = 0x99aabbccddeeff00`. -/
example : blake2fCompress 12 (inputtwelveRounds.extract 4 68)
      (inputtwelveRounds.extract 68 196) 0x1122334455667788 0x99aabbccddeeff00 true =
    hex ("a4485332b3bed911dc3120d5173d3960e8cf0bd633a1966db0ae508f3635e2e7" ++
      "9441d136c83f0d15dde62f7f3b57e2d6d41dc9e20d04e85fc004bd93a71ca29e") := by
  native_decide

/-- 1 round, not final, same nonzero counter. -/
example : blake2fCompress 1 (inputtwelveRounds.extract 4 68)
      (inputtwelveRounds.extract 68 196) 0x1122334455667788 0x99aabbccddeeff00 false =
    hex ("76df1abdd8ee76fca0705e6216b426f7aaedfef4459e2984151adf57bc634043" ++
      "541e54c922a65f0e2cb629e49d6ec62fdf38d339eb7bc70c4c37d5d4dbc4f0d7") := by
  native_decide

/-! ### Length sentinels -/

/-- A 63-byte `h` substitute for the negative cases (contents do not
matter, the length sentinel fires first). -/
private def wrongH : ByteArray := ByteArray.mk (Array.replicate 63 0)

/-- A 128-byte `m` substitute for the negative cases. -/
private def goodM : ByteArray := ByteArray.mk (Array.replicate 128 0)

/-- Wrong-length `h` returns the empty `ByteArray`. -/
example : blake2fCompress 12 wrongH goodM 0 0 true = ByteArray.empty := by
  native_decide

/-- Wrong-length `m` returns the empty `ByteArray`. -/
example : blake2fCompress 12 (inputoneRound.extract 4 68) ByteArray.empty 3 0 true =
    ByteArray.empty := by
  native_decide

end LeanHazmatBlake2fTests.Vectors
