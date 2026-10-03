import LeanHazmatP256

/-!
# `LeanHazmatP256Tests.Vectors`: P256VERIFY Known-Answer-Tests

Self-contained KAT gate for the OpenSSL-backed shim. There is no
pure-Lean reference for P-256 ECDSA, so this is the *only* validation
of the FFI boundary (packages/hazmat/docs/ARCHITECTURE.md §10).

The cases are drawn from the **official EIP-7951 vector set** (the
EIP's `assets/eip-7951/test-vectors.json`, 781 Project Wycheproof
cases): three valid cases, the `n - s` complement of the malleability
pair, and two invalid cases (an order-complement `r`, `n - r`, and a
signature from the duplication bug), plus fixed negatives (zero and
out-of-range scalars, the infinity key, an out-of-range coordinate,
wrong lengths, a flipped hash bit, an off-curve point). Each raw input
is the EIP's 160-byte layout (`msgHash ‖ r ‖ s ‖ qx ‖ qy`),
split into the five 32-byte fields the primitive takes.

Each case is one `native_decide`, the OpenSSL computation runs as
compiled code at proof-check time (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for a KAT (CLAUDE.md "Proofs involving
SSZ hashes" generalises to all FFI crypto).
-/

set_option autoImplicit false

namespace LeanHazmatP256Tests.Vectors

open LeanHazmat.P256

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

/-- Wycheproof EcdsaP1363Verify SHA-256 #1: the malleability pair, low-s half, valid. -/
private def valid1MsgHash : ByteArray :=
  hex ("bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023")
/-- Its `r`. -/
private def valid1R : ByteArray :=
  hex ("2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18")
/-- Its `s`. -/
private def valid1S : ByteArray :=
  hex ("4cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd76")
/-- The signer key's `x`. -/
private def valid1Qx : ByteArray :=
  hex ("2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838")
/-- The signer key's `y`. -/
private def valid1Qy : ByteArray :=
  hex ("c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e")

/-- Wycheproof EcdsaVerify SHA-256 #244: special case hash, valid. -/
private def validSpecialHashMsgHash : ByteArray :=
  hex ("33239a52d72f1311512e41222a00000000d2dcceb301c54b4beae8e284788a73")
/-- Its `r`. -/
private def validSpecialHashR : ByteArray :=
  hex ("38686ff0fda2cef6bc43b58cfe6647b9e2e8176d168dec3c68ff262113760f52")
/-- Its `s`. -/
private def validSpecialHashS : ByteArray :=
  hex ("067ec3b651f422669601662167fa8717e976e2db5e6a4cf7c2ddabb3fde9d67d")
/-- Same key as `valid1`: `x`. -/
private def validSpecialHashQx : ByteArray :=
  hex ("2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838")
/-- Same key as `valid1`: `y`. -/
private def validSpecialHashQy : ByteArray :=
  hex ("c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e")

/-- Wycheproof EcdsaP1363Verify SHA-256 #311: y-coordinate of the public key is large, valid. -/
private def validLargeYMsgHash : ByteArray :=
  hex ("2f77668a9dfbf8d5848b9eeb4a7145ca94c6ed9236e4a773f6dcafa5132b2f91")
/-- Its `r`. -/
private def validLargeYR : ByteArray :=
  hex ("70bebe684cdcb5ca72a42f0d873879359bd1781a591809947628d313a3814f67")
/-- Its `s`. -/
private def validLargeYS : ByteArray :=
  hex ("aec03aca8f5587a4d535fa31027bbe9cc0e464b1c3577f4c2dcde6b2094798a9")
/-- The large-`y` key's `x`. -/
private def validLargeYQx : ByteArray :=
  hex ("bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015")
/-- The large-`y` key's `y`, near the field modulus. -/
private def validLargeYQy : ByteArray :=
  hex ("fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d")

/-- Wycheproof EcdsaP1363Verify SHA-256 invalid case: `r` is the
order complement of the valid case's `r` (`n - r`). -/
private def invalidModOrderMsgHash : ByteArray :=
  hex ("bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023")
/-- The mutated `r`. -/
private def invalidModOrderR : ByteArray :=
  hex ("d45c5740946b2a147f59262ee6f5bc90bd01ed280528b62b3aed5fc93f06f739")
/-- The unmutated `s`. -/
private def invalidModOrderS : ByteArray :=
  hex ("b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db")
/-- Same key as `valid1`: `x`. -/
private def invalidModOrderQx : ByteArray :=
  hex ("2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838")
/-- Same key as `valid1`: `y`. -/
private def invalidModOrderQy : ByteArray :=
  hex ("c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e")

/-- Wycheproof EcdsaVerify SHA-256 #340: duplication bug, invalid. -/
private def invalidDuplicationBugMsgHash : ByteArray :=
  hex ("bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023")
/-- The mutated `r`. -/
private def invalidDuplicationBugR : ByteArray :=
  hex ("6f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569")
/-- The mutated `s`. -/
private def invalidDuplicationBugS : ByteArray :=
  hex ("bb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b")
/-- The duplicated-point key's `x`. -/
private def invalidDuplicationBugQx : ByteArray :=
  hex ("5b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc46963")
/-- The duplicated-point key's `y`. -/
private def invalidDuplicationBugQy : ByteArray :=
  hex ("7c75bf0c5c9f6d17ffb16d2726bf30a9c7aaf31a8d317472b1ea145ab66db616")

/-- The other half of the malleability pair: the same `(hash, r, key)`
as `valid1` with `s' = n - s`. Verifies, pinning the
no-high-s-rejection behavior by construction rather than by chance. -/
private def highSS : ByteArray :=
  hex "b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db"

/-- The P-256 group order `n`. -/
private def p256N : ByteArray :=
  hex "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"

/-- The P-256 field modulus `p`. -/
private def p256P : ByteArray :=
  hex "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"

/-- The 32-byte all-zero string. -/
private def zeros32 : ByteArray := hex "0000000000000000000000000000000000000000000000000000000000000000"

/-! ### Ground-truth anchors (EIP-7951 / Wycheproof) -/

/-- The malleability pair's low-`s` half: verifies. Its `n - s`
complement (`highSS`) must verify too, which is what "no
anti-malleability policy" means. -/
example : p256Verify valid1MsgHash valid1R valid1S valid1Qx valid1Qy = true := by
  native_decide

/-- Special-case hash: verifies. -/
example : p256Verify validSpecialHashMsgHash validSpecialHashR validSpecialHashS
      validSpecialHashQx validSpecialHashQy = true := by
  native_decide

/-- Large y-coordinate public key: verifies. -/
example : p256Verify validLargeYMsgHash validLargeYR validLargeYS
      validLargeYQx validLargeYQy = true := by
  native_decide

/-- The high-`s` complement of `valid1`: verifies (no anti-malleability
policy). -/
example : p256Verify valid1MsgHash valid1R highSS valid1Qx valid1Qy = true := by
  native_decide

/-- The order-complement `r` does not verify. -/
example : p256Verify invalidModOrderMsgHash invalidModOrderR invalidModOrderS
      invalidModOrderQx invalidModOrderQy = false := by
  native_decide

/-- The duplication-bug signature does not verify. -/
example : p256Verify invalidDuplicationBugMsgHash invalidDuplicationBugR
      invalidDuplicationBugS invalidDuplicationBugQx invalidDuplicationBugQy =
      false := by
  native_decide

/-! ### Negatives -/

/-- `r = 0` is not a signature. -/
example : p256Verify valid1MsgHash zeros32 valid1S valid1Qx valid1Qy = false := by
  native_decide

/-- `s = 0` is not a signature. -/
example : p256Verify valid1MsgHash valid1R zeros32 valid1Qx valid1Qy = false := by
  native_decide

/-- `r = n` (the group order) is out of range. -/
example : p256Verify valid1MsgHash p256N valid1S valid1Qx valid1Qy = false := by
  native_decide

/-- `s = n` is out of range. -/
example : p256Verify valid1MsgHash valid1R p256N valid1Qx valid1Qy = false := by
  native_decide

/-- The point at infinity is not a public key. -/
example : p256Verify valid1MsgHash valid1R valid1S zeros32 zeros32 = false := by
  native_decide

/-- A coordinate equal to the field modulus is out of range. -/
example : p256Verify valid1MsgHash valid1R valid1S p256P valid1Qy = false := by
  native_decide

/-- A 31-byte field is rejected by the length sentinel. -/
example : p256Verify (valid1MsgHash.extract 0 31) valid1R valid1S
      valid1Qx valid1Qy = false := by
  native_decide

/-- Flipping one bit of the hash breaks the signature. -/
private def badHash : ByteArray :=
  (valid1MsgHash.extract 0 31).push (valid1MsgHash.get! 31 ^^^ 1)

/-- The flipped-bit hash does not verify. -/
example : p256Verify badHash valid1R valid1S valid1Qx valid1Qy = false := by
  native_decide

/-- A point off the curve is rejected (`false`, not an error). -/
example : p256Verify valid1MsgHash valid1R valid1S valid1Qx
      (ByteArray.mk (Array.replicate 32 0xAB)) = false := by
  native_decide

end LeanHazmatP256Tests.Vectors
