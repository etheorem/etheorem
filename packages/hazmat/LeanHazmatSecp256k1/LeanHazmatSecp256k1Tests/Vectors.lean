import LeanHazmatSecp256k1

/-!
# `LeanHazmatSecp256k1Tests.Vectors`: secp256k1 Known-Answer-Tests

Self-contained KAT gate for the libsecp256k1-backed shims. There is no
pure-Lean reference for secp256k1 ECDSA, so this is the *only*
validation of the FFI boundary (packages/hazmat/docs/ARCHITECTURE.md §10).
Three kinds of case:

* **EIP-155 ground truth**: the example transaction the EIP publishes
  (signing hash `daf5a779…`, `v = 37`, the `(r, s)` pair, and the
  private key `0x4646…46`). The recovered public key is pinned
  byte-for-byte, and `ecdsaVerify` accepts the same triple. The
  EIP-155 sender address derived from this key is checked in
  `LeanHazmatKeccakTests` (address derivation is consumer-side
  composition, so the anchor lives with the hashing package).
* **A second deterministic signature** over a different hash (same
  key), recovered and verified: two independent `(r, s, recId)`
  triples reaching the same pinned key.
* **Negatives**: a tampered `s` recovers a different, exactly pinned
  key; verification (`false`) catches the tamper; an `r` above the
  curve order is unparseable; a zero `r` or `s` recovers nothing and
  fails verification; a wrong-length input is rejected; an off-curve
  public key fails verification; a `recId` above 3 is rejected;
  `recId` parity 1 recovers a different, exactly pinned key, so the
  caller's `v` mapping decides which key comes back.

Each case is one `native_decide`, the libsecp256k1 computation runs as
compiled code at proof-check time (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for a KAT (CLAUDE.md "Proofs involving SSZ
hashes" generalises to all FFI crypto).
-/

set_option autoImplicit false

namespace LeanHazmatSecp256k1Tests.Vectors

open LeanHazmat.Secp256k1

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

/-! ### The EIP-155 example transaction -/

/-- The EIP-155 example's signing hash. -/
private def msgEip155 : ByteArray :=
  hex "daf5a779ae972f972197303d7b574746c7ef83eadac0f2791ad23db92e4c8e53"

/-- The EIP-155 example's `r`. -/
private def rEip155 : ByteArray :=
  hex "28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276"

/-- The EIP-155 example's `s`. -/
private def sEip155 : ByteArray :=
  hex "67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83"

/-- The EIP-155 example's signer public key (its private key
`0x4646…46` is published in the EIP). -/
private def pkEip155 : ByteArray :=
  hex ("4bc2a31265153f07e70e0bab08724e6b85e217f8cd628ceb62974247bb493382" ++
       "ce28cab79ad7119ee1ad3ebcdb98a16805211530ecc6cfefa1b88e6dff99232a")

/-- Recovery with `recId = 0` (`v = 37`, chain id 1, parity 0) matches
the published key, byte for byte. -/
example : ecdsaRecover msgEip155 rEip155 sEip155 0 = pkEip155 := by
  native_decide

/-- `ecdsaVerify` accepts the published triple. -/
example : ecdsaVerify msgEip155 rEip155 sEip155 pkEip155 = true := by
  native_decide

/-! ### A second deterministic signature, same key -/

/-- A second message (its hash), signed with the same EIP-155 key
using a fixed deterministic nonce. -/
private def msgToy : ByteArray :=
  hex "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

/-- The second signature's `r`. -/
private def rToy : ByteArray :=
  hex "4f355bdcb7cc0af728ef3cceb9615d90684bb5b2ca5f859ab0f0b704075871aa"

/-- The second signature's `s` (a high-`s` value, so verification
exercises the normalize path). -/
private def sToy : ByteArray :=
  hex "b166ed26fcb27f4ff5af9a74e5195af4e4c9f504cb6937f8e52de103a6202637"

/-- The second signature recovers the same pinned key. -/
example : ecdsaRecover msgToy rToy sToy 1 = pkEip155 := by
  native_decide

/-- ...and verifies against it. -/
example : ecdsaVerify msgToy rToy sToy pkEip155 = true := by
  native_decide

/-- Each signature does *not* verify under the other message. -/
example : ecdsaVerify msgEip155 rToy sToy pkEip155 = false := by
  native_decide

example : ecdsaVerify msgToy rEip155 sEip155 pkEip155 = false := by
  native_decide

/-! ### Negatives -/

/-- A tampered `s` (all `0x99` bytes) recovers exactly this wrong key,
pinned so an empty result or any other answer fails the gate. Recovery
alone does not detect the tamper; `ecdsaVerify` does. -/
private def pkTampered : ByteArray :=
  hex ("4a598137361927618552fa87f6125b9bf738e66856fcdd448abbf8d2a108f622" ++
      "bdb90c18e9af67483f72ba065689ac2a5c4331aa28d622581734a951bff5c745")

/-- The tampered-`s` signature recovers exactly the pinned wrong key. -/
example : ecdsaRecover msgEip155 rEip155
      (hex ("9999999999999999999999999999999999999999999999999999999999999999")) 0 = pkTampered := by
  native_decide

/-- An `r` above the curve order is not a parseable signature. -/
example : ecdsaRecover msgEip155 (ByteArray.mk (Array.replicate 32 0xFF)) sEip155 0
    = ByteArray.empty := by
  native_decide

/-- `recId > 3` is rejected. -/
example : ecdsaRecover msgEip155 rEip155 sEip155 4 = ByteArray.empty := by
  native_decide

/-- Wrong parity (`recId` 1) recovers exactly this other key, pinned
so the caller's `v` → `recId` mapping decides the answer. -/
private def pkParity1 : ByteArray :=
  hex ("5bcb07804fccffa8628b7151c4cce54f1251d59144736ddfe3bafacf45c5f8ec" ++
      "f48f8d6febdcc650a9e2e3cf464ef4dc31f28eb805f03f87d7ae9860703e6ad0")

/-- `recId` 1 recovers exactly the pinned other key. -/
example : ecdsaRecover msgEip155 rEip155 sEip155 1 = pkParity1 := by
  native_decide

/-- A tampered signature fails verification. -/
example : ecdsaVerify msgEip155 rEip155 sToy pkEip155 = false := by
  native_decide

/-- The all-zero 32-byte scalar. -/
private def zero32 : ByteArray := ByteArray.mk (Array.replicate 32 0x00)

/-- A zero `r` recovers nothing: `R` would be the identity point. -/
example : ecdsaRecover msgEip155 zero32 sEip155 0 = ByteArray.empty := by
  native_decide

/-- A zero `s` recovers nothing: the preimage step divides by `s`. -/
example : ecdsaRecover msgEip155 rEip155 zero32 0 = ByteArray.empty := by
  native_decide

/-- The EIP-155 signing hash truncated to 31 bytes. -/
private def msgEip155Short : ByteArray :=
  hex "daf5a779ae972f972197303d7b574746c7ef83eadac0f2791ad23db92e4c8e"

/-- A wrong-length message hash is rejected. -/
example : ecdsaRecover msgEip155Short rEip155 sEip155 0
    = ByteArray.empty := by
  native_decide

/-- A zero `r` fails verification. -/
example : ecdsaVerify msgEip155 zero32 sEip155 pkEip155 = false := by
  native_decide

/-- A zero `s` fails verification. -/
example : ecdsaVerify msgEip155 rEip155 zero32 pkEip155 = false := by
  native_decide

/-- The EIP-155 `r` truncated to 31 bytes fails verification. -/
private def rEip155Short : ByteArray :=
  hex "28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa6362"

example : ecdsaVerify msgEip155 rEip155Short sEip155 pkEip155 = false := by
  native_decide

/-- The point `(1, 1)` is not on secp256k1 (`1 ≠ 1³ + 7`), so the key
is unparseable: verification is `false`. -/
private def pkOffCurve : ByteArray :=
  hex ("0000000000000000000000000000000000000000000000000000000000000001" ++
       "0000000000000000000000000000000000000000000000000000000000000001")

example : ecdsaVerify msgEip155 rEip155 sEip155 pkOffCurve = false := by
  native_decide


/-! ### Order-range and key-length negatives

The curve order `n` bounds both signature scalars: the library rejects
an `r` or `s` at `n` itself, and `recId` 2 / 3 (the `R.x` overflow
flags) need `r + n` to stay below the field prime, which fails for
this signature (`r + n > p`), so recovery answers empty rather than a
wrong key. -/

/-- The curve order `n` as a 32-byte scalar. -/
private def orderN : ByteArray :=
  hex "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"

/-- An `r` equal to the order fails verification: no parseable scalar. -/
example : ecdsaVerify msgEip155 orderN sEip155 pkEip155 = false := by
  native_decide

/-- An `s` equal to the order recovers nothing. -/
example : ecdsaRecover msgEip155 rEip155 orderN 0 = ByteArray.empty := by
  native_decide

/-- A 63-byte key fails the length check, so verification is `false`. -/
private def pkShort : ByteArray :=
  ByteArray.mk (Array.replicate 63 0x02)

example : ecdsaVerify msgEip155 rEip155 sEip155 pkShort = false := by
  native_decide

/-- `recId` 2: the recovery `x = r + n` exceeds the field prime, so
recovery fails instead of returning a wrong key. -/
example : ecdsaRecover msgEip155 rEip155 sEip155 2 = ByteArray.empty := by
  native_decide

/-- `recId` 3, same overflow (the parity bit only picks the sign). -/
example : ecdsaRecover msgEip155 rEip155 sEip155 3 = ByteArray.empty := by
  native_decide

/- Length pin for the off-curve key: `hex` maps a bad character to 0
and drops an odd trailing digit, so a typo here would be rejected on
the length check instead of the curve check under test. The pin moves
the failure to the build. -/

#guard pkOffCurve.size == 64

end LeanHazmatSecp256k1Tests.Vectors
