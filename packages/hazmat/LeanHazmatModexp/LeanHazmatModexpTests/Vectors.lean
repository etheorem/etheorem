import LeanHazmatModexp

/-!
# `LeanHazmatModexpTests.Vectors`: modexp Known-Answer-Tests

Self-contained KAT gate for the OpenSSL-BIGNUM-backed shim. There is no
pure-Lean reference for this primitive, so this is the *only*
validation of the FFI boundary (packages/hazmat/docs/ARCHITECTURE.md §10).
Four kinds of case:

* **EIP-198 worked examples**, verbatim from the EIP text: the Fermat
  case (`3^(2^256 - 2^32 - 978) mod (2^256 - 2^32 - 977) = 1`), the
  zero-base case (answers `0`), and the `3^65535 mod 2^255` parse. The
  EIP shows that parse twice, once with an excess `0x07` byte and once
  with a one-byte right-padded modulus; both parse to the same three
  values, and the case pins those values.
* **Fixed modular-arithmetic cases**, cross-checked against Python's
  `pow` at authoring time: a zero exponent (answers `1`), modulus 1
  (answers the single `00`), leading-zero operands, and a multi-byte
  operand set.
* **Even moduli**: EIP-198 allows any positive modulus, even
  included; three cases with unit, odd, and multi-byte answers.
* **Negatives**: a zero modulus is a failure (empty `ByteArray`),
  as an unparsed empty input and as parsed zero values.

Each case is one `native_decide`, the BIGNUM computation runs as
compiled code at proof-check time (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for a KAT (CLAUDE.md "Proofs involving
SSZ hashes" generalises to all FFI crypto).
-/

set_option autoImplicit false

namespace LeanHazmatModexpTests.Vectors

open LeanHazmat.Modexp

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

/-! ### EIP-198 worked examples -/

/-- The Fermat case from the EIP text:
`3^(2^256 - 2^32 - 978) mod (2^256 - 2^32 - 977) = 1`. The raw
primitive answers in **minimal** big-endian form (the precompile's
left-padding to the modulus length is the caller's step), so the
published `0x…0001` pins here as `01`. -/
private def fermatExp : ByteArray :=
  hex "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"

/-- The Fermat case modulus, `2^256 - 2^32 - 977`. -/
private def fermatMod : ByteArray :=
  hex "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"

example : modExp (hex "03") fermatExp fermatMod = hex "01" := by
  native_decide

/-- The EIP's zero-base parse: answers `0` (the single zero byte)
regardless of the exponent. -/
example :
    modExp ByteArray.empty fermatExp fermatMod = hex "00" := by
  native_decide

/-- The EIP's `3^65535 mod 2^255` example (base length 1, exponent
length 2 carrying `0xffff`, modulus `0x80` right-padded to 32 bytes).
The EIP also shows the same parse with an excess trailing `0x07` byte
and with a one-byte modulus; all three parse to these values. Result
verbatim from the EIP text. -/
example : modExp (hex "03") (hex "ffff")
      (hex "8000000000000000000000000000000000000000000000000000000000000000") =
    hex "3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab" := by
  native_decide

/-! ### Fixed modular-arithmetic cases -/

/-- A zero exponent answers `1 mod modulus`. -/
example : modExp (hex "0123456789abcdef") ByteArray.empty (hex "97") =
    hex "01" := by
  native_decide

/-- Modulus 1 collapses every answer to `0` (the minimal big-endian
zero). -/
example : modExp (hex "03") fermatExp (hex "01") = hex "00" := by
  native_decide

/-- Multi-byte operands: `256^2 = 65536`, and `65536 mod 65519 = 17`,
so the minimal big-endian answer is the single byte `11`. -/
example : modExp (hex "0100") (hex "02") (hex "ffef") = hex "11" := by
  native_decide

/-- Leading zeros in an operand change nothing. -/
example : modExp (hex "000003") fermatExp fermatMod = hex "01" := by
  native_decide

/-! ### Even moduli -/

/-- EIP-198 allows any positive modulus, even included.
`3^2 mod 4 = 1`. -/
example : modExp (hex "03") (hex "02") (hex "04") = hex "01" := by
  native_decide

/-- An even modulus with a non-unit answer: `5^3 mod 8 = 5`. -/
example : modExp (hex "05") (hex "03") (hex "08") = hex "05" := by
  native_decide

/-- An even modulus with a multi-byte operand: `2^10 mod 12 = 4`. -/
example : modExp (hex "02") (hex "0a") (hex "0c") = hex "04" := by
  native_decide

/-! ### Negatives -/

/-- A zero modulus is a failure: reduction mod 0 is undefined. The
empty input parses to zero. -/
example : modExp (hex "03") (hex "02") ByteArray.empty = ByteArray.empty := by
  native_decide

/-- A parsed zero modulus fails the same way: the all-zero byte strings
`00` and `0000` parse to the BIGNUM `0`, and the shim rejects a zero
modulus before exponentiating. -/
example : modExp (hex "03") (hex "02") (hex "00") = ByteArray.empty := by
  native_decide

example : modExp (hex "03") (hex "02") (hex "0000") = ByteArray.empty := by
  native_decide

end LeanHazmatModexpTests.Vectors
