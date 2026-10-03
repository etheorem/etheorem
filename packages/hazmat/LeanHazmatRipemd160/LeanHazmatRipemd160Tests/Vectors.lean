import LeanHazmatRipemd160

/-!
# `LeanHazmatRipemd160Tests.Vectors`: RIPEMD-160 Known-Answer-Tests

Self-contained KAT gate for the OpenSSL-backed shim. There is no
pure-Lean reference for RIPEMD-160, so this is the *only* validation of
the FFI boundary (packages/hazmat/docs/ARCHITECTURE.md §10). Two kinds of case:

* **The published RIPEMD-160 test-vector set** (the consortium's nine
  vectors, cross-checked against `openssl dgst -rmd160` at authoring
  time): the empty string, single bytes, `"abc"`, the two standard
  padded strings, the alphabet, `8 × "1234567890"`, and the
  million-`a` stress case (one megabyte, exercising multi-block
  absorption over the legacy-provider path).
* **Consistency of the private-context setup**: every gate above runs
  through the shim's private `OSSL_LIB_CTX` with `default` + `legacy`
  loaded; if the provider is unavailable, every case fails at once
  with the empty `ByteArray`.

Each case is one `native_decide`, the digest runs as compiled code at
proof-check time (one `Lean.ofReduceBool` axiom per case), the
acceptable regime for a KAT (CLAUDE.md "Proofs involving SSZ hashes"
generalises to all FFI crypto).
-/

set_option autoImplicit false

namespace LeanHazmatRipemd160Tests.Vectors

open LeanHazmat.Ripemd160

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

/-! ### The published test-vector set -/

/-- The empty string. -/
example : ripemd160 ByteArray.empty =
    hex "9c1185a5c5e9fc54612808977ee8f548b2258d31" := by
  native_decide

/-- The single byte `a`. -/
example : ripemd160 (String.toUTF8 "a") =
    hex "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe" := by
  native_decide

/-- `"abc"`. -/
example : ripemd160 (String.toUTF8 "abc") =
    hex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc" := by
  native_decide

/-- `"message digest"`. -/
example : ripemd160 (String.toUTF8 "message digest") =
    hex "5d0689ef49d2fae572b881b123a85ffa21595f36" := by
  native_decide

/-- The lower-case alphabet. -/
example : ripemd160 (String.toUTF8 "abcdefghijklmnopqrstuvwxyz") =
    hex "f71c27109c692c1b56bbdceb5b9d2865b3708dbc" := by
  native_decide

/-- The 56-byte canonical block-boundary string. -/
example :
    ripemd160
        (String.toUTF8 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
      hex "12a053384a9c0c88e405a06c27dcf49ada62eb2b" := by
  native_decide

/-- The 62-digit mixed-alphabet string. -/
example :
    ripemd160
        (String.toUTF8 "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789") =
      hex "b0e20b6e3116640286ed3a87a5713079b21f5189" := by
  native_decide

/-- Eight repetitions of `"1234567890"` (80 bytes). -/
private def eighty : ByteArray :=
  hex ((String.join (List.replicate 8 "31323334353637383930")))

example : ripemd160 eighty =
    hex "9b752e45573d4b39f4dbd3323cab82bf63326bfb" := by
  native_decide

/-- One million `a` bytes: the multi-block stress case. -/
private def millionA : ByteArray :=
  ByteArray.mk (Array.replicate 1000000 97)

example : ripemd160 millionA =
    hex "52783243c1697bdbe16d37f97f68f08325dc1528" := by
  native_decide

end LeanHazmatRipemd160Tests.Vectors
