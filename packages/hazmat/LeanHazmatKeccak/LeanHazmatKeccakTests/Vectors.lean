import LeanHazmatKeccak

/-!
# `LeanHazmatKeccakTests.Vectors`: Keccak-256 Known-Answer-Tests

Self-contained KAT gate for the keccak-tiny-backed shim. There is no
pure-Lean reference for Keccak-256, so this is the *only* validation of
the FFI boundary (packages/hazmat/docs/ARCHITECTURE.md §10). Three kinds of
case:

* **EVM canonical constants**: `keccak256 ""` =
  `c5d246…a470` (the digest every Ethereum client hard-codes) and
  `keccak256 0x80` = `56e81f…b421` (the MPT empty-trie root). A wrong
  padding byte (SHA3 instead of Keccak) fails these immediately.
* **Published Keccak-256 vectors**: short strings, a one-block
  boundary input (exactly 136 bytes), and a multi-block input, all
  generated from the reference Keccak definition and cross-checked
  against the constants above.
* **Consumer-side composition**: address derivation,
  `keccak256(pubkey)[12:32]`, for the EIP-155 example transaction's
  public key. This documents the LeanHazmat rule that composition is
  the caller's job (packages/hazmat/docs/ARCHITECTURE.md §4): the primitive is
  `keccak256` alone, and no package-level function derives addresses.

Each case is one `native_decide`, the keccak computation runs as
compiled code at proof-check time (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for a KAT (CLAUDE.md "Proofs involving SSZ
hashes" generalises to all FFI crypto).
-/

set_option autoImplicit false

namespace LeanHazmatKeccakTests.Vectors

open LeanHazmat.Keccak

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

/-! ### EVM canonical constants -/

/-- `keccak256 ""`, the constant every Ethereum client hard-codes. -/
private def emptyDigest : ByteArray :=
  hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

example : keccak256 ByteArray.empty = emptyDigest := by native_decide

/-- `keccak256 0x80`, the MPT empty-trie root (`keccak256(rlp(""))`). -/
private def rlpEmptyDigest : ByteArray :=
  hex "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

/-- The RLP encoding of the empty string, the single byte `0x80`. -/
private def rlpEmpty : ByteArray := hex "80"

example : keccak256 rlpEmpty = rlpEmptyDigest := by native_decide

/-! ### Published Keccak-256 vectors -/

example : keccak256 (String.toUTF8 "abc") =
    hex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45" := by
  native_decide

example : keccak256 (String.toUTF8 "testing") =
    hex "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02" := by
  native_decide

example :
    keccak256 (String.toUTF8 "The quick brown fox jumps over the lazy dog") =
      hex "4d741b6f1eb29cb2a9b9911c82f56fa8d73b04959d3d9d222895df6c0b28aa15" := by
  native_decide

/-- 135 zero bytes: the `0x01` delimiter and the final `0x80` pad byte
land on the SAME byte, the classic padding collision. -/
example : keccak256 (ByteArray.mk (Array.replicate 135 0)) =
    hex "29e3704feeca7fb9ba229f0fa04d9b36449cf3ad6e1d85d9cfff3a10df9abc3e" := by
  native_decide

/-- Exactly one full absorb block (136 zero bytes): the padding lands
at the block boundary, the classic off-by-one trap. -/
example : keccak256 (ByteArray.mk (Array.replicate 136 0)) =
    hex "3a5912a7c5faa06ee4fe906253e339467a9ce87d533c65be3c15cb231cdb25f9" := by
  native_decide

/-- 137 zero bytes: one byte into the second block. -/
example : keccak256 (ByteArray.mk (Array.replicate 137 0)) =
    hex "bee7fbb405cb0d91a8775e338c4a5e4b5d6b2d051f687fa942043cffdc73bd28" := by
  native_decide

/-- A multi-block input (300 bytes of `0,1,2,…`): exercises the
absorb-fold loop over two blocks. -/
private def pattern300 : ByteArray :=
  ⟨((List.range 256 ++ List.range 44).map (fun n => n.toUInt8)).toArray⟩

example : keccak256 pattern300 =
    hex "a679e749a6af300c36e7ff2255d220864eab27b382f9cfdc5aa4d13563ba36ff" := by
  native_decide

/-- 36 zero bytes (an input the trie path hashing hits). -/
example : keccak256 (ByteArray.mk (Array.replicate 36 0)) =
    hex "74723bc3efaf59d897623890ae3912b9be3c4c67ccee3ffcf10b36406c722c1b" := by
  native_decide

/-! ### Consumer-side composition: address derivation

`address = keccak256(pubkey)[12:32]`, the EIP-155 example transaction's
public key (see `LeanHazmatSecp256k1Tests`, which recovers this same
key). The composition lives in the *test*, documenting that the
package exposes only the raw digest. -/

/-- The uncompressed 64-byte public key (x ‖ y) of the EIP-155 example
transaction (its private key `0x4646…46` is published in the EIP). -/
private def eip155Pubkey : ByteArray :=
  hex ("4bc2a31265153f07e70e0bab08724e6b85e217f8cd628ceb62974247bb493382" ++
       "ce28cab79ad7119ee1ad3ebcdb98a16805211530ecc6cfefa1b88e6dff99232a")

/-- The EIP-155 example's sender address, `keccak256(pk)[12:32]`. -/
private def eip155Address : ByteArray :=
  hex "9d8a62f656a8d1615c1294fd71e9cfb3e4855a4f"

/-- Address derivation, expressed as consumer-side composition. -/
example : (keccak256 eip155Pubkey).extract 12 32 = eip155Address := by
  native_decide

end LeanHazmatKeccakTests.Vectors
