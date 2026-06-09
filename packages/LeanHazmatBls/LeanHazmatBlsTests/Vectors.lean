import LeanHazmatBls

/-!
# `LeanHazmatBlsTests.Vectors`: consensus BLS Known-Answer-Tests

Self-contained KAT gate for the blst-backed BLS shims. There is no
pure-Lean reference for BLS, so this is the *only* validation of the FFI
boundary (hazmat-docs/ARCHITECTURE.md §10). Two kinds of case:

* **Ground-truth anchors**: `(sk, msg) ↦ sig` and `(pk, msg, sig) ↦ true`
  triples lifted verbatim from the official `ethereum/consensus-spec-tests`
  `general/phase0/bls` suite (v1.5.0). A wrong ciphersuite, DST, or
  group choice fails these immediately against published ground truth.
* **Self-contained round-trips**: derive pubkeys with `skToPk`, sign,
  aggregate, and verify, exercising `aggregate` / `aggregateVerify` /
  `fastAggregateVerify` / `ethFastAggregateVerify` without needing
  vendored vectors for every operation.

Each case is one `native_decide`, the blst computation runs as compiled
code at proof-check time (one `Lean.ofReduceBool` axiom per case), the
acceptable regime for a KAT (CLAUDE.md "Proofs involving SSZ hashes"
generalises to all FFI crypto).

## Lean idioms used here

* `hex`: a compile-time hex-string → `ByteArray` decoder, so the
  vectors read as the hex strings the spec publishes. `native_decide`
  evaluates it by running compiled code.
-/

set_option autoImplicit false

namespace LeanHazmatBlsTests.Vectors

open LeanHazmat.Bls

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

/-! ### Ground-truth anchors (consensus-spec-tests v1.5.0) -/

/-- `sign_case_11b8c7cad5238946` secret key. -/
private def skAnchor : ByteArray :=
  hex "47b8192d77bf871b62e87859d653922725724a5c031afeabc60bcef5ff665138"

/-- 32 zero bytes, the message of `sign_case_11b8c7cad5238946`. -/
private def msgZero : ByteArray :=
  hex "0000000000000000000000000000000000000000000000000000000000000000"

/-- Expected signature of `sign(skAnchor, msgZero)`. -/
private def sigAnchor : ByteArray :=
  hex ("b23c46be3a001c63ca711f87a005c200cc550b9429d5f4eb38d74322144f1b63" ++
       "926da3388979e5321012fb1a0526bcd100b5ef5fe72628ce4cd5e904aeaa3279" ++
       "527843fae5ca9ca675f4f51ed8f83bbf7155da9ecc9663100a885d5dc6df96d9")

/-- `Sign` matches the published vector byte-for-byte. -/
example : sign skAnchor msgZero = sigAnchor := by native_decide

/-- `verify_valid_case_195246ee3bd3b6ec` public key / message / signature. -/
private def pkValid : ByteArray :=
  hex ("b53d21a4cfd562c469cc81514d4ce5a6b577d8403d32a394dc265dd190b47fa9" ++
       "f829fdd7963afdf972e5e77854051f6f")

private def msgValid : ByteArray :=
  hex "abababababababababababababababababababababababababababababababab"

private def sigValid : ByteArray :=
  hex ("ae82747ddeefe4fd64cf9cedb9b04ae3e8a43420cd255e3c7cd06a8d88b7c7f8" ++
       "638543719981c5d16fa3527c468c25f0026704a6951bde891360c7e8d12ddee0" ++
       "559004ccdbe6046b55bae1b257ee97f7cdb955773d7cf29adf3ccbb9975e4eb9")

/-- `Verify` accepts the published valid triple. -/
example : verify pkValid msgValid sigValid = true := by native_decide

/-- `Verify` rejects the same signature against a different message. -/
example : verify pkValid msgZero sigValid = false := by native_decide

/-! ### KeyValidate -/

/-- A valid published pubkey passes `KeyValidate`. -/
example : keyValidate pkValid = true := by native_decide

/-- The empty input fails `KeyValidate` (wrong length). -/
example : keyValidate ByteArray.empty = false := by native_decide

/-- An all-zero 48-byte input fails `KeyValidate` (not a valid
compressed point, the compression flag bits are wrong). -/
example : keyValidate (ByteArray.mk (Array.replicate 48 0)) = false := by
  native_decide

/-! ### Self-contained round-trips via `skToPk`

Two small valid secret keys; derive pubkeys, sign, aggregate, verify. -/

private def sk1 : ByteArray :=
  hex "0000000000000000000000000000000000000000000000000000000000000002"
private def sk2 : ByteArray :=
  hex "0000000000000000000000000000000000000000000000000000000000000003"

private def pk1 : ByteArray := skToPk sk1
private def pk2 : ByteArray := skToPk sk2

/-- `skToPk` returns a 48-byte pubkey that passes `KeyValidate`. -/
example : keyValidate pk1 = true := by native_decide

/-- Round-trip: a freshly signed message verifies under the derived key. -/
example : verify pk1 msgValid (sign sk1 msgValid) = true := by native_decide

/-- And fails under the *other* key. -/
example : verify pk2 msgValid (sign sk1 msgValid) = false := by native_decide

/-! ### Aggregate + FastAggregateVerify (same message) -/

/-- Both keys sign the *same* message; the aggregate signature verifies
under the two pubkeys via `FastAggregateVerify`. -/
example :
    fastAggregateVerify #[pk1, pk2] msgValid
      (aggregate #[sign sk1 msgValid, sign sk2 msgValid]) = true := by
  native_decide

/-- The same aggregate fails against a different message. -/
example :
    fastAggregateVerify #[pk1, pk2] msgZero
      (aggregate #[sign sk1 msgValid, sign sk2 msgValid]) = false := by
  native_decide

/-- An empty pubkey list is rejected by `FastAggregateVerify`. -/
example :
    fastAggregateVerify #[] msgValid
      (aggregate #[sign sk1 msgValid]) = false := by native_decide

/-! ### AggregateVerify (distinct messages) -/

/-- Distinct messages, one per key: the aggregate verifies via the
distinct-message `AggregateVerify`. -/
example :
    aggregateVerify #[pk1, pk2] #[msgValid, msgZero]
      (aggregate #[sign sk1 msgValid, sign sk2 msgZero]) = true := by
  native_decide

/-- Swapping the messages breaks it. -/
example :
    aggregateVerify #[pk1, pk2] #[msgZero, msgValid]
      (aggregate #[sign sk1 msgValid, sign sk2 msgZero]) = false := by
  native_decide

/-! ### eth_fast_aggregate_verify special case

The G2 point at infinity: `0xc0` then 95 zero bytes. -/

private def infinitySig : ByteArray :=
  ByteArray.mk (#[0xc0] ++ Array.replicate 95 0)

/-- An empty pubkey list verifies iff the signature is the infinity
point (the consensus `eth_fast_aggregate_verify` special case). -/
example : ethFastAggregateVerify #[] msgValid infinitySig = true := by
  native_decide

/-- A non-empty list behaves like `FastAggregateVerify`. -/
example :
    ethFastAggregateVerify #[pk1, pk2] msgValid
      (aggregate #[sign sk1 msgValid, sign sk2 msgValid]) = true := by
  native_decide

/-! ### G1 point ops (`g1Add` / `g1Neg`)

The pubkey-arithmetic primitives. Beyond basic algebra, these check the
identity behind the sync-aggregate verification optimization:
`aggregate(all) − aggregate(non_participants) = aggregate(participants)`. -/

private def sk3 : ByteArray :=
  hex "0000000000000000000000000000000000000000000000000000000000000005"
private def pk3 : ByteArray := skToPk sk3

/-- The G1 point at infinity, compressed: `0xc0` then 47 zero bytes. -/
private def g1Infinity : ByteArray :=
  ByteArray.mk (#[0xc0] ++ Array.replicate 47 0)

/-- `p + (−p) = ∞`. -/
example : g1Add pk1 (g1Neg pk1) = g1Infinity := by native_decide

/-- Addition is commutative. -/
example : g1Add pk1 pk2 = g1Add pk2 pk1 := by native_decide

/-- `g1Add` matches `eth_aggregate_pubkeys` (incremental vs. batch sum). -/
example : g1Add (ethAggregatePubkeys #[pk1, pk2]) pk3 = ethAggregatePubkeys #[pk1, pk2, pk3] := by
  native_decide

/-- The sync-aggregate optimization identity: subtracting the non-participants
from the full aggregate equals aggregating the participants directly,
`agg({p1,p2,p3}) + (−p3) = agg({p1,p2})`. -/
example : g1Add (ethAggregatePubkeys #[pk1, pk2, pk3]) (g1Neg pk3) = ethAggregatePubkeys #[pk1, pk2] := by
  native_decide

/-- Bad input length ⇒ empty `ByteArray`. -/
example : g1Neg ByteArray.empty = ByteArray.empty := by native_decide

end LeanHazmatBlsTests.Vectors
