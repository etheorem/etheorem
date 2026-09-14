import LeanHazmatXmss
import LeanHazmatXmss.Kat
/-!
# `LeanHazmatXmssTests.Vectors`: XMSS Known-Answer-Tests

Build-time conformance gate for the xmss-reference FFI shim. Each `example`
uses `native_decide` to compile and evaluate the full call chain (Lean → C →
xmss-reference) at build time. A failing `native_decide` is a build error.

Parameter set: **XMSS-SHA2_10_256**, OID `#[0x00, 0x00, 0x00, 0x01]`
  (n = 32 bytes, tree height h = 10, Winternitz w = 16).

## What pins the trust

RFC 8391 ships no official test vectors. The next best ground truth is
xmss-reference's own reference-vector generator, `test/vectors.c`, which uses
the fixed seed `0x00, 0x01, …` and prints `shake128(pk_core, 10)` and
`shake128(sig, 10)`. We use the same seed and check those exact digests, so
the anchors are validated against upstream's own driver (a different code path
from this FFI shim), not merely against our own extraction:

* `upstreamPkDigest` / `upstreamSigDigest` reproduce the two values
  `test/vectors.c` prints for XMSS-SHA2_10_256 (oid 1): `7de72d192121f414d4bb`
  for the public key, and `8b6cb278d50a3694ca38` for a signature made at leaf
  index `2^(h-1) = 512` over the one-byte message `0x25`, upstream's exact
  setup. Agreement cross-validates keygen and sign against the reference.
* `sizesAnchor` fixes the buffer sizes `(pk, sig, sk) = (68, 2500, 136)`.
  A wrong size table (a real past bug) fails here immediately.
* `pkAnchor` fixes the whole 68-byte public key in raw form (its core hashes to
  `upstreamPkDigest`), pinning the Merkle root byte for byte.
* `sigPrefixAnchor` fixes the first 64 bytes of an index-0 signature over
  "XMSS", pinning the natural-usage signing path.

A byte-for-byte regression in any of these fails the build. The round-trip and
negative cases below then check that verification accepts a genuine signature
and rejects tampered inputs.

## Why `native_decide` here

`keygenFromSeed`, `sign`, and `verify` are `@[extern] opaque`. The kernel
cannot reduce them, so `decide` would loop. `native_decide` compiles the
expression to native code, executes it, and closes the goal with a single
`Lean.ofReduceBool` axiom. That axiom is the cost: we trust the compiler and
the linked C implementation (CLAUDE.md "Proofs involving SSZ hashes"
generalises to all FFI crypto).

## Lean idioms used here

* `hex`: a compile-time hex-string → `ByteArray` decoder, so the anchor bytes
  read as the hex the extractor printed. `native_decide` evaluates it by
  running compiled code.
-/

set_option autoImplicit false

namespace LeanHazmatXmssTests.Vectors

open LeanHazmat.Xmss

/-! ### Hex helper -/

/-- Value of a single hex digit (`0` for any non-hex char; inputs here are
always well-formed). -/
private def hexVal (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else 0

/-- Pair adjacent hex digits into bytes. Structural recursion on the char list
(each step drops two elements). -/
private def hexBytes : List Char → List UInt8
  | a :: b :: rest => (hexVal a * 16 + hexVal b) :: hexBytes rest
  | _ => []

/-- Decode a hex string (no `0x` prefix) into a `ByteArray`. -/
private def hex (s : String) : ByteArray := ⟨(hexBytes s.toList).toArray⟩

/-- SHAKE128 digest, from the KAT-support module (see `LeanHazmatXmss.Kat`).
Used only to reproduce upstream's `test/vectors.c` digests. -/
private def shake128 (data : ByteArray) (outLen : USize) : ByteArray :=
  LeanHazmat.Xmss.Kat.shake128 data outLen

/-! ### Parameter set and inputs -/

private def oid10 : ByteArray := .mk #[0x00, 0x00, 0x00, 0x01]

/-- Fixed, publicly derivable seed: bytes `0x00, 0x01, …, 0x5f`. Length is
`3·n = 96` for n = 32 (`sk_seed ‖ sk_prf ‖ pub_seed`). Reproducible, and never
a real key (see the danger note on `keygenFromSeed`). -/
private def seed : ByteArray := .mk ((List.range 96).map (fun i => i.toUInt8)).toArray

/-- Short KAT message: ASCII "XMSS". -/
private def katMsg : ByteArray := .mk #[0x58, 0x4d, 0x53, 0x53]

/-- Sizes read from `paramSizes`, so the slicing below never retypes the
constants. `sizesAnchor` pins the concrete values. -/
private def pkBytes  : Nat := match paramSizes oid10 with | some (p, _, _) => p | none => 0
private def sigBytes : Nat := match paramSizes oid10 with | some (_, s, _) => s | none => 0

/-! ### Anchors (xmss-reference output for `seed`, extracted once) -/

/-- The full 68-byte public key for `keygenFromSeed oid10 seed`: OID (4) ‖
Merkle root (32) ‖ pub_seed (32). The pub_seed tail is `seed[64..95]`. -/
private def pkAnchor : ByteArray :=
  hex ("000000019d898033e37af48e6a116f8b15651cc26773467007ad19375d38c23c" ++
       "690c3483404142434445464748494a4b4c4d4e4f505152535455565758595a5b" ++
       "5c5d5e5f")

/-- The first 64 bytes of `sign sk katMsg`: leaf index (4, zero for the first
signature) ‖ randomness `r` (32) ‖ start of the WOTS+ signature. -/
private def sigPrefixAnchor : ByteArray :=
  hex ("0000000011c3e8f92a6565812dad1b5e748d117a17f1f9f07336cf6c1eaa3a2b" ++
       "77071cb24a382f08d5fdd5f9c553541aa898f5a2b0f4e492a34c83e5c8b30289")

/-! ### Size KAT -/

/-- `paramSizes` returns the exact `(pk, sig, sk)` sizes for XMSS-SHA2_10_256.
A regression in the size table fails here. -/
example : paramSizes oid10 = some (68, 2500, 136) := by native_decide

/-- An unrecognized OID is rejected. -/
example : paramSizes (.mk #[0xff, 0xff, 0xff, 0xff]) = none := by native_decide

/-! ### Keygen and sign KATs -/

/-- Keygen from the fixed seed reproduces the committed public key byte for
byte. This pins the Merkle root, so a broken tree computation fails even when
the round-trip below would still succeed. -/
example : (keygenFromSeed oid10 seed).extract 0 pkBytes = pkAnchor := by native_decide

/-- Keygen is a pure function of `(oid, seed)`: a different seed gives a
different key. -/
example :
    (keygenFromSeed oid10 seed).extract 0 pkBytes ≠
    (keygenFromSeed oid10 (.mk (Array.replicate 96 0))).extract 0 pkBytes := by
  native_decide

/-- The first 64 signature bytes match the committed anchor, pinning the
signing path. -/
example :
    let pkSk := keygenFromSeed oid10 seed
    let sk   := pkSk.extract pkBytes pkSk.size
    ((sign sk katMsg).extract 0 64) = sigPrefixAnchor := by native_decide

/-! ### Upstream reference-vector cross-check (`test/vectors.c`)

The two digests xmss-reference's own `test/vectors.c` prints for oid 1. Matching
them validates keygen and sign against the reference driver, a different code
path from this shim, closing the "self-extracted anchor" gap. -/

/-- `shake128(pk_core, 10)` printed by upstream `test/vectors.c` for oid 1. -/
private def upstreamPkDigest : ByteArray := hex "7de72d192121f414d4bb"

/-- `shake128(sig, 10)` printed by upstream `test/vectors.c` for oid 1: a
signature at leaf index `2^(h-1) = 512` over the one-byte message `0x25`. -/
private def upstreamSigDigest : ByteArray := hex "8b6cb278d50a3694ca38"

/-- The core public key (dropping the 4-byte OID) hashes to upstream's printed
public-key digest. -/
example :
    shake128 ((keygenFromSeed oid10 seed).extract 4 pkBytes) 10 = upstreamPkDigest := by
  native_decide

/-- Reproducing upstream's exact signature setup (leaf index 512, message
`0x25`) and hashing the signature matches upstream's printed signature digest.
The index lives in the 4 big-endian bytes of the secret key right after the
OID; `512 = 0x00000200`. -/
example :
    let pkSk := keygenFromSeed oid10 seed
    -- sk layout: OID(4) ‖ index(4) ‖ SK_SEED ‖ SK_PRF ‖ root ‖ PUB_SEED.
    let sk   := (pkSk.extract pkBytes pkSk.size).set! 4 0 |>.set! 5 0
                  |>.set! 6 2 |>.set! 7 0
    let sig  := (sign sk (.mk #[0x25])).extract 0 sigBytes
    shake128 sig 10 = upstreamSigDigest := by native_decide

/-! ### Round-trip and negative cases -/

/-- Round-trip: a signature over `katMsg` verifies under the derived pk. -/
example :
    let pkSk := keygenFromSeed oid10 seed
    let pk   := pkSk.extract 0 pkBytes
    let sk   := pkSk.extract pkBytes pkSk.size
    let sig  := (sign sk katMsg).extract 0 sigBytes
    verify pk sig katMsg = true := by native_decide

/-- A different message does not verify under the same signature. -/
example :
    let pkSk := keygenFromSeed oid10 seed
    let pk   := pkSk.extract 0 pkBytes
    let sk   := pkSk.extract pkBytes pkSk.size
    let sig  := (sign sk katMsg).extract 0 sigBytes
    verify pk sig (.mk #[0x00]) = false := by native_decide

/-- A signature with one flipped WOTS+ byte does not verify. This exercises the
verification path itself, not the C size guard. -/
example :
    let pkSk := keygenFromSeed oid10 seed
    let pk   := pkSk.extract 0 pkBytes
    let sk   := pkSk.extract pkBytes pkSk.size
    let sig  := (sign sk katMsg).extract 0 sigBytes
    let bad  := sig.set! 40 (sig.get! 40 ^^^ 0xff)
    verify pk bad katMsg = false := by native_decide

end LeanHazmatXmssTests.Vectors
