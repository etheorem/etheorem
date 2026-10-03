# LeanHazmatP256: Architecture

The single-family trust-boundary record for `LeanHazmatP256`. The
cross-family view is
[`../../docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md).

## What this package is

NIST P-256 (secp256r1) ECDSA verification in namespace
`LeanHazmat.P256`:

| Primitive | C symbol |
| --- | --- |
| `p256Verify` | `lean_hazmat_p256_verify` |

Five 32-byte big-endian fields (hash, `r`, `s`, public-key `x`,
public-key `y`) → `Bool`. The precompile's 160-byte input layout, gas
schedule, and `0x…01` success encoding stay with the consumer.

## Backend

The system OpenSSL `libcrypto`, discovered via `pkg-config` exactly as
in `LeanHazmatSha256` (helpers duplicated per §3.3). The shim uses the
OpenSSL 3.x provider API, no deprecated `EC_KEY` / `ECDSA_*` calls:

* The public key is imported with `EVP_PKEY_fromdata` from the group
  name `prime256v1` plus the uncompressed `0x04 ‖ x ‖ y` point. The
  import is the validator: coordinates ≥ p and off-curve points fail
  there.
* The raw `(r, s)` pair is DER-encoded by hand as an ECDSA-Sig-Value
  (RFC 5480) and verified with `EVP_PKEY_verify`: the data is the
  already-computed hash, the documented EVP equivalent of the legacy
  `ECDSA_verify`. So the semantics match the legacy call: `r` or
  `s` zero and failed equations reject. All failures collapse to
  `false`.

**No high-s rejection**: the provider's ECDSA verification has no
anti-malleability policy, which matches EIP-7951 exactly (its suite
marks a malleability case valid).

## Trust boundary

No pure-Lean reference exists; the binding is an opaque `@[extern]`
boundary. The empirical trust assumption is *that the linked OpenSSL
libcrypto implements NIST P-256 ECDSA verification correctly*,
validated by `LeanHazmatP256Tests` against the **official EIP-7951
vector set**, the EIP's `assets/eip-7951/test-vectors.json` (781
Project Wycheproof cases), from which the suite pins:

* Three valid cases, including the signature-malleability case that
  fixes the no-high-s-rejection behavior, and a large-y-coordinate key.
* Two invalid cases: an `r` adjusted by the group order, and a
  signature from the duplication bug.
* Negatives: a flipped hash bit and an off-curve point.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for an FFI KAT. The selected vectors are
hard-coded into `LeanHazmatP256Tests/Vectors.lean`, keeping the build
hermetic; bumping EIP-7951 vector coverage means re-selecting from the
JSON in lockstep.
