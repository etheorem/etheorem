import LeanHazmatBls
import LeanHazmatKzg
import EthCLLib.Spec.Errors
import EthCLLib.Spec.Arith
import Std.Data.HashMap

/-!
# `EthCLLib.Spec.Crypto`: the `[CryptoBackend]` seam

The framework owns the domain-agnostic crypto mechanics; the spec owns the
consensus-aware part (`FRAMEWORK_ARCHITECTURE.md` §11). The signature- and
commitment-based primitives, BLS verify / aggregate and the KZG cell-proof
batch, sit behind the `[CryptoBackend]` seam so a consumer substitutes the
FFI backend (runner), a verify-off mode (a vector's `bls_setting: 2`), or a
symbolic backend (proofs) at the call boundary, never touching the spec.

The seam's currency is raw `ByteArray` wire buffers (pubkey 48, signature 96,
commitment 48, proof 48, cell 2048 bytes; cell index `UInt64`), matching the
crypto FFI exactly. The spec converts its SSZ-typed pubkeys / signatures (byte
vectors) to `ByteArray` before calling, so the seam carries no SSZ dependency.

Three backends ship here: `ffi` (the real FFI primitives, used by the runner),
`verifyOff` (signature checks short-circuit to accept, for `bls_setting: 2`
vectors), and `symbolic` (all checks accept, for the proofs config). Memoization
of repeated hashes is handled structurally by SizzLean's cached `Box`, so the
crypto seam itself stays a thin pass-through.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The crypto seam. BLS verification / aggregate and the KZG cell-proof batch,
the primitives whose backend a consumer swaps. Buffers are raw wire bytes. -/
class CryptoBackend where
  /-- BLS `verify pubkey message signature`. -/
  verify : ByteArray → ByteArray → ByteArray → Bool
  /-- BLS same-message aggregate verify over a pubkey set
  (`processSyncAggregate`'s primitive). -/
  fastAggregateVerify : Array ByteArray → ByteArray → ByteArray → Bool
  /-- The consensus `eth_fast_aggregate_verify`: an empty pubkey set verifies iff
  the signature is the G2 point-at-infinity. -/
  ethFastAggregateVerify : Array ByteArray → ByteArray → ByteArray → Bool
  /-- BLS `eth_aggregate_pubkeys`: the group sum of a pubkey set, a 48-byte G1
  point. The sync-committee selection's `aggregate_pubkey`. This is a
  deterministic aggregation, not a verification gate, so the verify-off backend
  keeps the real FFI. -/
  aggregatePubkeys : Array ByteArray → ByteArray
  /-- KZG cell-proof batch over equal-length arrays of commitments, cell indices,
  cells, and proofs (Fulu PeerDAS). Not a single-cell call. -/
  kzgVerifyCellProofBatch :
    Array ByteArray → Array UInt64 → Array ByteArray → Array ByteArray → Bool

namespace CryptoBackend

/-- The production backend: every primitive delegates straight to the committed
crypto FFI (blst for BLS, c-kzg for KZG). The runner injects this (later wrapped
by the caching backend). -/
@[reducible] def ffi : CryptoBackend where
  verify                  := LeanHazmat.Bls.verify
  fastAggregateVerify     := LeanHazmat.Bls.fastAggregateVerify
  ethFastAggregateVerify  := LeanHazmat.Bls.ethFastAggregateVerify
  aggregatePubkeys        := LeanHazmat.Bls.ethAggregatePubkeys
  kzgVerifyCellProofBatch := LeanHazmat.Kzg.verifyCellKzgProofBatch

/-- The `bls_setting: 2` verify-off backend: BLS verification is forced `true`,
so a case the upstream generator made invalid only by a dummy signature is not
falsely rejected. KZG stays real (it is not gated by `bls_setting`). Keeps the
reject-faithfulness audit honest (`FRAMEWORK_ARCHITECTURE.md` §11.1). -/
@[reducible] def verifyOff : CryptoBackend where
  verify _ _ _                  := true
  fastAggregateVerify _ _ _     := true
  ethFastAggregateVerify _ _ _  := true
  aggregatePubkeys              := LeanHazmat.Bls.ethAggregatePubkeys
  kzgVerifyCellProofBatch       := LeanHazmat.Kzg.verifyCellKzgProofBatch

/-- The symbolic backend the pure configuration injects: BLS verification is
assumed-true (an uninterpreted gate a transition theorem case-splits on, never
executes), so proofs carry no compiler axioms for crypto. KZG is likewise
assumed-true. -/
@[reducible] def symbolic : CryptoBackend where
  verify _ _ _                  := true
  fastAggregateVerify _ _ _     := true
  ethFastAggregateVerify _ _ _  := true
  aggregatePubkeys _            := ⟨Array.replicate 48 0⟩
  kzgVerifyCellProofBatch _ _ _ _ := true

/-! ## The caching backend (`FRAMEWORK_ARCHITECTURE.md` §11.1, §14)

BLS `verify` is the dominant repeated primitive: the same committee / sync-aggregate
/ deposit signatures recur across a sweep, and a pairing check is milliseconds. A
memo over the exact `(pubkey, message, signature)` wire bytes turns the repeats into
a hash + map lookup. Because the seam's `verify` is a *pure* `Bool`, the memo lives
behind an `@[implemented_by]` swap: the logical definition stays the FFI primitive
(so transparency is `rfl`), and only the compiled code consults the global cache. -/

/-- Global memo for BLS `verify`, keyed by the exact `(pubkey, message, signature)`
wire bytes, so a hit is always the right answer. -/
initialize verifyCache : IO.Ref (Std.HashMap (ByteArray × ByteArray × ByteArray) Bool) ←
  IO.mkRef ∅

/-- The memoized `verify`: look the triple up, and on a miss run the FFI and store
the result. Unsafe (a mutable global behind a pure signature); reached only through
`@[implemented_by]`. -/
unsafe def cachedVerifyImpl (pk msg sig : ByteArray) : Bool :=
  unsafeBaseIO do
    let cache ← verifyCache.get
    match cache.get? (pk, msg, sig) with
    | some r => return r
    | none =>
      let r := LeanHazmat.Bls.verify pk msg sig
      verifyCache.modify (·.insert (pk, msg, sig) r)
      return r

/-- BLS `verify`, *logically* the FFI primitive, with the compiled implementation
memoized through `cachedVerifyImpl`. -/
@[implemented_by cachedVerifyImpl]
def cachedVerify (pk msg sig : ByteArray) : Bool := LeanHazmat.Bls.verify pk msg sig

/-- Transparency: the caching `verify` is *definitionally* the FFI `verify`, so the
memo can never disagree with the real primitive; the `@[implemented_by]` swap is the
runtime memo only. This is the §14 cache-transparency guarantee, by construction. -/
example (pk msg sig : ByteArray) : cachedVerify pk msg sig = LeanHazmat.Bls.verify pk msg sig := rfl

/-- The caching backend the runner injects: `verify` is memoized; the rest delegate to
the FFI (aggregate and the KZG batch are not the repeated hot path). -/
@[reducible] def caching : CryptoBackend where
  verify                  := cachedVerify
  fastAggregateVerify     := LeanHazmat.Bls.fastAggregateVerify
  ethFastAggregateVerify  := LeanHazmat.Bls.ethFastAggregateVerify
  aggregatePubkeys        := LeanHazmat.Bls.ethAggregatePubkeys
  kzgVerifyCellProofBatch := LeanHazmat.Kzg.verifyCellKzgProofBatch

/-- Whether the BLS-`verify` memo is disabled, read once from the
`ETHCL_DISABLE_CRYPTO_CACHE` environment variable at process start. The runner's
switch for cache-on versus cache-off; unset (the default) keeps caching on. -/
initialize cryptoCacheDisabled : Bool ← do
  let v ← IO.getEnv "ETHCL_DISABLE_CRYPTO_CACHE"
  return v.isSome

/-- The runner's real-crypto backend: `caching` by default, or the plain `ffi` backend
when `cryptoCacheDisabled`. The `bls_setting: 2` verify-off override is applied at the
call site (it depends on per-case metadata), so this covers the caching toggle alone. -/
@[reducible] def realBackend : CryptoBackend := if cryptoCacheDisabled then ffi else caching

/-- Select the backend for a vector's `bls_setting`: `2` is the verify-off mode (a case
the upstream generator made invalid only by a dummy signature), anything else the real
backend. The single home for the `bls_setting` policy, so a `PySpecTests` entry point writes
`CryptoBackend.forBlsSetting cmeta.blsSetting` rather than re-spelling the `== 2` test. -/
@[reducible] def forBlsSetting (blsSetting : Nat) : CryptoBackend :=
  if blsSetting == 2 then verifyOff else realBackend

end CryptoBackend

/-! ## Spec-facing BLS wrappers

The seam's currency is the raw `ByteArray`; the spec's pubkeys, signatures, and roots are
SSZ byte vectors (`BLSPubkey = Vector UInt8 48`, `BLSSignature = Vector UInt8 96`,
`Root = Vector UInt8 32`). These thin wrappers do the `vecToBytes` conversion at the seam,
so a call site names the values it verifies and the seam's wire-byte detail stays here. The
signing-root combinator `blsVerifySigned`, which folds in `computeSigningRoot`, lives in
`SigningRoot` beside the signing-root helpers it composes. -/

/-- BLS `verify` over the spec's SSZ-typed pubkey, signing root, and signature. -/
@[inline] def blsVerify [CryptoBackend] (pubkey : Vector UInt8 48) (signingRoot : Vector UInt8 32)
    (signature : Vector UInt8 96) : Bool :=
  CryptoBackend.verify pubkey signingRoot signature

/-- BLS same-message aggregate verify over a pubkey set (the indexed-attestation aggregate). -/
@[inline] def blsFastAggregateVerify [CryptoBackend] (pubkeys : Array (Vector UInt8 48))
    (signingRoot : Vector UInt8 32) (signature : Vector UInt8 96) : Bool :=
  CryptoBackend.fastAggregateVerify (pubkeys.map vecToBytes) signingRoot signature

/-- The consensus `eth_fast_aggregate_verify` (the sync-aggregate primitive; an empty pubkey
set verifies iff the signature is the G2 point at infinity). -/
@[inline] def blsEthFastAggregateVerify [CryptoBackend] (pubkeys : Array (Vector UInt8 48))
    (signingRoot : Vector UInt8 32) (signature : Vector UInt8 96) : Bool :=
  CryptoBackend.ethFastAggregateVerify (pubkeys.map vecToBytes) signingRoot signature

/-- `eth_aggregate_pubkeys`: the group sum of a pubkey set, as a 48-byte G1 point. -/
@[inline] def blsAggregatePubkeys [CryptoBackend] (pubkeys : Array (Vector UInt8 48)) : Vector UInt8 48 :=
  bytesToVec 48 (CryptoBackend.aggregatePubkeys (pubkeys.map vecToBytes))

end EthCLLib.Spec
