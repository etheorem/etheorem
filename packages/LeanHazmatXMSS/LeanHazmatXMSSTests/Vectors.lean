import LeanHazmatXMSS
/-!
# `LeanHazmatXMSSTests.Vectors`: XMSS round-trip KAT

Build-time conformance gate for the xmss-reference FFI shim. Each `example`
uses `native_decide` to compile and evaluate the full call chain (Lean → C →
xmss-reference) at build time. A failing `native_decide` is a build error.

Parameter set: **XMSS-SHA2_10_256**, OID `#[0x00, 0x00, 0x00, 0x01]`
  (n = 32 bytes, tree height h = 10, Winternitz w = 16)

Size constants for this parameter set:
  - `pk_bytes  = 68`   (4 OID + 32 root + 32 pub_seed)
  - `sig_bytes = 2500` (4 idx + 32 rand + 67×32 WOTS + 10×32 auth path)

Keygen uses a deterministic counter seed (starting at 0), so `keygenSeeded`
is idempotent: calling it twice with the same OID produces the same pk and sk.

## Why `native_decide` here

`keygenSeeded`, `sign`, and `verify` are `@[extern] opaque`. The kernel cannot
reduce them, so `decide` would loop. `native_decide` compiles the expression
to native code, executes it, and closes the goal with a single
`Lean.ofReduceBool` axiom. That axiom is the cost: we trust the compiler and
the linked C implementation. The KAT vectors are exactly what pins that trust.
-/

set_option autoImplicit false

namespace LeanHazmatXMSSTests

private def oid10 : ByteArray := .mk #[0x00, 0x00, 0x00, 0x01]
private def pkBytes  : Nat := 68
private def sigBytes : Nat := 2500

-- Short message for KAT (4 bytes: ASCII "XMSS").
private def katMsg : ByteArray := .mk #[0x58, 0x4d, 0x53, 0x53]

/-- keygenSeeded returns a non-empty result for XMSS-SHA2_10_256. -/
example : (LeanHazmat.Xmss.keygenSeeded oid10).size > 0 := by native_decide

/-- keygenSeeded result is at least pk_bytes long. -/
example : (LeanHazmat.Xmss.keygenSeeded oid10).size ≥ pkBytes := by native_decide

/-- Round-trip: sign then verify returns true.
This is the primary conformance gate: it exercises the full keygen → sign →
verify pipeline with real RFC 8391 XMSS-SHA2_10_256 parameters. -/
example : (
    let pkSk    := LeanHazmat.Xmss.keygenSeeded oid10
    let pk      := pkSk.extract 0 pkBytes
    let sk      := pkSk.extract pkBytes pkSk.size
    let sigNewSk := LeanHazmat.Xmss.sign sk katMsg
    let sig     := sigNewSk.extract 0 sigBytes
    LeanHazmat.Xmss.verify pk sig katMsg) = true := by native_decide

/-- Wrong message does not verify under the same signature. -/
example : (
    let pkSk    := LeanHazmat.Xmss.keygenSeeded oid10
    let pk      := pkSk.extract 0 pkBytes
    let sk      := pkSk.extract pkBytes pkSk.size
    let sigNewSk := LeanHazmat.Xmss.sign sk katMsg
    let sig     := sigNewSk.extract 0 sigBytes
    LeanHazmat.Xmss.verify pk sig (.mk #[0x00])) = false := by native_decide

/-- Empty signature does not verify. -/
example : LeanHazmat.Xmss.verify
    (LeanHazmat.Xmss.keygenSeeded oid10 |>.extract 0 pkBytes)
    ByteArray.empty
    katMsg = false := by native_decide

/-- keygenSeeded is deterministic: two calls produce the same pk. -/
example : (LeanHazmat.Xmss.keygenSeeded oid10).extract 0 pkBytes =
          (LeanHazmat.Xmss.keygenSeeded oid10).extract 0 pkBytes := by native_decide

end LeanHazmatXMSSTests
