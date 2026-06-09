import SizzLean.Hasher.Class
import LeanSha256.Core

/-!
# `SizzLean.Hasher.Sha256Spec`: `Hasher Sha256Spec` instance bridge

A thin bridge between the standalone `LeanSha256` library (the
actual pure-Lean SHA-256 implementation lives there) and
SizzLean's `Hasher` typeclass.

## What's here

* The `Sha256Spec` phantom tag, a distinct nominal type from `Sha256`
  (the FFI-backed tag in `FFI/Sha256.lean`); call sites pick between
  them via the `Hasher H` instance binder.
* A single `instance : Hasher Sha256Spec` whose methods delegate
  to `LeanSha256.hash` and `LeanSha256.combine`.

## What lives in `LeanSha256` instead

The actual SHA-256 implementation: FIPS 180-4 constants, round
functions, message schedule, compression, padding, byte/word
conversions, `hash`, `combine`, NIST §B acceptance asserts, and
the full structural-conformance lemma set. `LeanSha256` has no
dependency on SSZ machinery; anyone wanting a Lean-kernel-reducible
SHA-256 reference imports it directly.

This split keeps the SHA-256 implementation reusable outside the
Ethereum SSZ context. The `Sha256Spec` tag and its `Hasher` instance
exist *here* because the `Hasher` typeclass is SSZ-side abstraction;
the SHA-256 functions themselves are independent.
-/

set_option autoImplicit false

namespace SizzLean.Hasher

/-- Phantom tag for the pure-Lean SHA-256 `Hasher` instance. Empty
`inductive` keeps it nominally distinct from `Sha256` (the
FFI-backed tag in `Hasher/Sha256.lean`); call sites pick between
them via the `Hasher H` instance binder. -/
inductive Sha256Spec : Type

/-- Pure-Lean `Hasher Sha256Spec` instance. Both methods delegate
to the standalone `LeanSha256` library. `hash` runs SHA-256 over
an arbitrary `ByteArray`, `combine` does the two-input
concatenation variant. -/
instance : Hasher Sha256Spec where
  hash    := LeanSha256.hash
  combine := LeanSha256.combine

end SizzLean.Hasher
