import SizzLean.Hasher.Class
import LeanHazmatSha256

/-!
# `SizzLean.Hasher.Sha256`: FFI SHA-256 `Hasher` instance

The `Hasher Sha256` instance, wiring the abstract `Hasher` typeclass
(`SizzLean/Hasher/Class.lean`) to the OpenSSL-backed FFI primitives in
the `LeanHazmatSha256` package (`LeanHazmat.Sha256.sha256Hash` /
`LeanHazmat.Sha256.sha256Combine`). Any downstream code with `[Hasher Sha256]`
in scope picks this up at instance synthesis.

## What moved out, and why

The `@[extern] opaque` SHA-256 bindings themselves no longer live
here: they were migrated to the standalone `LeanHazmatSha256` package
(hazmat-docs/ARCHITECTURE.md §9, PLAN.md Stage 1) so the FFI surface
ships independently of the SSZ library. SizzLean keeps only the
*spec-side* glue, this `Sha256` tag and instance, plus the
FFI ≡ pure-Lean equivalence axioms in `Sha256Equiv.lean` /
`Sha256Batch.lean`. SizzLean is the one layer entitled to import both
the FFI binding (`LeanHazmatSha256`) and the pure-Lean spec
(`LeanSha256`), which is exactly what the equivalence axioms need.

## Why the `Sha256` phantom tag

`class Hasher (H : Type)` carries `H` as a *phantom* type parameter.
It appears in the class binder but not in any method signature. Its
job is to disambiguate instances at the call site: `[Hasher Sha256]`
selects this OpenSSL-backed instance, leaving room for the pure-Lean
`Sha256Spec` (in `Hasher/Sha256Spec.lean`) or a future `Poseidon2`.
Using an empty `inductive` for the tag keeps it nominal, two distinct
tag types resolve to two distinct instances even if their
implementations coincide.
-/

set_option autoImplicit false

namespace SizzLean.Hasher

/-- Phantom tag for the FFI-backed SHA-256 `Hasher` instance. Empty
`inductive` so the type is nominal and distinct from any other hash
backend (e.g. `Sha256Spec`, the pure-Lean reference).
`Hasher.combine (H := Sha256) ...` selects this instance
unambiguously. -/
inductive Sha256 : Type

/-- The FFI-backed `Hasher Sha256` instance. Both methods delegate to
the `LeanHazmatSha256` externs (`LeanHazmat.Sha256.sha256Hash` for the
single-input digest, `LeanHazmat.Sha256.sha256Combine` for the two-input
inner-Merkle step). The trust assumption (the shim implements NIST
SHA-256) lives with those externs; the FFI ≡ pure-Lean equivalence
axioms in `Sha256Equiv.lean` make it auditable. -/
instance : Hasher Sha256 where
  hash    := LeanHazmat.Sha256.sha256Hash
  combine := LeanHazmat.Sha256.sha256Combine

end SizzLean.Hasher
