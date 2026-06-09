import SizzLean.Hasher.Sha256
import SizzLean.Hasher.Sha256Spec
import LeanHazmatSha256
import LeanSha256.Core

/-!
# `SizzLean.Hasher.Sha256Equiv`: FFI / spec SHA-256 equivalence axioms

## What this file asserts

Two axioms stating that the FFI-backed `LeanHazmat.Sha256.sha256Hash` and
`LeanHazmat.Sha256.sha256Combine` (in the `LeanHazmatSha256` package) compute
the same function on every input as the pure-Lean reference
(`LeanSha256.hash` / `LeanSha256.combine`).

```lean
axiom sha256Hash_eq_spec    : @LeanHazmat.Sha256.sha256Hash    = LeanSha256.hash
axiom sha256Combine_eq_spec : @LeanHazmat.Sha256.sha256Combine = LeanSha256.combine
```

These, together with `sha256BatchCombine_eq_spec` in
`Sha256Batch.lean`, are the SHA-256 *bridge*. They live in SizzLean
because SizzLean is the one layer entitled to import both the FFI
binding (`LeanHazmatSha256`) and the spec (`LeanSha256`); neither
package leaks into the other (hazmat-docs/ARCHITECTURE.md §9).

## Why axioms (and not theorems)

The FFI implementation lives in `LeanHazmatSha256/csrc/sha256_shim.c`
and calls OpenSSL's `EVP_*`. Proving in Lean that the C code computes
SHA-256 would require extracting the C semantics into Lean, not
feasible without heavy machinery (verified C compiler, model of
OpenSSL's internals, etc.).

We instead:

1. **Validate the equivalence empirically.**
   `LeanHazmatSha256Tests/Cavp.lean` runs the FFI against the full
   NIST CAVP suite; `SizzLeanTests/Sha256Equivalence.lean` checks
   that the FFI and the pure-Lean reference agree on a randomised
   input batch.
2. **Promote that validation to a named Lean axiom here.** Proofs can
   now `rw` the FFI calls into their pure-Lean equivalents. At audit
   time, `#axioms theoremName` lists `sha256Hash_eq_spec` /
   `sha256Combine_eq_spec` as the (single, named, replaceable) trust
   assumptions behind the proof.

The trust commitment is the empirical assertion "the FFI shim
implements SHA-256," already validated by the CAVP KAT. Naming it as a
Lean axiom makes the assumption visible in `#axioms` and replaceable
in one place when the corresponding `@[csimp]` proof lands.

## How proofs use these

The typical pattern is to rewrite Sha256-flavoured terms into
Sha256Spec-flavoured ones inside a proof, then close with
`native_decide` (which trusts the compiler's reduction of pure-Lean
code rather than the C shim):

```lean
theorem someBeaconStateRoot :
    (SSZ.FastBox myState).hashTreeRoot = expectedHex := by
  rw [show @LeanHazmat.Sha256.sha256Hash    = LeanSha256.hash    from sha256Hash_eq_spec]
  rw [show @LeanHazmat.Sha256.sha256Combine = LeanSha256.combine from sha256Combine_eq_spec]
  -- Every FFI call is now substituted for its pure-Lean equivalent.
  -- The term is fully kernel-evaluable; native_decide closes via
  -- compiled code-gen of LeanSha256.
  native_decide
```

For pure state-transition proofs that don't need concrete hash values
(only structural equalities), these axioms are *not* required, both
sides of the equality invoke the same opaque `LeanHazmat.Sha256.sha256Hash` /
`sha256Combine` calls and `rfl` / `simp` closes them without ever
caring what the bytes are. Reach for these axioms only when a goal
requires the hash to *actually compute*.

## Trust commitment

The axioms encode an empirical equivalence between two
implementations of SHA-256. A `@[csimp]`-attributed equality
proved from primitives would discharge them, leaving every
dependent proof with identical statements. The axioms are
named so that path can be taken without rewriting downstream
theorems.
-/

set_option autoImplicit false

namespace SizzLean.Hasher

/-- **Axiom**: the FFI-backed `LeanHazmat.Sha256.sha256Hash` (which calls
`LeanHazmatSha256/csrc/sha256_shim.c`'s `lean_hazmat_sha256_hash` via
`@[extern]`) computes the same function as `LeanSha256.hash` (the
pure-Lean NIST-validated reference). Empirically validated by
`LeanHazmatSha256Tests.Cavp` + `SizzLeanTests.Sha256Equivalence`;
promoted here to a named Lean axiom so proofs that depend on it can be
audited via `#axioms`.

A `@[csimp]`-proved theorem with the same statement could replace
this axiom without disturbing dependent proofs. -/
axiom sha256Hash_eq_spec : @LeanHazmat.Sha256.sha256Hash = LeanSha256.hash

/-- **Axiom**: the FFI-backed `LeanHazmat.Sha256.sha256Combine` (which calls
`LeanHazmatSha256/csrc/sha256_shim.c`'s `lean_hazmat_sha256_combine`)
computes SHA-256 over the concatenation of its two inputs, matching
`LeanSha256.combine`'s pure-Lean implementation. Same validation /
auditing story as `sha256Hash_eq_spec`. -/
axiom sha256Combine_eq_spec : @LeanHazmat.Sha256.sha256Combine = LeanSha256.combine

/-! ### Smoke test: the rewrite closes a Sha256 → Sha256Spec goal

A minimal proof that the axioms can be used to convert an FFI hash
call into its pure-Lean equivalent. If either axiom name or statement
drifts, this example stops elaborating. -/

example (b : ByteArray) : LeanHazmat.Sha256.sha256Hash b = LeanSha256.hash b := by
  rw [sha256Hash_eq_spec]

example (l r : ByteArray) :
    LeanHazmat.Sha256.sha256Combine l r = LeanSha256.combine l r := by
  rw [sha256Combine_eq_spec]

end SizzLean.Hasher
