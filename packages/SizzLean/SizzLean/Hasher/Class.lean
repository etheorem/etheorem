/-!
# `SizzLean.Hasher`: abstract hash typeclass

This file declares the single typeclass that Layers 1 (Spec) and 4
(Tree) parameterise over for every Merkleization step. There are no
instances here; the FFI SHA-256 instance lives in
`SizzLean/Hasher/Sha256.lean`, and the pure-Lean reference instance
in `SizzLean/Hasher/Sha256Spec.lean`.

Threading a `Hasher` typeclass through every `merkleRoot*` call site
from the start, rather than hardcoding SHA-256, is the
forward-compatibility hedge for the Beam Chain post-quantum redesign
(Poseidon2 et al.). The class is small precisely so that swap is
a one-instance change. See `ARCHITECTURE.md` §9 for the full
trust-boundary discussion.

The class parameter `H` is a phantom *tag* type, for example `Sha256`,
eventually `Poseidon2`, used to disambiguate instances at the call
site. The methods do not consume `H`; Lean resolves them through the
surrounding `[Hasher H]` instance binder.
-/

set_option autoImplicit false

namespace SizzLean


/-- Abstract 32-byte hash typeclass consumed by Spec and Tree.

Both `hash` and `combine` are documented to return a 32-byte
`ByteArray`. We intentionally do *not* encode that as a subtype: the
Day-1 instance is an `@[extern] opaque` FFI shim returning plain
`ByteArray`, and the central correctness theorems (Layer 2) do not
touch hashes, so a refinement here would buy nothing and complicate
the FFI boundary. Callers may rely on the 32-byte invariant as a
documentation-level contract enforced by each instance. -/
class Hasher (H : Type) where
  /-- 32-byte digest of an arbitrary input.

  Used at SSZ Merkleization leaves where the input is a chunk-packed
  buffer (basic types, `Bitvector`, `Bitlist`) before the tree-step
  recursion takes over. -/
  hash    : ByteArray → ByteArray
  /-- 32-byte digest of two 32-byte inputs concatenated, the inner
  Merkle step.

  Pulled out as its own method (rather than `hash (l ++ r)`) so that
  production instances can dispatch directly to a SHA-NI / AVX-512
  two-block primitive without a redundant copy at every interior
  tree node. -/
  combine : ByteArray → ByteArray → ByteArray

/-- Typecheck-only acceptance: `[Hasher H]` is usable downstream
even before any instance is defined. The class opens as an instance
binder and both fields project cleanly.

The `(H := H)` named-argument form on `Hasher.combine` and
`Hasher.hash` is *load-bearing*: because `H` is a
phantom tag (it doesn't appear in either method's argument or
result types), instance synthesis can't recover it from `b₁ b₂`.
Naming it explicitly resolves the ambiguity. Downstream files
(`Spec/HashTreeRoot.lean`, etc.) follow the same convention. -/
example {H : Type} [Hasher H] (b₁ b₂ : ByteArray) : ByteArray :=
  Hasher.combine (H := H) (Hasher.hash (H := H) b₁) b₂

end SizzLean
