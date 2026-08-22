set_option autoImplicit false

/-!
# LeanIMT+ hash interface

The LeanIMT+ tree, unified proof, and verifier depend on this interface rather
than on a concrete hash implementation. The digest type is associated with the
hasher tag: SHA-256 adapters use 216-bit `Nat` digests, while Poseidon2 uses a
canonical BN254 field element.

This class deliberately lives in LeanImtPlus. Importing SizzLean's byte-oriented
SSZ hasher would couple two otherwise independent libraries and would not model
LeanIMT+'s scheme-specific value encoding.
-/

namespace LeanImtPlus

/-- Hash operations and validity rules required by LeanIMT+.

`H` is a phantom tag selecting an implementation. `ofNat` embeds a valid leaf
value into the digest domain; `compress` is the two-to-one operation used for
both tagged leaves and internal nodes. -/
class Hasher (H : Type) where
  /-- Committed value stored in roots and sibling paths. -/
  Digest : Type
  /-- Default value used only by total array access in the tree builder. -/
  digestInhabited : Inhabited Digest
  /-- Boolean digest equality used by verification. -/
  digestBEq : BEq Digest
  /-- Readable digest output for proofs and test failures. -/
  digestRepr : Repr Digest
  /-- Whether a `Nat` has a canonical, collision-free encoding for this scheme. -/
  validValue : Nat → Bool
  /-- Whether a supplied root or sibling is canonical for this scheme. -/
  validDigest : Digest → Bool
  /-- Embed a validated LeanIMT+ value into the digest domain. -/
  ofNat : Nat → Digest
  /-- Two-to-one hash or algebraic compression function. -/
  compress : Digest → Digest → Digest

/-- The digest selected by hasher tag `H`. -/
abbrev Digest (H : Type) [Hasher H] : Type :=
  Hasher.Digest H

@[reducible] instance {H : Type} [hasher : Hasher H] : Inhabited (Digest H) :=
  hasher.digestInhabited

@[reducible] instance {H : Type} [hasher : Hasher H] : BEq (Digest H) :=
  hasher.digestBEq

@[reducible] instance {H : Type} [hasher : Hasher H] : Repr (Digest H) :=
  hasher.digestRepr

/-- Numerals in backend-specific fixtures use the backend's canonical embedding. -/
@[reducible] instance {H : Type} [Hasher H] (n : Nat) : OfNat (Digest H) n :=
  ⟨Hasher.ofNat (H := H) n⟩

end LeanImtPlus
