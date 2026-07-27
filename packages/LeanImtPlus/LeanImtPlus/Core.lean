import LeanImtPlus.Hasher.Class

set_option autoImplicit false

/-!
# Hash-generic LeanIMT+ proofs

This module contains the linked-leaf commitment format and unified membership /
non-membership verifier. It knows how LeanIMT+ combines values, but it does not
import or select a concrete hash implementation.
-/

namespace LeanImtPlus

/-- The semantic kind of a unified LeanIMT+ proof. -/
inductive ProofType where
  | membership
  | nonMembership
  deriving BEq, DecidableEq, Repr

/-- A linked LeanIMT+ leaf: `nextValue` is the next active value in order. -/
structure Leaf where
  value : Nat
  nextValue : Nat
  deriving BEq, Inhabited, Repr

/-- A unified proof using the digest representation selected by `H`. -/
structure Proof (H : Type) [Hasher H] where
  proofType : ProofType
  root : Digest H
  value : Nat
  leaf : Leaf
  leafIndex : Nat
  depth : Nat
  siblings : Array (Digest H)
  deriving BEq, Repr

/-- Failures raised while validating or authenticating a unified proof. -/
inductive VerifyError where
  | invalidMaxDepth
  | zeroValue
  | valueOutOfRange
  | leafValueOutOfRange
  | leafNextValueOutOfRange
  | rootOutOfRange
  | siblingOutOfRange (index : Nat)
  | membershipLeafMismatch
  | nonMembershipRange
  | tombstoneReplay
  | depthTooLarge
  | notEnoughSiblings
  | nonCanonicalSiblings
  | nonCanonicalIndex
  | rootMismatch
  deriving BEq, DecidableEq, Repr

/-- Result of reconstructing a root without authenticating it. -/
abbrev RecomputeResult (H : Type) [Hasher H] :=
  Except VerifyError (Digest H)

/-- Result of authenticating a unified proof. -/
abbrev VerifyResult := Except VerifyError Unit

private def okOr (cond : Bool) (err : VerifyError) : VerifyResult :=
  if cond then .ok () else .error err

private def checkSiblings {H : Type} [Hasher H]
    (siblings : Array (Digest H)) (depth : Nat) : VerifyResult := do
  for i in [0:depth] do
    let sibling := siblings[i]!
    okOr (Hasher.validDigest (H := H) sibling) (.siblingOutOfRange i)

private def checkProofShape {H : Type} [Hasher H]
    (maxDepth : Nat) (proof : Proof H) : VerifyResult := do
  okOr (maxDepth < 252) .invalidMaxDepth
  okOr (proof.value != 0) .zeroValue
  okOr (Hasher.validValue (H := H) proof.value) .valueOutOfRange
  okOr (Hasher.validValue (H := H) proof.leaf.value) .leafValueOutOfRange
  okOr (Hasher.validValue (H := H) proof.leaf.nextValue) .leafNextValueOutOfRange
  okOr (proof.depth <= maxDepth) .depthTooLarge
  okOr (proof.siblings.size >= proof.depth) .notEnoughSiblings
  checkSiblings proof.siblings proof.depth
  okOr (proof.leafIndex < 2 ^ proof.depth) .nonCanonicalIndex

private def checkMembershipSemantics {H : Type} [Hasher H]
    (proof : Proof H) : VerifyResult := do
  match proof.proofType with
  | .membership =>
      okOr (proof.leaf.value == proof.value) .membershipLeafMismatch
  | .nonMembership =>
      let lowerOk := proof.leaf.value < proof.value
      let upperOk := proof.value < proof.leaf.nextValue || proof.leaf.nextValue == 0
      okOr (lowerOk && upperOk) .nonMembershipRange
      okOr (proof.leaf.value != 0 || proof.leafIndex == 0) .tombstoneReplay

/-- LeanIMT+ leaf commitment with the reference leaf-domain tag. -/
def leafHash {H : Type} [Hasher H] (leaf : Leaf) : Digest H :=
  let value := Hasher.ofNat (H := H) leaf.value
  let nextValue := Hasher.ofNat (H := H) leaf.nextValue
  let tag := Hasher.ofNat (H := H) 1
  Hasher.compress (H := H) (Hasher.compress (H := H) value nextValue) tag

/-- Internal-node commitment for the selected hasher. -/
def internalHash {H : Type} [Hasher H] (left right : Digest H) : Digest H :=
  Hasher.compress (H := H) left right

private def recomputeFrom {H : Type} [Hasher H] (node : Digest H)
    (leafIndex : Nat) (siblings : Array (Digest H)) (depth : Nat) : Digest H :=
  Id.run do
    let mut acc := node
    for i in [0:depth] do
      let sibling := siblings[i]!
      if ((leafIndex >>> i) &&& 1) == 0 then
        acc := internalHash acc sibling
      else
        acc := internalHash sibling acc
    return acc

/-- Recompute a proof root without comparing it with the committed root. -/
def recomputeRoot {H : Type} [Hasher H]
    (maxDepth : Nat) (proof : Proof H) : RecomputeResult H := do
  checkProofShape maxDepth proof
  checkMembershipSemantics proof
  return recomputeFrom (leafHash proof.leaf) proof.leafIndex proof.siblings proof.depth

/-- Verify a unified proof against the root carried by the proof. -/
def verify {H : Type} [Hasher H] (maxDepth : Nat) (proof : Proof H) : VerifyResult := do
  okOr (Hasher.validDigest (H := H) proof.root) .rootOutOfRange
  let computedRoot ← recomputeRoot maxDepth proof
  okOr (computedRoot == proof.root) .rootMismatch

/-- Verify a canonical proof using its compressed path length as the depth cap. -/
def verifyProof {H : Type} [Hasher H] (proof : Proof H) : VerifyResult :=
  if proof.siblings.size != proof.depth then
    .error .nonCanonicalSiblings
  else
    verify proof.depth proof

end LeanImtPlus
