import LeanSha256

set_option autoImplicit false

namespace LeanImtPlus
namespace Sha256

inductive ProofType where
  | membership
  | nonMembership
  deriving BEq, DecidableEq, Repr

structure Leaf where
  value : Nat
  nextValue : Nat
  deriving BEq, Repr

structure Proof where
  proofType : ProofType
  value : Nat
  leaf : Leaf
  leafIndex : Nat
  depth : Nat
  siblings : Array Nat
  deriving BEq, Repr

inductive VerifyError where
  | zeroValue
  | valueOutOfRange
  | leafValueOutOfRange
  | leafNextValueOutOfRange
  | siblingOutOfRange (index : Nat)
  | membershipLeafMismatch
  | nonMembershipRange
  | tombstoneReplay
  | depthTooLarge
  | notEnoughSiblings
  | nonCanonicalIndex
  deriving BEq, DecidableEq, Repr

abbrev VerifyResult := Except VerifyError Nat

def twoPow216 : Nat := 2 ^ 216
def max216 : Nat := twoPow216 - 1

def fits216 (n : Nat) : Bool :=
  n < twoPow216

private def byteAtBE (width : Nat) (n : Nat) (i : Nat) : UInt8 :=
  Nat.toUInt8 ((n >>> (8 * (width - 1 - i))) &&& 0xff)

/-- Encode `n` as a fixed-width, big-endian byte string. -/
def toBytesBE (width : Nat) (n : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := width) fun i => byteAtBE width n i.val)

/-- Circuit input encoding: 216 bits = 27 big-endian bytes. -/
def toBE27 (n : Nat) : ByteArray :=
  toBytesBE 27 n

def natFromBytesBE (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Low 216 bits of a SHA-256 digest, matching circomlib's `Sha256_2` output. -/
def low216FromDigest (digest : ByteArray) : Nat :=
  natFromBytesBE digest % twoPow216

/--
Hash two LeanIMT+ SHA-256 field inputs.

Each input is encoded as a 27-byte big-endian integer. The 256-bit SHA-256
digest is truncated to its low 216 bits.
-/
def hash2 (a b : Nat) : Nat :=
  low216FromDigest (LeanSha256.hash (toBE27 a ++ toBE27 b))

/--
LeanIMT+ leaf commitment.

The extra `1` is the leaf-domain tag used by the referenced verifier circuit:
`hash2 (hash2 value nextValue) 1`. It separates leaf commitments from internal
node commitments, which use the same `hash2` primitive with untagged children.
-/
def leafHash (leaf : Leaf) : Nat :=
  hash2 (hash2 leaf.value leaf.nextValue) 1

/-- Internal node commitment: the circuit's plain two-child SHA-256 hash. -/
def internalHash (left right : Nat) : Nat :=
  hash2 left right

private def okOr (cond : Bool) (err : VerifyError) : Except VerifyError Unit :=
  if cond then .ok () else .error err

private def check216 (n : Nat) (err : VerifyError) : Except VerifyError Unit :=
  okOr (fits216 n) err

private def checkSiblings216 (siblings : Array Nat) (depth : Nat) :
    Except VerifyError Unit := do
  for i in [0:depth] do
    let sib := siblings[i]!
    check216 sib (.siblingOutOfRange i)

private def checkProofShape (maxDepth : Nat) (proof : Proof) :
    Except VerifyError Unit := do
  okOr (proof.value != 0) .zeroValue
  check216 proof.value .valueOutOfRange
  check216 proof.leaf.value .leafValueOutOfRange
  check216 proof.leaf.nextValue .leafNextValueOutOfRange
  okOr (proof.depth <= maxDepth) .depthTooLarge
  okOr (proof.siblings.size >= proof.depth) .notEnoughSiblings
  checkSiblings216 proof.siblings proof.depth
  okOr (proof.leafIndex < 2 ^ proof.depth) .nonCanonicalIndex

private def checkMembershipSemantics (proof : Proof) :
    Except VerifyError Unit := do
  match proof.proofType with
  | .membership =>
      okOr (proof.leaf.value == proof.value) .membershipLeafMismatch
  | .nonMembership =>
      let lowerOk := proof.leaf.value < proof.value
      let upperOk := proof.value < proof.leaf.nextValue || proof.leaf.nextValue == 0
      okOr (lowerOk && upperOk) .nonMembershipRange
      okOr (proof.leaf.value != 0 || proof.leafIndex == 0) .tombstoneReplay

private def recomputeFrom (node : Nat) (leafIndex : Nat)
    (siblings : Array Nat) (depth : Nat) : Nat :=
  Id.run do
    let mut acc := node
    for i in [0:depth] do
      let sibling := siblings[i]!
      if ((leafIndex >>> i) &&& 1) == 0 then
        acc := internalHash acc sibling
      else
        acc := internalHash sibling acc
    return acc

/--
Circuit-equivalent SHA-256 LeanIMT+ verifier.

`maxDepth` is the circuit template parameter. On success, the returned value is
the recomputed root.
-/
def verify (maxDepth : Nat) (proof : Proof) : VerifyResult := do
  checkProofShape maxDepth proof
  checkMembershipSemantics proof
  return recomputeFrom (leafHash proof.leaf) proof.leafIndex proof.siblings proof.depth

end Sha256
end LeanImtPlus
