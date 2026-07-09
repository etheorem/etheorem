import LeanImtPlus.Sha256

set_option autoImplicit false

/-!
# LeanIMT+ proof verification

This package models the SHA-256 LeanIMT+ verifier circuit from
`protocolwhisper/leanimt-plus`, starting with circuit-equivalent proof
validation and root recomputation.

The design reference is the PSE LeanIMT+ writeup:
https://pse.dev/blog/lean-imt-plus-efficient-merkle-tree-for-membership-and-non-membership-proofs

LeanIMT+ is used here because it is designed for efficient Merkle membership
and non-membership proofs in one structure. This package starts with the
smallest useful, circuit-facing surface: verify a supplied proof and recompute
the committed root.
-/

namespace LeanImtPlus

export Sha256 (
  ProofType
  Leaf
  Proof
  VerifyError
  VerifyResult
  twoPow216
  max216
  fits216
  toBytesBE
  toBE27
  natFromBytesBE
  low216FromDigest
  hash2
  leafHash
  internalHash
  verify
)

end LeanImtPlus
