import EthCLLib.Spec.Arith
import EthCLLib.Spec.Hasher
import EthCLLib.Spec.Crypto

/-!
# `EthCLLib.Spec.SigningRoot`: the hashing-based crypto primitives

The framework-owned, domain-agnostic half of the crypto layer
(`FRAMEWORK_ARCHITECTURE.md` §11): the signing-root combinators
(`computeForkDataRoot`, `computeDomain`, `computeSigningRoot`) and the
Merkle-proof check (`isValidMerkleBranch`). They hash over small byte containers
through the `[HasherTag]` hasher and take fork-version / domain values without
reading any `State`, so they stay framework-side. The spec owns `getDomain` (it
reads `state.fork`) and the `DOMAIN_*` constants.
-/

set_option autoImplicit false

open SizzLean
open SizzLean.Hasher
open SizzLean.Repr

namespace EthCLLib.Spec

/-- Hash-tree-root of any SSZ value as a 32-byte `Vector`, via the `[HasherTag]`
hasher. The spec's `Root` is `Vector UInt8 32`, so this is its `hash_tree_root`. -/
@[inline] def htr {T : Type} [HasherTag] [SSZRepr T] (x : T) : Vector UInt8 32 :=
  bytesToRoot (SSZ.hashTreeRoot HasherTag.H x)

/-- The spec's `hash(b)`: a 32-byte digest through the `[HasherTag]` hasher. Used
by the shuffle / seed derivation. -/
@[inline] def sha [HasherTag] (b : ByteArray) : ByteArray := Hasher.hash (H := HasherTag.H) b

/-- `ForkData = {current_version, genesis_validators_root}`; framework-internal,
hashed by `computeForkDataRoot`. -/
structure ForkData where
  currentVersion        : Vector UInt8 4
  genesisValidatorsRoot : Vector UInt8 32
  deriving SSZRepr

/-- `SigningData = {object_root, domain}`; framework-internal, hashed by
`computeSigningRoot`. -/
structure SigningData where
  objectRoot : Vector UInt8 32
  domain     : Vector UInt8 32
  deriving SSZRepr

/-- `compute_fork_data_root(current_version, genesis_validators_root)`. -/
def computeForkDataRoot [HasherTag] (currentVersion : Vector UInt8 4)
    (genesisValidatorsRoot : Vector UInt8 32) : Vector UInt8 32 :=
  htr { currentVersion, genesisValidatorsRoot : ForkData }

/-- `compute_domain` = `domain_type ‖ compute_fork_data_root(fork_version, gvr)[:28]`
(32 bytes; `domain_type` is the 4-byte `DOMAIN_*` tag). -/
def computeDomain [HasherTag] (domainType : ByteArray) (forkVersion : Vector UInt8 4)
    (genesisValidatorsRoot : Vector UInt8 32) : Vector UInt8 32 :=
  let fdr := computeForkDataRoot forkVersion genesisValidatorsRoot
  Vector.ofFn (fun i : Fin 32 => if i.val < 4 then domainType.get! i.val else vget fdr (i.val - 4))

/-- `compute_signing_root(obj, domain)` = `htr(SigningData{htr(obj), domain})`. -/
def computeSigningRoot [HasherTag] {T : Type} [SSZRepr T] (obj : T)
    (domain : Vector UInt8 32) : Vector UInt8 32 :=
  htr { objectRoot := htr obj, domain : SigningData }

/-- `is_valid_merkle_branch(leaf, branch, depth, index, root)`: walk `depth`
sibling hashes from `leaf`, mixing each in on the left or right by `index`'s bit,
and compare to `root`. Used by `processDeposit` against `eth1Data.depositRoot`. -/
def isValidMerkleBranch [HasherTag] (leaf : Vector UInt8 32)
    (branch : Array (Vector UInt8 32)) (depth : Nat) (index : Nat)
    (root : Vector UInt8 32) : Bool :=
  let value : ByteArray := (List.range depth).foldl (init := vecToBytes leaf) fun acc i =>
    let sibling := vecToBytes (branch[i]!)
    if (index >>> i) &&& 1 == 1
    then Hasher.combine (H := HasherTag.H) sibling acc
    else Hasher.combine (H := HasherTag.H) acc sibling
  bytesToRoot value == root

/-- Verify a signature over an SSZ object's signing root: `blsVerify pubkey
(computeSigningRoot obj domain) signature`. The common signature-gate shape, folding the
signing-root construction and the BLS verify into one call so a gate names the object and
the domain. The simple byte-typed `blsVerify` and the aggregate variants live in `Crypto`. -/
@[inline] def blsVerifySigned [HasherTag] [CryptoBackend] {T : Type} [SSZRepr T]
    (pubkey : Vector UInt8 48) (obj : T) (domain : Vector UInt8 32) (signature : Vector UInt8 96) : Bool :=
  blsVerify pubkey (computeSigningRoot obj domain) signature

end EthCLLib.Spec
