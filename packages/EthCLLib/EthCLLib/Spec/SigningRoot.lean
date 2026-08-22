import EthCLLib.Spec.Arith
import EthCLLib.Spec.Hasher
import EthCLLib.Spec.Crypto
import EthCLLib.Spec.MerklePath

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

/-- `compute_merkle_branch_root(leaf, branch, depth, index)`
(`beacon-chain.md:782-798`): fold `branch` into `leaf`. Level `i` mixes its
sibling in on the side that bit `i` of `index` picks.

`routeRight` names that side. The pyspec spells the bit `index // (2**i) % 2`
inline, and `routeRight_eq_div_mod` holds the two spellings together. One
definition therefore carries the convention for this check and for the honest
openers both.

A `branch[i]` read past the end raises `IndexError`, which the reference runner's
`expect_assertion_error` catches. The read is therefore a checked reject and not
a defaulted one. The carrier is `IndexError` rather than either machine's reject,
because this function reads no state. A caller routes the miss through `liftErr`
to whichever machine it runs on. -/
def computeMerkleBranchRoot [HasherTag] (leaf : Vector UInt8 32)
    (branch : Array (Vector UInt8 32)) (depth index : Nat) :
    Except SizzLean.Cache.IndexError (Vector UInt8 32) := do
  let value ← (List.range depth).foldlM (init := vecToBytes leaf) fun value i => do
    let sibling ←
      if h : i < branch.size then pure (vecToBytes branch[i])
      else throw (.indexError i branch.size)
    return if routeRight index i
      then Hasher.combine (H := HasherTag.H) sibling value
      else Hasher.combine (H := HasherTag.H) value sibling
  return bytesToRoot value

/-- `is_valid_merkle_branch(leaf, branch, depth, index, root)` (`:800-812`):
reject on `depth != len(branch)`, else compare the reconstructed root. Used by
`processDeposit` against `eth1Data.depositRoot`.

The guard runs first, so the fold reads `branch` only in range. The reject arm is
therefore unreachable from here. The spec returns `False` on the guard and never
reaches its raise either. -/
def isValidMerkleBranch [HasherTag] (leaf : Vector UInt8 32)
    (branch : Array (Vector UInt8 32)) (depth : Nat) (index : Nat)
    (root : Vector UInt8 32) : Bool :=
  if branch.size = depth then
    match computeMerkleBranchRoot leaf branch depth index with
    | .ok value => value == root
    | .error _  => false
  else false

/-- Verify a signature over an SSZ object's signing root: `blsVerify pubkey
(computeSigningRoot obj domain) signature`. The common signature-gate shape, folding the
signing-root construction and the BLS verify into one call so a gate names the object and
the domain. The simple byte-typed `blsVerify` and the aggregate variants live in `Crypto`. -/
@[inline] def blsVerifySigned [HasherTag] [CryptoBackend] {T : Type} [SSZRepr T]
    (pubkey : Vector UInt8 48) (obj : T) (domain : Vector UInt8 32) (signature : Vector UInt8 96) : Bool :=
  blsVerify pubkey (computeSigningRoot obj domain) signature

end EthCLLib.Spec
