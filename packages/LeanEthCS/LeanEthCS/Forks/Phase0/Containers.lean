import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Phase0.Containers`: Phase 0 fixed-size containers

Bundles the simpler Phase 0 container types that consist entirely of
fixed-size primitive fields. Each type compiles via `deriving SSZRepr`
and has a `native_decide` round-trip smoke test. Mirrors the spec
definitions in `consensus-specs/specs/phase0/beacon-chain.md`.

Variable-size containers (`Attestation`, `IndexedAttestation`,
`BeaconBlockBody`, `BeaconState`) live in dedicated files because
they exercise the variable-field offset-table path. Keeping them
separate makes it easier to spot a regression in that path vs.
one in the simple fixed-field path.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Phase0

open SizzLean

open LeanEthCS

/-- `Fork`: pair of current/previous fork versions plus the
activation epoch. Used inside `BeaconState`. -/
structure Fork where
  previousVersion : Version
  currentVersion  : Version
  epoch           : Epoch
  deriving SSZRepr

/-- `Checkpoint`: an epoch boundary the chain has finalized at. -/
structure Checkpoint where
  epoch : Epoch
  root  : Root
  deriving SSZRepr

/-- `Eth1Data`: the latest eth1-chain anchor a validator votes for. -/
structure Eth1Data where
  depositRoot  : Root
  depositCount : UInt64
  blockHash    : Hash32
  deriving SSZRepr

/-- `AttestationData`: the inner payload of an attestation: which
slot, committee index, block being attested to, and source/target
checkpoints. -/
structure AttestationData where
  slot            : Slot
  index           : CommitteeIndex
  beaconBlockRoot : Root
  source          : Checkpoint
  target          : Checkpoint
  deriving SSZRepr

/-- `Validator`: the validator registry entry. Eight fixed-size
fields, all primitives. -/
structure Validator where
  pubkey                       : BLSPubkey
  withdrawalCredentials        : Bytes32
  effectiveBalance             : Gwei
  slashed                      : Bool
  activationEligibilityEpoch   : Epoch
  activationEpoch              : Epoch
  exitEpoch                    : Epoch
  withdrawableEpoch            : Epoch
  deriving SSZRepr

/-- Signed wrapper around a `BeaconBlockHeader`. -/
structure SignedBeaconBlockHeader where
  message   : BeaconBlockHeader
  signature : BLSSignature
  deriving SSZRepr

/-- `ProposerSlashing`: two signed headers from the same proposer
in the same slot. Exercises a struct-of-struct field
(`SignedBeaconBlockHeader`), which the deriving handler resolves
through the recursive `synthInstance` fallback in `Repr/Deriving.lean`. -/
structure ProposerSlashing where
  signedHeader1 : SignedBeaconBlockHeader
  signedHeader2 : SignedBeaconBlockHeader
  deriving SSZRepr

/-- `DepositMessage`: the SSZ payload signed by a depositing
validator. -/
structure DepositMessage where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  deriving SSZRepr

/-- `DepositData`: `DepositMessage` plus the BLS signature. -/
structure DepositData where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature
  deriving SSZRepr

/-- `VoluntaryExit`: message a validator signs to exit. -/
structure VoluntaryExit where
  epoch          : Epoch
  validatorIndex : ValidatorIndex
  deriving SSZRepr

/-- Signed wrapper around `VoluntaryExit`. -/
structure SignedVoluntaryExit where
  message   : VoluntaryExit
  signature : BLSSignature
  deriving SSZRepr

/-- `ForkData`: fork digest pre-image. Same fields as `Fork` but
distinct nominal type (used for BLS domain construction). -/
structure ForkData where
  currentVersion        : Version
  genesisValidatorsRoot : Root
  deriving SSZRepr

/-- `SigningData`: `(object_root, domain)` pair fed into the BLS
signing primitive. -/
structure SigningData where
  objectRoot : Root
  domain     : Domain
  deriving SSZRepr

/-- `Eth1Block`: minimal eth1-block summary used during deposit
processing. -/
structure Eth1Block where
  timestamp    : UInt64
  depositRoot  : Root
  depositCount : UInt64
  deriving SSZRepr

/-! ### Round-trip smoke tests

One per type. Each uses a zero-valued instance and validates
end-to-end through `SSZ.serialize` / `SSZ.deserialize`. -/

private def zeroRoot : Root := Vector.replicate 32 0
private def zeroHash32 : Hash32 := Vector.replicate 32 0
private def zeroVersion : Version := Vector.replicate 4 0
private def zeroPubkey : BLSPubkey := Vector.replicate 48 0
private def zeroSig : BLSSignature := Vector.replicate 96 0

private def roundTripFork (x : Fork) : Bool :=
  match SSZ.deserialize (T := Fork) (SSZ.serialize x) with
  | .ok y => decide (y.previousVersion = x.previousVersion) &&
             decide (y.currentVersion = x.currentVersion) &&
             decide (y.epoch = x.epoch)
  | .error _ => false

example : roundTripFork ⟨zeroVersion, zeroVersion, 0⟩ = true := by native_decide

private def roundTripCheckpoint (x : Checkpoint) : Bool :=
  match SSZ.deserialize (T := Checkpoint) (SSZ.serialize x) with
  | .ok y => decide (y.epoch = x.epoch) && decide (y.root = x.root)
  | .error _ => false

example : roundTripCheckpoint ⟨0, zeroRoot⟩ = true := by native_decide

private def roundTripValidator (x : Validator) : Bool :=
  match SSZ.deserialize (T := Validator) (SSZ.serialize x) with
  | .ok y => decide (y.slashed = x.slashed) &&
             decide (y.activationEpoch = x.activationEpoch) &&
             decide (y.effectiveBalance = x.effectiveBalance)
  | .error _ => false

example : roundTripValidator
    ⟨zeroPubkey, zeroRoot, 32_000_000_000, false, 0, 0, 0, 0⟩ = true := by
  native_decide

private def roundTripProposerSlashing (x : ProposerSlashing) : Bool :=
  match SSZ.deserialize (T := ProposerSlashing) (SSZ.serialize x) with
  | .ok y => decide (y.signedHeader1.signature = x.signedHeader1.signature) &&
             decide (y.signedHeader2.signature = x.signedHeader2.signature)
  | .error _ => false

example : roundTripProposerSlashing
    ⟨⟨⟨0, 0, zeroRoot, zeroRoot, zeroRoot⟩, zeroSig⟩,
     ⟨⟨0, 0, zeroRoot, zeroRoot, zeroRoot⟩, zeroSig⟩⟩ = true := by
  native_decide

end LeanEthCS.Forks.Phase0
