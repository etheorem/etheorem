import EthCLSpecs.Fulu.Transition
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Tests.FuluBlockOpPins`: where the Fulu block operations raise

Each pin states what the pinned pyspec (`v1.7.0-alpha.11`, minimal preset) does on the same
input. The probe script that produced the pyspec side is `.tmp/batchfaith/probe_b4.py` (local,
not committed). `IndexError` is `.outOfBounds`, `ValueError` is `.arithmetic`.

Every fixture is the `default` state with one active 32 ETH validator.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluBlockOpPins

open EthCLSpecs.Fulu
open EthCLLib.Proofs (runPure pureState)
open EthCLSpecs.Proofs.Fulu (FuluRun)

section
-- The pins share one preset, config, hasher and crypto backend. The instances stay local to
-- this section.
local instance : Preset := minimal
local instance : Config := minimalConfig
local instance : HasherTag := fastHasherTag
local instance : CryptoBackend := CryptoBackend.realBackend

/-- The result raised the uncaught-fault kind (`.arithmetic`). -/
private def isArith {α : Type} : Except StateTransitionError α → Bool
  | .error (.arithmetic _) => true
  | _ => false

/-- The result raised the index-read kind (`.outOfBounds`). -/
private def isOob {α : Type} : Except StateTransitionError α → Bool
  | .error (.outOfBounds _ _) => true
  | _ => false

private def u64Max : UInt64 := 18446744073709551615
private def eth32 : Gwei := 32000000000

/-- The `default` state with one active 32 ETH validator. -/
private def oneValidator : BeaconState :=
  { (default : BeaconState) with
    validators := sszOfArray #[{ (default : Validator) with
      pubkey := Vector.replicate 48 0x11, effectiveBalance := eth32
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }]
    balances := sszOfArray #[eth32]
    previousEpochParticipation := sszOfArray #[0]
    currentEpochParticipation := sszOfArray #[0]
    inactivityScores := sszOfArray #[0] }

/-! ## P11: `is_valid_indexed_attestation` -/

-- An index past the registry raises `IndexError`.
example : isOob (isValidIndexedAttestation (pureState oneValidator)
    { (default : IndexedAttestation) with attestingIndices := sszOfArray #[5] }) = true := by
  native_decide

-- An empty index list returns `False` before any read.
example : (isValidIndexedAttestation (pureState oneValidator) default matches .ok false) = true := by
  native_decide

/-! ## Q7: `get_pending_balance_to_withdraw` -/

-- Two pending amounts of `2 ^ 63` for validator 0: the sum raises `ValueError`.
private def halfMax : PendingPartialWithdrawal :=
  { (default : PendingPartialWithdrawal) with validatorIndex := 0, amount := 9223372036854775808 }
example : isArith (getPendingBalanceToWithdraw (pureState
    { oneValidator with pendingPartialWithdrawals := sszOfArray #[halfMax, halfMax] }) 0)
    = true := by native_decide

/-! ## Q8: `slash_validator` -/

-- `slashings[0] = 2 ^ 64 - 1`: adding the effective balance raises `ValueError`.
example : isArith (runPure (slashValidator (StateTransition := FuluRun) 0)
    { oneValidator with slashings := oneValidator.slashings.set! 0 u64Max }) = true := by
  native_decide

/-! ## Q15, Q17, Q18: validator reads past the registry -/

-- `process_proposer_slashing` with proposer index 5 raises `IndexError`.
private def badHeader1 : SignedBeaconBlockHeader :=
  { (default : SignedBeaconBlockHeader) with
    message := { (default : BeaconBlockHeader) with proposerIndex := 5 } }
private def badHeader2 : SignedBeaconBlockHeader :=
  { (default : SignedBeaconBlockHeader) with
    message := { (default : BeaconBlockHeader) with
      proposerIndex := 5, bodyRoot := Vector.replicate 32 1 } }
example : isOob (runPure (processProposerSlashing (StateTransition := FuluRun)
    { signedHeader1 := badHeader1, signedHeader2 := badHeader2 }) oneValidator) = true := by
  native_decide

-- `process_voluntary_exit` with validator index 5 raises `IndexError`.
example : isOob (runPure (processVoluntaryExit (StateTransition := FuluRun)
    { (default : SignedVoluntaryExit) with
      message := { (default : VoluntaryExit) with validatorIndex := 5 } }) oneValidator) = true := by
  native_decide

-- `verify_block_signature` with proposer index 5 raises `IndexError`.
example : isOob (verifyBlockSignature (pureState oneValidator)
    { (default : SignedBeaconBlock) with
      message := { (default : BeaconBlock) with proposerIndex := 5 } }) = true := by
  native_decide

end

end EthCLSpecs.Tests.FuluBlockOpPins
