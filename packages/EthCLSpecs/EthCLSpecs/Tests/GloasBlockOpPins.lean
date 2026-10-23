import EthCLSpecs.Gloas.Withdrawals
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Tests.GloasBlockOpPins`: where the Gloas block operations raise

Each pin states what the pinned pyspec (`v1.7.0-alpha.11`, minimal preset) does on the same
input. The probe script that produced the pyspec side is `.tmp/batchfaith/probe_b4.py` (local,
not committed). `IndexError` is `.outOfBounds`, and `ValueError` and `ZeroDivisionError` are
`.arithmetic`.

Every fixture is the `default` state, with one active 32 ETH validator unless a pin says
otherwise.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasBlockOpPins

open EthCLSpecs.Gloas
open EthCLLib.Proofs (runPure pureState)
open EthCLSpecs.Proofs.Gloas (GloasRun)

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

/-- A builder with pubkey byte `0x22` and the given balance. -/
private def builder (balance : Gwei) : Builder :=
  { (default : Builder) with pubkey := Vector.replicate 48 0x22, balance }

/-! ## Q14: `is_active_builder` -/

-- An empty builder registry: the read raises `IndexError`.
example : isOob (isActiveBuilder (pureState oneValidator) 0) = true := by native_decide

/-! ## Q15: `process_proposer_slashing` -/

private def badHeader1 : SignedBeaconBlockHeader :=
  { (default : SignedBeaconBlockHeader) with
    message := { (default : BeaconBlockHeader) with proposerIndex := 5 } }
private def badHeader2 : SignedBeaconBlockHeader :=
  { (default : SignedBeaconBlockHeader) with
    message := { (default : BeaconBlockHeader) with
      proposerIndex := 5, bodyRoot := Vector.replicate 32 1 } }

-- Proposer index 5 raises `IndexError`.
example : isOob (runPure (processProposerSlashing (StateTransition := GloasRun)
    { signedHeader1 := badHeader1, signedHeader2 := badHeader2 }) oneValidator) = true := by
  native_decide

/-! ## Q16: `is_valid_indexed_payload_attestation` -/

-- An index past the registry raises `IndexError`.
example : isOob (isValidIndexedPayloadAttestation (pureState oneValidator)
    { (default : IndexedPayloadAttestation) with attestingIndices := sszOfArray #[5] }) = true := by
  native_decide

/-! ## Q11: `process_builder_deposit_request` -/

-- An existing builder at balance `2 ^ 64 - 1`: the top-up raises `ValueError`.
example : isArith (runPure (processBuilderDepositRequest (StateTransition := GloasRun)
    { (default : BuilderDepositRequest) with pubkey := Vector.replicate 48 0x22, amount := 1 })
    { oneValidator with builders := sszOfArray #[builder u64Max] }) = true := by native_decide

/-! ## Q9, Q10: `process_withdrawals` -/

-- One builder pending withdrawal and `next_withdrawal_index = 2 ^ 64 - 1`: the index add
-- raises `ValueError`.
example : isArith (runPure (processWithdrawals (StateTransition := GloasRun))
    { oneValidator with
      builders := sszOfArray #[builder 0]
      builderPendingWithdrawals := sszOfArray #[{ (default : BuilderPendingWithdrawal) with amount := 1 }]
      nextWithdrawalIndex := u64Max }) = true := by native_decide

-- An empty validator registry: `% len(state.validators)` raises `ZeroDivisionError`.
example : isArith (runPure (processWithdrawals (StateTransition := GloasRun)) default)
    = true := by native_decide

end

end EthCLSpecs.Tests.GloasBlockOpPins
