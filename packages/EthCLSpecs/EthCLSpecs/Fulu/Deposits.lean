import EthCLSpecs.Fulu.Rewards

/-!
# `EthCLSpecs.Fulu.Deposits`: deposit application (load order ~row 30)

The deposit-application helpers `process_pending_deposits` and the deposit
operation call: `get_validator_from_deposit`, `add_validator_to_registry`,
`is_valid_deposit_signature`, `apply_pending_deposit` (`SPECS_ARCHITECTURE.md`
§3.1, the deposit concern). `apply_pending_deposit` checks the deposit
proof-of-possession through the `[CryptoBackend]` seam, so the section carries it;
Lean attaches it only where used.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_validator_from_deposit`. -/
forkdef getValidatorFromDeposit (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei) : Validator :=
  let v : Validator :=
    { pubkey, withdrawalCredentials := wc, effectiveBalance := 0, slashed := false,
      activationEligibilityEpoch := Const.farFutureEpoch, activationEpoch := Const.farFutureEpoch,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { v with effectiveBalance := umin (amount - amount % Const.effectiveBalanceIncrementG) (getMaxEffectiveBalance v) }

/-- `add_validator_to_registry`: append a fresh validator and its parallel records. -/
forkdef addValidatorToRegistry (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei) : StateTransition Unit :=
  modifyState fun state =>
    sszUpdate state with
      validators := (sszGet state validators).push (getValidatorFromDeposit pubkey wc amount),
      balances := (sszGet state balances).push amount,
      previousEpochParticipation := (sszGet state previousEpochParticipation).push 0,
      currentEpochParticipation := (sszGet state currentEpochParticipation).push 0,
      inactivityScores := (sszGet state inactivityScores).push 0

/-- `is_valid_deposit_signature`: the proof-of-possession check. The domain is
fixed (`compute_domain(DOMAIN_DEPOSIT)`, the genesis fork version and a zero
`genesis_validators_root`, since a deposit predates genesis), so verification is a
single BLS gate through the `[CryptoBackend]` seam. -/
forkdef isValidDepositSignature (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei)
    (signature : BLSSignature) : Bool :=
  let msg : DepositMessage := { pubkey, withdrawalCredentials := wc, amount }
  let domain := computeDomain Const.domainDeposit Const.genesisForkVersion
    (Vector.replicate 32 0)
  let signingRoot := computeSigningRoot msg domain
  blsVerify pubkey signingRoot signature

/-- `apply_pending_deposit`: top up an existing validator's balance, or, for a new
pubkey with a valid proof-of-possession, add it to the registry. -/
forkdef applyPendingDeposit (deposit : PendingDeposit) : StateTransition Unit := do
  let state ← get
  match validatorIndexByPubkey? state deposit.pubkey with
  | some vi => modifyState fun state => increaseBalance state (UInt64.ofNat vi) deposit.amount
  | none    =>
      if isValidDepositSignature deposit.pubkey deposit.withdrawalCredentials deposit.amount deposit.signature then
        addValidatorToRegistry deposit.pubkey deposit.withdrawalCredentials deposit.amount
      else pure ()

end

end EthCLSpecs.Fulu
