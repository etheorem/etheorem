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

/-- `get_validator_from_deposit` (`fulu/mainnet.py:2104-2124`). The Electra
floor `min(amount - amount % EFFECTIVE_BALANCE_INCREMENT, max_effective_balance)`
is the checked `Gwei` chain, so the rounding subtraction binds before the `min`
picks its operand and the result carries the fault. -/
forkdef getValidatorFromDeposit (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei) :
    Checked Validator := do
  let v : Validator :=
    { pubkey, withdrawalCredentials := wc, effectiveBalance := 0, slashed := false,
      activationEligibilityEpoch := Const.farFutureEpoch, activationEpoch := Const.farFutureEpoch,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  let rounded ← amount - amount % Const.effectiveBalanceIncrementG
  return { v with effectiveBalance := min rounded (getMaxEffectiveBalance v) }

/-- `add_validator_to_registry` (`electra/beacon-chain.md:1736-1746`): write a fresh
validator and its parallel records at `get_index_for_new_validator`, the length of
`validators`. Each write is `set_or_append_list`, in spec order. On a state whose parallel
lists match `validators` in length, every write appends, and an append to a full list
raises `.listFull`. -/
forkdef addValidatorToRegistry (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei) : StateTransition Unit := do
  let state ← get
  -- `get_index_for_new_validator(state)` (`fulu/minimal.py:4317-4318`):
  -- `ValidatorIndex(len(state.validators))`, the pyspec's checked cast of the plain length.
  let index ← CLUint64.ofNat? state.validators.val.size
  let validator ← getValidatorFromDeposit pubkey wc amount
  setOrAppendState validators index validator
  setOrAppendState balances index amount
  setOrAppendState previousEpochParticipation index 0
  setOrAppendState currentEpochParticipation index 0
  setOrAppendState inactivityScores index 0

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
  | some vi =>
      -- `ValidatorIndex(validator_pubkeys.index(deposit.pubkey))`: the pyspec's checked cast.
      let index ← CLUint64.ofNat? vi
      set (← increaseBalance state index deposit.amount)
  | none    =>
      if isValidDepositSignature deposit.pubkey deposit.withdrawalCredentials deposit.amount deposit.signature then
        addValidatorToRegistry deposit.pubkey deposit.withdrawalCredentials deposit.amount
      else pure ()

end

end EthCLSpecs.Fulu
