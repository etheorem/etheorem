import EthCLSpecs.Fulu.Balances

/-!
# `EthCLSpecs.Fulu.Registry`: the registry read accessors (load order row 24)

`get_active_validator_indices` and `get_eligible_validator_indices`, the read-only
walks over the validator registry (`SPECS_ARCHITECTURE.md` §3.1 row 24). These sit
**below** `Committees` (which needs the active set) and below the registry
*mutators* (`initiateValidatorExit`, `slashValidator`), which need
`getBeaconProposerIndex` and so float above `Committees` into `RegistryUpdates`,
the read/write seam of §3.3. Splitting the registry concern this way, reads low /
writes high, is what the seam forces; it is not a by-kind split for its own sake.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- The indices of `get_active_validator_indices`, cast with a wrapping `UInt64.ofNat`.
`getActiveValidatorIndices` runs the spec's cast check first, so it returns this only where
every kept index fits. -/
forkdef activeValidatorIndicesOf (state : State) (epoch : Epoch) : Array ValidatorIndex :=
  indicesWhere (sszGet state validators).toArray (fun v _ => isActiveValidator v epoch)

/-- `get_active_validator_indices` (`phase0/beacon-chain.md:1469-1478`). The comprehension
builds `ValidatorIndex(index)` for each active validator, and that cast raises `ValueError`
for an index at `2 ^ 64` or above (`.arithmetic`). The comprehension has no other effect, so
the body tests for such an index first, and otherwise returns `activeValidatorIndicesOf`. -/
forkdef getActiveValidatorIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  if keepsIndexPast64 (sszGet state validators).toArray (isActiveValidator · epoch) then
    throwArithmetic "get_active_validator_indices: ValidatorIndex(index) at 2**64 or above"
  pure (activeValidatorIndicesOf state epoch)

/-- The eligibility test of `get_eligible_validator_indices` at the previous epoch. -/
forkdef isEligibleValidator (state : State) (validator : Validator) : Bool :=
  let prevEpoch := previousEpochOf state
  isActiveValidator validator prevEpoch || (validator.slashed && prevEpoch + 1 < validator.withdrawableEpoch)

/-- The indices of `get_eligible_validator_indices`, cast with a wrapping `UInt64.ofNat`, as
`activeValidatorIndicesOf` does. -/
forkdef eligibleValidatorIndicesOf (state : State) : Array ValidatorIndex :=
  indicesWhere (sszGet state validators).toArray (fun validator _ => isEligibleValidator state validator)

/-- `get_eligible_validator_indices` (`phase0/beacon-chain.md:2037-2045`, for rewards and
inactivity). The same `ValidatorIndex(index)` cast as `get_active_validator_indices` raises at
`2 ^ 64` or above. -/
forkdef getEligibleValidatorIndices (state : State) :
    Except StateTransitionError (Array ValidatorIndex) := do
  if keepsIndexPast64 (sszGet state validators).toArray (isEligibleValidator state ·) then
    throwArithmetic "get_eligible_validator_indices: ValidatorIndex(index) at 2**64 or above"
  pure (eligibleValidatorIndicesOf state)

/-- The registry index of the first validator whose `pubkey` equals `pk`, or `none` when no
validator carries that pubkey. The single home for the
`(sszGet state validators).findIdx? (·.pubkey == …)` scan that the deposit, withdrawal-request,
consolidation, and pending-deposit paths each re-spell. Returns the raw `Nat` index `findIdx?`
produces, not a narrowed `ValidatorIndex`: most callers need the index in both forms in the same
branch (as a `Nat` to read the registry or a parallel list, as a `UInt64` to hand a balance / exit
mutator), so the per-caller narrowing is left at the call site and only the scan and the pubkey
key are centralized. -/
forkdef validatorIndexByPubkey? (state : State) (pk : BLSPubkey) : Option Nat :=
  (sszGet state validators).findIdx? (·.pubkey == pk)

end

end EthCLSpecs.Fulu
