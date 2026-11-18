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

/-- `get_active_validator_indices`. -/
forkdef getActiveValidatorIndices (state : State) (epoch : Epoch) : Array ValidatorIndex :=
  indicesWhere (sszGet state validators).toArray (fun v _ => isActiveValidator v epoch)

/-- `get_eligible_validator_indices` (for rewards / inactivity,
`fulu/mainnet.py:1799-1806`). The comprehension's `previous_epoch + 1` is the pyspec's
checked `Epoch` add, and Python's `or` / `and` short-circuit, so the sum forms only for a
slashed validator the previous epoch left inactive; the fold binds it inside that branch
(`SPEC_ARITHMETIC.md` §4.3) and the result carries the fault. -/
forkdef getEligibleValidatorIndices (state : State) : Checked (Array ValidatorIndex) := do
  let prevEpoch := previousEpochOf state
  let validators := (sszGet state validators).toArray
  (List.range validators.size).foldlM (init := #[]) fun out i => do
    let validator := validators[i]!
    if isActiveValidator validator prevEpoch then
      pure (out.push (UInt64.ofNat i))
    else if validator.slashed then
      let nextEpoch ← prevEpoch + 1
      if nextEpoch < validator.withdrawableEpoch then pure (out.push (UInt64.ofNat i))
      else pure out
    else pure out

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
