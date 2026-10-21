import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Proofs.Fulu.Balances
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.SSZListGetElem
import SizzLean.Proofs.SSZListSet
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Fulu.ConsolidationRequest`: `processConsolidationRequest`'s request gates and success arms

`process_consolidation_request` (EIP-7251) runs its request through a ladder of gates, and
this file gives each gate one theorem. A gate theorem's hypotheses carry the request past
every earlier gate and then fire the named gate, so the generator's `decide` on the witness
guarantees the vector reaches that gate. The theorems sit in the function's gate order.
A shared lemma reduces the run to the validator ladder over the plain registry reads, and
each gate theorem after the match rewrites with it and fires its own gate.

Upstream tests live in `electra/block_processing/test_process_consolidation_request.py` at
pin `v1.7.0-alpha.11`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag SSZList ErrorConv IndexError sszGetIdx umax vecSliceEq)
open EthCLSpecs.Fulu (Preset Config BLSPubkey BeaconState ConsolidationRequest Gwei Validator
  ValidatorIndex Bytes32 Epoch ParticipationFlags PendingConsolidation
  PendingPartialWithdrawal
  computeActivationExitEpoch computeConsolidationEpochAndUpdateChurn computeEpochAtSlot
  getConsolidationChurnLimit hasCompoundingWithdrawalCredential hasExecutionWithdrawalCredential
  hasNotInitiatedExit isActiveValidator modBalance modValidator modifyState passedShardCommitteePeriod
  queueExcessActiveBalance reserveChurn switchToCompoundingValidator
  isValidSwitchToCompoundingRequest processConsolidationRequest validatorIndexByPubkey?)
open EthCLLib.Proofs (pureState run_bind run_get run_pure run_ofExcept_ok except_bind_ok)
open SizzLean.Proofs (sszList_getElem?_eq_getElem! sszListSet!_getElem!_self sszListSet!_size
  view_uncachedBox)

/-- The validator `processConsolidationRequest` reads at registry index `s`: the body's
`let src := validators[srcN]?.getD default`, with the box view reduced to the plain list. -/
private def registryValidator [Preset] (pre : BeaconState) (s : Nat) : Validator :=
  pre.validators.toArray[s]?.getD default

/-- The pending partial-withdrawal total of registry index `s`: the body's
`getPendingBalanceToWithdraw` read, reduced to the plain list. -/
private def pendingWithdrawalOf [Preset] (pre : BeaconState) (s : Nat) : Gwei :=
  pre.pendingPartialWithdrawals.val.foldl
    (fun acc w => if w.validatorIndex == UInt64.ofNat s then acc + w.amount else acc) 0

/-- The validator `processConsolidationRequest` reads for the request pubkey `pk`: the
registry lookup composed with the body's own `validators[s]?.getD default` read. The `none`
arm is the same `default` fallthrough the body's read has. -/
private def validatorByPubkey [Preset] (pre : BeaconState) (pk : BLSPubkey) : Validator :=
  match pre.validators.val.findIdx? (·.pubkey == pk) with
  | some s => pre.validators.toArray[s]?.getD default
  | none => default

/-- The pending partial-withdrawal total of the validator carrying `pk`: the registry lookup
composed with the body's `getPendingBalanceToWithdraw` read. The `none` arm returns `0`, the
fold's unit. -/
private def pendingWithdrawalOfPubkey [Preset] (pre : BeaconState) (pk : BLSPubkey) : Gwei :=
  match pre.validators.val.findIdx? (·.pubkey == pk) with
  | some s => pendingWithdrawalOf pre s
  | none => 0

/-- The bridge between the forkdef's box read and the plain list scan the gate hypotheses
state. `validatorIndexByPubkey?` reads through the boxed state; on the uncached box the read
is the plain `findIdx?` over `pre.validators.val`. -/
theorem validatorIndexByPubkey?_pureState [Preset] [HasherTag] (pre : BeaconState)
    (pk : BLSPubkey) :
    validatorIndexByPubkey? (pureState pre) pk = pre.validators.val.findIdx? (·.pubkey == pk) := by
  rfl

/-- The composed pubkey read at a found pubkey is the index read. -/
private theorem validatorByPubkey_eq_registryValidator [Preset]
    (pre : BeaconState) (pk : BLSPubkey) (s : Nat)
    (hfind : pre.validators.val.findIdx? (·.pubkey == pk) = some s) :
    validatorByPubkey pre pk = registryValidator pre s := by
  rw [validatorByPubkey, hfind]
  rfl

/-- The composed pubkey read of the pending total at a found pubkey is the index read. -/
private theorem pendingWithdrawalOfPubkey_eq [Preset]
    (pre : BeaconState) (pk : BLSPubkey) (s : Nat)
    (hfind : pre.validators.val.findIdx? (·.pubkey == pk) = some s) :
    pendingWithdrawalOfPubkey pre pk = pendingWithdrawalOf pre s := by
  rw [pendingWithdrawalOfPubkey, hfind]

/-- A `!`-negated gate condition fires when the tested predicate is `false`. -/
private theorem negCond_true {x : Bool} (h : x = false) : ((!x) = true) := by
  rw [Bool.not_eq_true']
  exact h

/-- A `!`-negated gate condition passes when the tested predicate is `true`. -/
private theorem negCond_not {x : Bool} (h : x = true) : ¬((!x) = true) := by
  rw [Bool.not_eq_true']
  rw [h]
  decide

/-- **The validity ladder, reduced.** Under the request-level gates (distinct pubkeys, queue
room, churn above `minActivationBalance`) and both pubkeys found at `s` and `t`, the run
reduces to the validator ladder over the plain reads: `registryValidator` for both
validators, `computeEpochAtSlot pre.slot` for the body's `currentEpochOf`, and
`pendingWithdrawalOf` for the pending-withdrawal total. Each gate theorem below rewrites
with this lemma and then fires its own gate. The last `else` is the success path, which no
gate theorem reaches. The gate hypotheses spell the total through `pendingWithdrawalOf`
rather than `getPendingBalanceToWithdraw`, so the two reads are definitionally equal here
and the spec accessor earns no proof-coverage row of its own. -/
private theorem processConsolidationRequest_run_validityLadder [Preset] [HasherTag] [Config]
    (pre : BeaconState) (req : ConsolidationRequest) (s t : Nat)
    (hne : req.sourcePubkey ≠ req.targetPubkey)
    (hroom : pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit)
    (hchurn : getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance)
    (hs : pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) = some s)
    (ht : pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) = some t) :
    (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
      = (if !(hasExecutionWithdrawalCredential (registryValidator pre s) &&
            vecSliceEq (registryValidator pre s).withdrawalCredentials 12 req.sourceAddress 0 20) then
          pure ()
        else if !(hasCompoundingWithdrawalCredential (registryValidator pre t)) then pure ()
        else if !(isActiveValidator (registryValidator pre s) (computeEpochAtSlot pre.slot)) then pure ()
        else if !(isActiveValidator (registryValidator pre t) (computeEpochAtSlot pre.slot)) then pure ()
        else if !(hasNotInitiatedExit (registryValidator pre s)) then pure ()
        else if !(hasNotInitiatedExit (registryValidator pre t)) then pure ()
        else if !(passedShardCommitteePeriod (registryValidator pre s) (computeEpochAtSlot pre.slot)) then
          pure ()
        else if pendingWithdrawalOf pre s > 0 then pure ()
        else
          (do
            let exitEpoch ← computeConsolidationEpochAndUpdateChurn (StateTransition := FuluRun)
              (registryValidator pre s).effectiveBalance
            modifyState fun state =>
              modValidator state (UInt64.ofNat s) fun validator =>
                { validator with
                  exitEpoch := exitEpoch,
                  withdrawableEpoch := exitEpoch + EthCLSpecs.Fulu.Const.minValidatorWithdrawabilityDelay }
            modifyState fun state =>
              sszModify state pendingConsolidations as l => l.push
                { sourceIndex := UInt64.ofNat s, targetIndex := UInt64.ofNat t })).run (pureState pre) := by
  unfold processConsolidationRequest
  -- `run_bind` splits the do-block. `run_get` pairs the threaded box with itself, and beta
  -- plus `except_bind_ok` substitute `pureState pre` for the `state` binder.
  simp only [run_bind, run_get, except_bind_ok]
  -- The switch path. Its first check is the pubkey inequality, so `hne` makes the whole
  -- predicate answer `false`, and the run takes the else branch.
  have hswitch : ¬(isValidSwitchToCompoundingRequest (pureState pre) req = true) := by
    unfold isValidSwitchToCompoundingRequest
    simp [hne]
  rw [if_neg hswitch]
  -- G1: same pubkeys. `false` under `hne`.
  have hsame : ¬((req.sourcePubkey == req.targetPubkey) = true) := by
    simp [hne]
  rw [if_neg hsame]
  -- G2: queue below its cap. `false` under `hroom`.
  have hqueue : ¬((sszGet (pureState pre) pendingConsolidations).size
      == EthCLSpecs.Fulu.Const.pendingConsolidationsLimit) = true := by
    simp only [view_uncachedBox, beq_iff_eq]
    omega
  rw [if_neg hqueue]
  -- G3: churn above `minActivationBalance`, so the churn gate passes. `omega` cannot see
  -- through the `Gwei` abbrev, so the comparison rides its `toNat` form.
  have hchurnle : ¬(getConsolidationChurnLimit (pureState pre)
      ≤ EthCLSpecs.Fulu.Const.minActivationBalance) := by
    have hlt : EthCLSpecs.Fulu.Const.minActivationBalance
        < getConsolidationChurnLimit (pureState pre) := hchurn
    rw [UInt64.lt_iff_toNat_lt] at hlt
    rw [UInt64.le_iff_toNat_le]
    omega
  rw [if_neg hchurnle]
  -- Both lookups found: rewrite through the bridge, substitute `some s` / `some t`, and the
  -- match enters its two-index arm. The remaining equation holds by the lets' zeta and the
  -- match's iota reduction against the plain-read spellings above.
  simp only [validatorIndexByPubkey?_pureState]
  rw [hs, ht]
  rfl

/-! ## The manual witnesses

Ten of the gate theorems and the two success-arm theorems below carry
`theorem_vectors_manual` registrations
(`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), and this block holds the one state
and the base request most registrations name; the switch arm's registration
spells its same-pubkey request inline. Each patch is a named
argument to `consolidationState`, because the patched field sits inside an
`SSZList` a record update cannot reach. The def sits once, before the first
theorem that uses it, and every vector length comes from the preset constants,
so G1's line runs the same state at both presets. -/

/-- The pubkey of the consolidation witness validator at `index`: the index
byte, replicated across all 48 bytes. The five witness pubkeys (indexes 0-4)
and the unknown index 9 are pairwise distinct, which is all the registry
lookups and the pubkey gates read. No signature check runs on these bytes;
the gates compare them byte by byte. -/
private def basePubkey (index : Nat) : BLSPubkey :=
  Vector.ofFn (fun _ : Fin 48 => UInt8.ofNat index)

/-- The withdrawal credentials of a consolidation witness validator: the
prefix byte at position 0, zeros elsewhere, so the tail matches the zero
execution address the witness requests carry. -/
private def baseCredentials (tag : UInt8) : Bytes32 :=
  Vector.ofFn (fun i : Fin 32 => if i.val == 0 then tag else 0)

/-- A consolidation witness validator: active from epoch 0 with no exit
initiated, at the given credential prefix and effective balance. The exit
and activation knobs carry the per-gate patches. -/
private def consolidationValidator [Preset] (tag : UInt8) (index : Nat)
    (activation : Epoch := 0) (exit : Epoch := EthCLSpecs.Fulu.Const.farFutureEpoch)
    (balance : Gwei := 32000000000) : Validator :=
  { pubkey := basePubkey index
    withdrawalCredentials := baseCredentials tag
    effectiveBalance := balance
    slashed := false
    activationEligibilityEpoch := activation
    activationEpoch := activation
    exitEpoch := exit
    withdrawableEpoch := EthCLSpecs.Fulu.Const.farFutureEpoch }

/-- The consolidation base state. Five active validators: three compounding
validators at 2048 ETH (indexes 0-2), the consolidation source at index 3
with eth1 credentials, and the consolidation target at index 4 with
compounding credentials. The total active balance of 6208 ETH puts the
consolidation churn limit at 66 ETH at minimal, above `minActivationBalance`,
so the churn gate passes. The slot sits at epoch 65, past the minimal
`shardCommitteePeriod` of 64, so the shard-period gate passes. The queues
start empty; the knobs patch one field per theorem. -/
private def consolidationState [Preset]
    (srcTag : UInt8 := EthCLSpecs.Fulu.Const.eth1AddressWithdrawalPrefix)
    (tgtTag : UInt8 := EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix)
    (srcActivation : Epoch := 0) (tgtActivation : Epoch := 0)
    (srcExit : Epoch := EthCLSpecs.Fulu.Const.farFutureEpoch)
    (tgtExit : Epoch := EthCLSpecs.Fulu.Const.farFutureEpoch)
    (srcPending : Gwei := 0) (queue : Nat := 0)
    (srcBalance : Gwei := 32000000000) : BeaconState :=
  let vs : SSZList Validator EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    ((default : SSZList Validator EthCLSpecs.Fulu.Const.validatorRegistryLimit)
      |>.push (consolidationValidator EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix 0
        (balance := 2048000000000))
      |>.push (consolidationValidator EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix 1
        (balance := 2048000000000))
      |>.push (consolidationValidator EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix 2
        (balance := 2048000000000))
      |>.push (consolidationValidator srcTag 3 srcActivation srcExit)
      |>.push (consolidationValidator tgtTag 4 tgtActivation tgtExit))
  let bs : SSZList Gwei EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    ((default : SSZList Gwei EthCLSpecs.Fulu.Const.validatorRegistryLimit)
      |>.push 2048000000000 |>.push 2048000000000 |>.push 2048000000000
      |>.push srcBalance |>.push 32000000000)
  -- the per-validator lists the epoch step indexes by validator index:
  -- one zero entry per validator, the way the fork's genesis builder fills them
  let flags : SSZList ParticipationFlags EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    (Array.range 5).foldl (fun xs _ => xs.push 0) default
  let scores : SSZList UInt64 EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    (Array.range 5).foldl (fun xs _ => xs.push 0) default
  let partials :
      SSZList PendingPartialWithdrawal EthCLSpecs.Fulu.Const.pendingPartialWithdrawalsLimit :=
    if srcPending == 0 then default
    else
      ((default : SSZList PendingPartialWithdrawal
          EthCLSpecs.Fulu.Const.pendingPartialWithdrawalsLimit).push
        { validatorIndex := 3, amount := srcPending
          withdrawableEpoch := EthCLSpecs.Fulu.Const.farFutureEpoch })
  let consolidations :
      SSZList PendingConsolidation EthCLSpecs.Fulu.Const.pendingConsolidationsLimit :=
    (Array.range queue).foldl (fun xs _ => xs.push default) default
  { (default : BeaconState) with
    slot := UInt64.ofNat (65 * EthCLSpecs.Fulu.Const.slotsPerEpoch)
    validators := vs
    balances := bs
    previousEpochParticipation := flags
    currentEpochParticipation := flags
    inactivityScores := scores
    pendingPartialWithdrawals := partials
    pendingConsolidations := consolidations }

/-- The consolidation request the base state answers: the source and target
validators at indexes 3 and 4, and the zero execution address their
credentials carry. Every container carries the `Preset` binder, preset-free
fields included (`FRAMEWORK_ARCHITECTURE.md` §5). -/
private def baseRequest [Preset] : ConsolidationRequest :=
  { sourceAddress := default
    sourcePubkey := basePubkey 3
    targetPubkey := basePubkey 4 }

/-- **Same pubkeys.** Equal source and target pubkeys take this gate's arm, so the run
returns with the state unchanged. The switch-invalid hypothesis excludes the one way a
same-pubkey request would change the state. The six `switch_to_compounding` tests reach this
gate because the switch's pubkey-inequality check evaluates `false` first and the switch
ladder then rejects each case.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_same_source_target`,
`test_incorrect_source_pubkey_is_target_pubkey`,
`test_switch_to_compounding_exited_source`,
`test_switch_to_compounding_inactive_source`,
`test_switch_to_compounding_not_authorized`,
`test_switch_to_compounding_source_bls_withdrawal_credential`,
`test_switch_to_compounding_source_compounding_withdrawal_credential`,
`test_switch_to_compounding_unknown_source_pubkey`. -/
theorem processConsolidationRequest_run_same_pubkeys [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey = req.targetPubkey →
      isValidSwitchToCompoundingRequest (pureState pre) req = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req heq hswitch
  unfold processConsolidationRequest
  simp only [run_bind, run_get, except_bind_ok]
  have hswitch' : ¬(isValidSwitchToCompoundingRequest (pureState pre) req = true) := by
    simp [hswitch]
  rw [if_neg hswitch']
  -- G1: the equality makes the gate condition `true`, and the arm is `pure ()`.
  have hsame : (req.sourcePubkey == req.targetPubkey) = true := by
    simp [heq]
  rw [if_pos hsame]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_same_source_target`: the request reuses the target's pubkey,
-- and the target's compounding credentials fail the switch's eth1 check.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_same_pubkeys
  pre := consolidationState
  req := { sourceAddress := default, sourcePubkey := basePubkey 4,
           targetPubkey := basePubkey 4 }

/-- **Queue full.** The pending-consolidations queue at its cap fails the queue gate. The run
returns with the state unchanged, because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_exceed_pending_consolidations_limit`. -/
theorem processConsolidationRequest_run_queue_full [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size = EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hfull
  unfold processConsolidationRequest
  simp only [run_bind, run_get, except_bind_ok]
  have hswitch : ¬(isValidSwitchToCompoundingRequest (pureState pre) req = true) := by
    unfold isValidSwitchToCompoundingRequest
    simp [hne]
  rw [if_neg hswitch]
  have hsame : ¬((req.sourcePubkey == req.targetPubkey) = true) := by
    simp [hne]
  rw [if_neg hsame]
  -- G2: the queue is at its cap, so the gate fires and its arm is `pure ()`.
  have hqueue : ((sszGet (pureState pre) pendingConsolidations).size
      == EthCLSpecs.Fulu.Const.pendingConsolidationsLimit) = true := by
    simp only [view_uncachedBox, beq_iff_eq]
    exact hfull
  rw [if_pos hqueue]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_exceed_pending_consolidations_limit`.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_queue_full
  pre := consolidationState (queue := EthCLSpecs.Fulu.Const.pendingConsolidationsLimit)
  req := baseRequest

/-- **Consolidation churn too low.** With distinct source and target pubkeys and room in the
pending-consolidations queue, a consolidation churn limit at or below `minActivationBalance`
fails the churn gate. The run stops there and returns with the state unchanged, because the
gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_not_enough_consolidation_churn_available`. -/
theorem processConsolidationRequest_run_churn_too_low [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) ≤ EthCLSpecs.Fulu.Const.minActivationBalance →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn
  unfold processConsolidationRequest
  -- `run_bind` splits the do-block. `run_get` pairs the threaded box with itself, and beta
  -- plus `except_bind_ok` substitute `pureState pre` for the `state` binder.
  simp only [run_bind, run_get, except_bind_ok]
  -- The switch path. Its first check is the pubkey inequality, so `hne` makes the whole
  -- predicate answer `false`, and the run takes the else branch.
  have hswitch : ¬(isValidSwitchToCompoundingRequest (pureState pre) req = true) := by
    unfold isValidSwitchToCompoundingRequest
    simp [hne]
  rw [if_neg hswitch]
  -- G1: same pubkeys. `false` under `hne`.
  have hsame : ¬((req.sourcePubkey == req.targetPubkey) = true) := by
    simp [hne]
  rw [if_neg hsame]
  -- G2: queue at its cap. `false` under `hroom`.
  have hqueue : ¬((sszGet (pureState pre) pendingConsolidations).size
      == EthCLSpecs.Fulu.Const.pendingConsolidationsLimit) = true := by
    simp only [view_uncachedBox, beq_iff_eq]
    omega
  rw [if_neg hqueue]
  -- G3, the churn gate. The hypothesis fires it, and its body is `pure ()`: the run returns
  -- with the state unchanged.
  rw [if_pos hchurn]
  rfl

/-- **Unknown pubkey.** With room in the queue and churn above `minActivationBalance`, an
unknown source or target pubkey drops the two registry lookups into the match's fall-through
arm. The run returns with the state unchanged.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_unknown_source_pubkey`,
`test_incorrect_unknown_target_pubkey`. -/
theorem processConsolidationRequest_run_unknown_pubkey [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      (pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) = none ∨
        pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) = none) →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hunk
  unfold processConsolidationRequest
  simp only [run_bind, run_get, except_bind_ok]
  have hswitch : ¬(isValidSwitchToCompoundingRequest (pureState pre) req = true) := by
    unfold isValidSwitchToCompoundingRequest
    simp [hne]
  rw [if_neg hswitch]
  have hsame : ¬((req.sourcePubkey == req.targetPubkey) = true) := by
    simp [hne]
  rw [if_neg hsame]
  have hqueue : ¬((sszGet (pureState pre) pendingConsolidations).size
      == EthCLSpecs.Fulu.Const.pendingConsolidationsLimit) = true := by
    simp only [view_uncachedBox, beq_iff_eq]
    omega
  rw [if_neg hqueue]
  have hchurnle : ¬(getConsolidationChurnLimit (pureState pre)
      ≤ EthCLSpecs.Fulu.Const.minActivationBalance) := by
    have hlt : EthCLSpecs.Fulu.Const.minActivationBalance
        < getConsolidationChurnLimit (pureState pre) := hchurn
    rw [UInt64.lt_iff_toNat_lt] at hlt
    rw [UInt64.le_iff_toNat_le]
    omega
  rw [if_neg hchurnle]
  -- Rewrite both lookups through the bridge, then let each disjunct put `none` into its
  -- scrutinee: the match falls through to `pure ()`.
  simp only [validatorIndexByPubkey?_pureState]
  cases hunk with
  | inl h => rw [h]; rfl
  | inr h =>
    rw [h]
    -- The first scrutinee is still a lookup; either concrete value drops the match into
    -- its fall-through arm.
    cases hs' : pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) <;> rfl

/-- **Source not authorized.** With both pubkeys in the registry, a source without an
execution withdrawal credential, or with a withdrawal address that misses
`req.sourceAddress`, fails the authorization gate. The run returns with the state unchanged,
because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_source_with_bls_credential`,
`test_incorrect_no_source_execution_withdrawal_credential`,
`test_incorrect_source_address`. -/
theorem processConsolidationRequest_run_source_not_authorized [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hgate
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  -- G5: the conjunction is `false`, so the `!`-negated condition is `true` and the gate fires.
  rw [if_pos (negCond_true hgate)]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_source_with_bls_credential`: the source carries the BLS
-- prefix, so its credential fails the execution-credential check.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_source_not_authorized
  pre := consolidationState (srcTag := EthCLSpecs.Fulu.Const.blsWithdrawalPrefix)
  req := baseRequest

/-- **Target not compounding.** With both pubkeys in the registry and the source authorized,
a target whose withdrawal credential prefix is not compounding fails the target-credential
gate. The run returns with the state unchanged, because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_target_with_bls_credential`,
`test_incorrect_target_with_eth1_credential`. -/
theorem processConsolidationRequest_run_target_not_compounding [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hauth hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hgate
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  -- G5 passes: the conjunction is `true`.
  rw [if_neg (negCond_not hauth)]
  -- G6: the target's prefix is not compounding, so the gate fires.
  rw [if_pos (negCond_true hgate)]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_target_with_eth1_credential`: the target carries the eth1
-- prefix, so its credential fails the compounding check.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_target_not_compounding
  pre := consolidationState (tgtTag := EthCLSpecs.Fulu.Const.eth1AddressWithdrawalPrefix)
  req := baseRequest

/-- **Source inactive.** With both pubkeys in the registry and the target compounding, a
source inactive in the current epoch fails the activity gate. The run returns with the state
unchanged, because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_inactive_source`. -/
theorem processConsolidationRequest_run_source_inactive [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = true →
      (isActiveValidator (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hauth hcomp hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth hgate
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hcomp
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  rw [if_neg (negCond_not hauth)]
  rw [if_neg (negCond_not hcomp)]
  -- G7: the source is inactive in `computeEpochAtSlot pre.slot`, so the gate fires.
  rw [if_pos (negCond_true hgate)]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_inactive_source`.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_source_inactive
  pre := consolidationState (srcActivation := EthCLSpecs.Fulu.Const.farFutureEpoch)
  req := baseRequest

/-- **Target inactive.** With both pubkeys in the registry and the source active, a target
inactive in the current epoch fails the activity gate. The run returns with the state
unchanged, because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_inactive_target`. -/
theorem processConsolidationRequest_run_target_inactive [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = true →
      (isActiveValidator (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (isActiveValidator (validatorByPubkey pre req.targetPubkey)
        (computeEpochAtSlot pre.slot)) = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hauth hcomp hsrcact hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth hsrcact
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hcomp hgate
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  rw [if_neg (negCond_not hauth)]
  rw [if_neg (negCond_not hcomp)]
  rw [if_neg (negCond_not hsrcact)]
  -- G8: the target is inactive in `computeEpochAtSlot pre.slot`, so the gate fires.
  rw [if_pos (negCond_true hgate)]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_inactive_target`.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_target_inactive
  pre := consolidationState (tgtActivation := EthCLSpecs.Fulu.Const.farFutureEpoch)
  req := baseRequest

/-- **Source exited.** With both pubkeys in the registry and both validators active, a source
that has initiated its exit fails the exit gate. The run returns with the state unchanged,
because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_exited_source`. -/
theorem processConsolidationRequest_run_source_exited [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = true →
      (isActiveValidator (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (isActiveValidator (validatorByPubkey pre req.targetPubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.sourcePubkey)) = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hauth hcomp hsrcact htgtact hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth hsrcact hgate
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hcomp htgtact
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  rw [if_neg (negCond_not hauth)]
  rw [if_neg (negCond_not hcomp)]
  rw [if_neg (negCond_not hsrcact)]
  rw [if_neg (negCond_not htgtact)]
  -- G9: the source has initiated its exit, so the gate fires.
  rw [if_pos (negCond_true hgate)]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_exited_source`: the patch sets exit epoch 66, one past the
-- state's epoch 65, so the source stays active but its exit has begun.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_source_exited
  pre := consolidationState (srcExit := 66)
  req := baseRequest

/-- **Target exited.** With both pubkeys in the registry and the source's exit uninitiated, a
target that has initiated its exit fails the exit gate. The run returns with the state
unchanged, because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_exited_target`. -/
theorem processConsolidationRequest_run_target_exited [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = true →
      (isActiveValidator (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (isActiveValidator (validatorByPubkey pre req.targetPubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.sourcePubkey)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.targetPubkey)) = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hauth hcomp hsrcact htgtact hsrcexit hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth hsrcact hsrcexit
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hcomp htgtact hgate
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  rw [if_neg (negCond_not hauth)]
  rw [if_neg (negCond_not hcomp)]
  rw [if_neg (negCond_not hsrcact)]
  rw [if_neg (negCond_not htgtact)]
  rw [if_neg (negCond_not hsrcexit)]
  -- G10: the target has initiated its exit, so the gate fires.
  rw [if_pos (negCond_true hgate)]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_exited_target`: the patch sets exit epoch 66, one past the
-- state's epoch 65, so the target stays active but its exit has begun.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_target_exited
  pre := consolidationState (tgtExit := 66)
  req := baseRequest

/-- **Shard period not passed.** With both pubkeys in the registry and neither validator
exiting, a source short of `shardCommitteePeriod` epochs of activity fails the tenure gate.
The run returns with the state unchanged, because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_source_not_active_long_enough`. -/
theorem processConsolidationRequest_run_shard_period_not_passed [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = true →
      (isActiveValidator (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (isActiveValidator (validatorByPubkey pre req.targetPubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.sourcePubkey)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.targetPubkey)) = true →
      (passedShardCommitteePeriod (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = false →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hauth hcomp hsrcact htgtact hsrcexit htgtexit
    hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth hsrcact hsrcexit hgate
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hcomp htgtact htgtexit
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  rw [if_neg (negCond_not hauth)]
  rw [if_neg (negCond_not hcomp)]
  rw [if_neg (negCond_not hsrcact)]
  rw [if_neg (negCond_not htgtact)]
  rw [if_neg (negCond_not hsrcexit)]
  rw [if_neg (negCond_not htgtexit)]
  -- G11: the source is short of the shard-committee period, so the gate fires.
  rw [if_pos (negCond_true hgate)]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_source_not_active_long_enough`: the patch sets activation
-- epoch 2, so `2 + shardCommitteePeriod` (64 at minimal) passes epoch 65.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_shard_period_not_passed
  pre := consolidationState (srcActivation := 2)
  req := baseRequest

/-- **Source pending withdrawal.** With both pubkeys in the registry and the source past its
shard-committee period, a nonzero pending partial-withdrawal total fails the last gate. The
run returns with the state unchanged, because the gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_source_has_pending_withdrawal`. -/
theorem processConsolidationRequest_run_source_pending_withdrawal [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = true →
      (isActiveValidator (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (isActiveValidator (validatorByPubkey pre req.targetPubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.sourcePubkey)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.targetPubkey)) = true →
      (passedShardCommitteePeriod (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      pendingWithdrawalOfPubkey pre req.sourcePubkey > 0 →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn hfindS hfindT hauth hcomp hsrcact htgtact hsrcexit htgtexit
    hshard hgate
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth hsrcact hsrcexit hshard
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hcomp htgtact htgtexit
  rw [pendingWithdrawalOfPubkey_eq pre req.sourcePubkey s hs] at hgate
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  rw [if_neg (negCond_not hauth)]
  rw [if_neg (negCond_not hcomp)]
  rw [if_neg (negCond_not hsrcact)]
  rw [if_neg (negCond_not htgtact)]
  rw [if_neg (negCond_not hsrcexit)]
  rw [if_neg (negCond_not htgtexit)]
  rw [if_neg (negCond_not hshard)]
  -- G12: the pending total is nonzero, so the gate fires.
  rw [if_pos hgate]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_incorrect_source_has_pending_withdrawal`: the patch queues one
-- 1-ETH partial withdrawal at the source index.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_source_pending_withdrawal
  pre := consolidationState (srcPending := 1000000000)
  req := baseRequest

/-! ## The two success arms

The catalog's last two branches mutate the state. The switch arm rewrites the
source's credential prefix and queues the balance above `minActivationBalance`;
the success arm reserves churn and appends the pending consolidation. Each
theorem states the post-state in closed form over a helper, and each carries a
registry size bound: the writes index the registry through a `UInt64`, so the
`uint64` truncation has to read back as the found index. The switch arm also
reads the balance list at the found index, so its theorem adds the two lists'
equal length: on a broken pair the balance read rejects with `outOfBounds`,
the reject `Operations.lean`'s own comment names for the withdrawal path. -/

/-- The total read at an in-range index equals the composed read the helpers
state: the element, taken out of the `some` the checked read wraps. -/
private theorem sszList_getElem!_eq_getD {α : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (i : Nat) (h : i < xs.size) :
    xs[i]! = xs.toArray[i]?.getD default := by
  rw [getElem!_pos (dom := fun (xs : SSZList α cap) j => j < xs.size) (h := h)]
  rw [Array.getElem?_eq_getElem h]
  rfl

/-- A monadic read at an in-range index lifts to the element, with the threaded
box handed on unchanged. The read-level fact the two success arms rewrite
through at each of their reads. -/
private theorem run_sszGetIdx_of_range {α : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (j : Nat) (h : j < xs.size)
    {σ ε : Type} [ErrorConv IndexError ε] (sb : σ) :
    (sszGetIdx (E := ε) (m := StateT σ (Except ε)) xs j).run sb = .ok (xs[j]!, sb) := by
  show (MonadExcept.ofExcept (ε := ε) (m := StateT σ (Except ε))
    (Except.mapError ErrorConv.conv
      (match xs.val[j]? with
      | some a => Except.ok a
      | none => .error (SizzLean.Cache.IndexError.indexError j xs.val.size)))).run sb = _
  rw [sszList_getElem?_eq_getElem! xs j h]
  exact run_ofExcept_ok sb

/-- Reading back the element a `set!` wrote, in range: the read lifts to the
written value. The credential write's own read-back, which the switch arm's
pending deposit reads. -/
private theorem run_sszGetIdx_of_set!_self {α : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (j : Nat) (v : α) (h : j < xs.size)
    {σ ε : Type} [ErrorConv IndexError ε] (sb : σ) :
    (sszGetIdx (E := ε) (m := StateT σ (Except ε)) (xs.set! j v) j).run sb = .ok (v, sb) := by
  rw [run_sszGetIdx_of_range (xs.set! j v) j (by rw [sszListSet!_size]; exact h) sb,
    sszListSet!_getElem!_self xs j v h]

/-- The run of one `modifyState` write: the written box handed on, no value.
The write-level fact the two success arms rewrite through at each of their
writes, so the next read meets the written state. The statement is about the
box machinery itself (`SPECS_ARCHITECTURE.md` §11.1's first `box_generic`
kind): `modifyState` hands the written box on, for whatever box the run
threads. -/
@[box_generic "modifyState's run hands the written box on; the lemma is about \
the box step itself, and every run-level write rewrite in this file reads it"]
private theorem run_modifyState [Preset] [HasherTag] {ε : Type}
    (f : EthCLSpecs.Fulu.State → EthCLSpecs.Fulu.State) (sb : EthCLSpecs.Fulu.State) :
    (modifyState f : StateT EthCLSpecs.Fulu.State (Except ε) PUnit).run sb
      = .ok ((), f sb) := rfl

/-- A conditional action's run splits into the conditional runs of its arms.
The success arms state their balance conditions at the value level, so the
run-level conditionals rewrite through this before the branches reduce. -/
private theorem run_ite {σ ε α : Type} (c : Prop) [Decidable c]
    (x y : StateT σ (Except ε) α) (sb : σ) :
    (if c then x else y).run sb = if c then x.run sb else y.run sb := by
  by_cases h : c <;> simp [h]

/-- A conditional pair of answers is the answer of the conditional value. The
run-level conditional's arms both answer `.ok`, so the split condition moves
inside, where the helper states it. -/
private theorem except_ok_ite {ε α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then Except.ok x else Except.ok y : Except ε α)
      = Except.ok (if c then x else y) := by
  by_cases h : c <;> simp [h]

/-- The pair's second component carries the split condition, so the pair
constructor moves inside the conditional, where the helper states it. -/
private theorem prod_ite {α β : Type} (c : Prop) [Decidable c] (a : α) (x y : β) :
    (if c then (a, x) else (a, y)) = (a, if c then x else y) := by
  by_cases h : c <;> simp [h]

/-- `modValidator`'s write at the pure box lands as one plain record update.
The mirror of `modBalance_pureState` (`Proofs/Fulu/Balances.lean`), stated
here because the switch arm's reads meet the validator write and the run
has to reduce through it. This one stays private and untagged: the theorem
is setup for the proofs above, and `modValidator` remains merely touched. -/
private theorem modValidator_pureState [Preset] [HasherTag] :
    ∀ (state : BeaconState) (i : ValidatorIndex) (f : Validator → Validator),
      modValidator (pureState state) i f =
        pureState
          { state with validators := state.validators.set! i.toNat (f state.validators[i.toNat]!) } :=
  fun _ _ _ => rfl

/-- The balance of registry index `i`: the body's `queueExcessActiveBalance`
read, reduced to the plain list. -/
private def registryBalance [Preset] (pre : BeaconState) (i : Nat) : Gwei :=
  pre.balances.toArray[i]?.getD default

/-- The switch arm's post-state at the found index `i`: the source's
withdrawal credential prefix becomes `compoundingWithdrawalPrefix`, and a
balance above `minActivationBalance` moves the excess into a pending deposit
while the balance drops to the minimum. The helper `switchedState`'s found
arm, stated once so the ladder below names it. -/
private def switchedArm [Preset] (pre : BeaconState) (i : Nat) : BeaconState :=
  let creds := (registryValidator pre i).withdrawalCredentials.set 0
    EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix
  let srcVal : Validator := { registryValidator pre i with withdrawalCredentials := creds }
  let b := registryBalance pre i
  if b > EthCLSpecs.Fulu.Const.minActivationBalance then
    { pre with
      validators := pre.validators.set! i srcVal
      balances := pre.balances.set! i EthCLSpecs.Fulu.Const.minActivationBalance
      pendingDeposits := pre.pendingDeposits.push
        { pubkey := srcVal.pubkey, withdrawalCredentials := creds,
          amount := b - EthCLSpecs.Fulu.Const.minActivationBalance,
          signature := EthCLSpecs.Fulu.Const.g2PointAtInfinity,
          slot := EthCLSpecs.Fulu.Const.genesisSlot } }
  else
    { pre with validators := pre.validators.set! i srcVal }

/-- The exact closed-form post-state of the switch arm. The `none` arm is
unreachable under the switch hypothesis (the lookup is found there); the arm
exists so the helper is total. -/
private def switchedState [Preset] (pre : BeaconState) (pk : BLSPubkey) : BeaconState :=
  match pre.validators.val.findIdx? (·.pubkey == pk) with
  | none => pre
  | some i => switchedArm pre i

/-- The switch arm's whole run at the box, over the found index `j`. The range
and parity hypotheses carry the three registry reads' bounds, and the size
bound the `uint64` truncation's read-back, so the proof reduces to the helper's
record updates. -/
private theorem switchArm_run_eq [Preset] [HasherTag] (pre : BeaconState) (j : Nat)
    (hj : j < pre.validators.size) (hpar : pre.balances.size = pre.validators.size)
    (hsize : j < 2 ^ 64) :
    (do
        let state ← get
        let validator ← sszGetIdx (sszGet state validators) (UInt64.ofNat j).toNat
        let newWc : Bytes32 := validator.withdrawalCredentials.set 0
          EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix
        modifyState fun state => modValidator state (UInt64.ofNat j) fun validator =>
          { validator with withdrawalCredentials := newWc }
        queueExcessActiveBalance (UInt64.ofNat j) : FuluRun PUnit).run (pureState pre)
      = .ok ((), pureState (switchedArm pre j)) := by
  have hj' : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' hsize
  have hv' : j < pre.validators.size := hj
  have hb' : j < pre.balances.size := by rw [hpar]; exact hj
  -- Each read lifts to its element at the in-range index, each write hands its
  -- state on, and the conditionals split so both sides compare at the value
  -- level.
  simp only [hj', view_uncachedBox,
    run_bind, run_get, run_pure, except_bind_ok, run_ite, except_ok_ite, prod_ite,
    queueExcessActiveBalance,
    run_sszGetIdx_of_range pre.validators _ hv',
    run_sszGetIdx_of_range pre.balances _ hb',
    run_sszGetIdx_of_set!_self pre.validators _ _ hv',
    modValidator_pureState, modBalance_pureState, run_modifyState]
  -- Both sides now carry the balance conditional at the value level, the run's
  -- on the total read and the helper's on the composed read. The two conditions
  -- are the same read, so one split discharges both branches.
  by_cases hbal : pre.balances[j]! > EthCLSpecs.Fulu.Const.minActivationBalance
  · have hbal' : registryBalance pre j > EthCLSpecs.Fulu.Const.minActivationBalance := hbal
    simp only [if_pos hbal, switchedArm, if_pos hbal']
    rfl
  · have hbal' : ¬(registryBalance pre j > EthCLSpecs.Fulu.Const.minActivationBalance) := hbal
    simp only [if_neg hbal, switchedArm, if_neg hbal']
    rfl

/-- **Switch to compounding.** A request whose source and target pubkeys are equal and
that passes `isValidSwitchToCompoundingRequest` takes the switch arm. The conclusion
states the post-state in closed form: the source's withdrawal credential prefix becomes
`compoundingWithdrawalPrefix`, and a balance above `minActivationBalance` moves the
excess into a pending deposit while the balance drops to the minimum. One theorem
states both balance cases, because upstream's three switch tests exercise each. The
equal-pubkey hypothesis names the arm the statement covers; the switch hypothesis
already implies it, and the statement keeps it so the hypothesis list reads in the
body's gate order. The two registry hypotheses carry the facts the arm's reads and
writes need: the run indexes the balance list at the found registry index, so the two
lists match, and the write's `uint64`-truncated index reads back as the index, so the
registry stays inside the `uint64` range.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_basic_switch_to_compounding`,
`test_switch_to_compounding_with_excess`,
`test_switch_to_compounding_with_pending_consolidations_at_limit`. -/
theorem processConsolidationRequest_run_switch_to_compounding [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey = req.targetPubkey →
      isValidSwitchToCompoundingRequest (pureState pre) req = true →
      pre.validators.size < 2 ^ 64 →
      pre.balances.size = pre.validators.size →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState (switchedState pre req.sourcePubkey)) := by
  intro pre req _heq hswitch hsize hpar
  unfold processConsolidationRequest
  -- `run_bind` splits the do-block. `run_get` pairs the threaded box with itself, and beta
  -- plus `except_bind_ok` substitute `pureState pre` for the `state` binder.
  simp only [run_bind, run_get, except_bind_ok]
  -- The switch gate fires on the hypothesis.
  rw [if_pos hswitch]
  -- Both lookups: rewrite through the bridge, then let each concrete value put the
  -- match into its arm.
  simp only [validatorIndexByPubkey?_pureState]
  cases hfind : pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) with
  | none =>
    simp only [switchedState, hfind]
    rfl
  | some i =>
    obtain ⟨hv, -⟩ := Array.findIdx?_eq_some_iff_findIdx_eq.mp hfind
    -- The match enters its `some` arm and the switch unfolds; the arm's run
    -- reduces through the ladder.
    dsimp only
    simp only [switchToCompoundingValidator]
    rw [switchArm_run_eq pre i hv hpar (Nat.lt_trans hv hsize)]
    simp only [switchedState, hfind]

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_switch_to_compounding_with_excess`: the patch raises the source's
-- balance by 1 ETH (`EFFECTIVE_BALANCE_INCREMENT`), so the switch queues the
-- excess and caps the balance.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_switch_to_compounding
  pre := consolidationState (srcBalance := 33000000000)
  req := { sourceAddress := default, sourcePubkey := basePubkey 3,
           targetPubkey := basePubkey 3 }

/-- The exact closed-form post-state of the success arm. The exit epoch and
the churn bookkeeping are `reserveChurn`'s output, the arithmetic core
`computeConsolidationEpochAndUpdateChurn` runs, and the churn reads spell as the
body's own (`getConsolidationChurnLimit` on the box, the epoch step on the slot),
so the helper covers every churn scenario without pinning one. The `_, _` arm is
unreachable under the found-ness hypotheses; it keeps the helper total. -/
private def consolidatedState [Preset] [HasherTag] [Config]
    (pre : BeaconState) (req : ConsolidationRequest) : BeaconState :=
  match pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey),
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) with
  | some s, some t =>
    let bal := (registryValidator pre s).effectiveBalance
    let earliest := umax pre.earliestConsolidationEpoch
      (computeActivationExitEpoch (computeEpochAtSlot pre.slot))
    let perEpoch := getConsolidationChurnLimit (pureState pre)
    let consume := if pre.earliestConsolidationEpoch < earliest then perEpoch
      else pre.consolidationBalanceToConsume
    let churn := reserveChurn bal consume perEpoch earliest
    let churned : BeaconState :=
      { pre with
        consolidationBalanceToConsume := churn.2 - bal,
        earliestConsolidationEpoch := churn.1 }
    let exitedVal : Validator :=
      { registryValidator pre s with
        exitEpoch := churn.1,
        withdrawableEpoch :=
          churn.1 + EthCLSpecs.Fulu.Const.minValidatorWithdrawabilityDelay }
    let exited : BeaconState :=
      { churned with validators := churned.validators.set! s exitedVal }
    let pushed :
        SSZList PendingConsolidation EthCLSpecs.Fulu.Const.pendingConsolidationsLimit :=
      exited.pendingConsolidations.push
        { sourceIndex := UInt64.ofNat s, targetIndex := UInt64.ofNat t }
    { exited with pendingConsolidations := pushed }
  | _, _ => pre

/-- **Consolidation success.** A request through every gate reserves churn and appends
one `PendingConsolidation`. The exit epoch comes from
`computeConsolidationEpochAndUpdateChurn`'s effect, and the right-hand side states its
arithmetic through `reserveChurn`, the core that function runs, so one statement covers
every churn scenario upstream tests: a fresh budget, churn already spent this epoch, and
a spread over several epochs. The registry size bound carries the fact the write's
`uint64`-truncated index reads back as the found source index.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_basic_consolidation_in_current_consolidation_epoch`,
`test_basic_consolidation_with_excess_target_balance`,
`test_basic_consolidation_in_new_consolidation_epoch`,
`test_basic_consolidation_with_preexisting_churn`,
`test_basic_consolidation_with_insufficient_preexisting_churn`,
`test_basic_consolidation_with_compounding_credentials`,
`test_consolidation_churn_limit_balance`,
`test_basic_consolidation_source_has_less_than_max_effective_balance`,
`test_basic_consolidation_target_has_less_than_min_activation_effective_balance`,
`test_consolidation_balance_larger_than_churn_limit`,
`test_consolidation_balance_through_two_churn_epochs`. -/
theorem processConsolidationRequest_run_consolidation_success [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) > EthCLSpecs.Fulu.Const.minActivationBalance →
      pre.validators.val.findIdx? (·.pubkey == req.sourcePubkey) ≠ none →
      pre.validators.val.findIdx? (·.pubkey == req.targetPubkey) ≠ none →
      pre.validators.size < 2 ^ 64 →
      (hasExecutionWithdrawalCredential (validatorByPubkey pre req.sourcePubkey) &&
          vecSliceEq (validatorByPubkey pre req.sourcePubkey).withdrawalCredentials 12
            req.sourceAddress 0 20) = true →
      (hasCompoundingWithdrawalCredential (validatorByPubkey pre req.targetPubkey)) = true →
      (isActiveValidator (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (isActiveValidator (validatorByPubkey pre req.targetPubkey)
        (computeEpochAtSlot pre.slot)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.sourcePubkey)) = true →
      (hasNotInitiatedExit (validatorByPubkey pre req.targetPubkey)) = true →
      (passedShardCommitteePeriod (validatorByPubkey pre req.sourcePubkey)
        (computeEpochAtSlot pre.slot)) = true →
      pendingWithdrawalOfPubkey pre req.sourcePubkey = 0 →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState (consolidatedState pre req)) := by
  intro pre req hne hroom hchurn hfindS hfindT hsize hauth hcomp hsrcact htgtact
    hsrcexit htgtexit hshard hpend
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfindS
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hfindT
  rw [validatorByPubkey_eq_registryValidator pre req.sourcePubkey s hs] at hauth hsrcact hsrcexit hshard
  rw [validatorByPubkey_eq_registryValidator pre req.targetPubkey t ht] at hcomp htgtact htgtexit
  rw [pendingWithdrawalOfPubkey_eq pre req.sourcePubkey s hs] at hpend
  rw [processConsolidationRequest_run_validityLadder pre req s t hne hroom hchurn hs ht]
  rw [if_neg (negCond_not hauth)]
  rw [if_neg (negCond_not hcomp)]
  rw [if_neg (negCond_not hsrcact)]
  rw [if_neg (negCond_not htgtact)]
  rw [if_neg (negCond_not hsrcexit)]
  rw [if_neg (negCond_not htgtexit)]
  rw [if_neg (negCond_not hshard)]
  -- The last gate: the composed pending total is zero, so it cannot exceed zero.
  have hgate : ¬(pendingWithdrawalOf pre s > 0) := by
    rw [hpend]
    decide
  rw [if_neg hgate]
  -- The write's `uint64`-truncated index reads back as the found index under the
  -- registry size bound.
  obtain ⟨hsz, -⟩ := Array.findIdx?_eq_some_iff_findIdx_eq.mp hs
  have h64 : (UInt64.ofNat s).toNat = s :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hsz hsize)
  -- Both sides: the helper's match enters the two-index arm, the churn
  -- reservation's run threads through its write, and the validator write's total
  -- read spells as the helper's composed read at the in-range source index.
  simp only [consolidatedState, hs, ht, h64, view_uncachedBox,
    computeConsolidationEpochAndUpdateChurn,
    run_bind, run_get, except_bind_ok, run_modifyState, modValidator]
  rfl

-- The manual witness for the theorem above
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), mirroring
-- `test_basic_consolidation_in_current_consolidation_epoch`: the base state
-- passes every gate unchanged, so the run takes the success arm exactly as
-- the plainest upstream basic test does.
open EthCLLib.Internal in
theorem_vectors_manual processConsolidationRequest_run_consolidation_success
  pre := consolidationState
  req := baseRequest

end EthCLSpecs.Proofs.Fulu
