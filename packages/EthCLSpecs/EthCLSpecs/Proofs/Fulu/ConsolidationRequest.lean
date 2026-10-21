import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Fulu.ConsolidationRequest`: `processConsolidationRequest`'s request gates

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

open EthCLLib.Spec (HasherTag vecSliceEq)
open EthCLSpecs.Fulu (Preset Config BLSPubkey BeaconState ConsolidationRequest Gwei Validator
  computeConsolidationEpochAndUpdateChurn computeEpochAtSlot getConsolidationChurnLimit
  hasCompoundingWithdrawalCredential hasExecutionWithdrawalCredential hasNotInitiatedExit
  isActiveValidator modValidator modifyState passedShardCommitteePeriod
  isValidSwitchToCompoundingRequest processConsolidationRequest validatorIndexByPubkey?)
open EthCLLib.Proofs (pureState run_bind run_get except_bind_ok)
open SizzLean.Proofs (view_uncachedBox)

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

end EthCLSpecs.Proofs.Fulu
