import EthCLSpecs.Proofs.Heze.DriftAttest
import EthCLSpecs.Proofs.Heze.EconFrame

/-!
# `EthCLSpecs.Proofs.Heze.DriftBlock`: the operations of a block keep the invariant

`process_operations` runs six loops. The exit loops keep `OpsInv` (`DriftOps.lean`). An
attestation keeps it at the cost `attBudget` (`DriftAttest.lean`). A BLS change writes the
withdrawal credentials of one validator from the BLS prefix to the execution prefix, so the
cap of its effective balance stays (`RunInv.sameReads`). A payload attestation writes no read
of the invariant.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok keepsUncached_bind
  keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

/-- A write of one validator that keeps every read of the invariant keeps the invariant. -/
theorem RunInv.sameReads {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat} {j : Nat} {v v' : Validator}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (w : OneWrite a b j v v')
    (heb : v'.effectiveBalance = v.effectiveBalance)
    (hmx : EthCLSpecs.Heze.getMaxEffectiveBalance v' = EthCLSpecs.Heze.getMaxEffectiveBalance v)
    (hact : v'.activationEpoch = v.activationEpoch) (hex : v'.exitEpoch = v.exitEpoch)
    (hwd : v'.withdrawableEpoch = v.withdrawableEpoch) (hsl : v'.slashed = v.slashed)
    (hq1 : b.pendingConsolidations = a.pendingConsolidations)
    (hq2 : b.pendingPartialWithdrawals = a.pendingPartialWithdrawals)
    (hd : b.depositBalanceToConsume = a.depositBalanceToConsume)
    (hx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch) :
    RunInv vals st₀ E CX CC b V W tag Γp B := by
  have emx : ∀ k, maxN b k = maxN a k := fun k =>
    w.read (fun u => (EthCLSpecs.Heze.getMaxEffectiveBalance u).toNat) 0
      (by dsimp only; rw [hmx]) k
  have eeb : ∀ k, ebN b k = ebN a k := fun k =>
    w.read (fun u => u.effectiveBalance.toNat) 0 (by dsimp only; rw [heb]) k
  have eact : ∀ k, actOf b k = actOf a k := fun k =>
    w.read (fun u => u.activationEpoch.toNat) 0 (by dsimp only; rw [hact]) k
  have eex : ∀ k, exitOf b k = exitOf a k := fun k =>
    w.read (fun u => u.exitEpoch.toNat) _ (by dsimp only; rw [hex]) k
  have ewd : ∀ k, wdrOf b k = wdrOf a k := fun k =>
    w.read (fun u => u.withdrawableEpoch.toNat) _ (by dsimp only; rw [hwd]) k
  have esl : ∀ k, slashedOf b k = slashedOf a k := fun k => by
    unfold slashedOf
    rw [w.get k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, w.old]; exact hsl
    · rw [if_neg hk]
  have ecap : ∀ k, capN b k = capN a k := fun k => by unfold capN balN; rw [w.bal, emx]
  have ephi : phi vals E b = phi vals E a := by
    have hg : gSl vals b = gSl vals a := by
      unfold gSl
      rw [w.size]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      rw [esl, emx]
    have hc : gCons E b = gCons E a := by
      unfold gCons
      rw [hq1]
      simp only [ewd]
    unfold phi gPart
    rw [hg, hc, hq2, hd]
  refine I.transfer ecap ephi eact eex ewd esl w.size (by rw [w.bal]) hx1 hx2 hc1 hc2
    (fun i hi hl => by rw [eeb]; exact I.track i hi hl)
    (fun i hi => by rw [eeb, emx]; exact I.shape.ebLe i (by rw [← w.size]; exact hi))
    (fun i hi => by rw [eeb]; exact I.shape.ebMul i (by rw [← w.size]; exact hi))

omit [HasherTag] in
/-- A validator without compounding credentials has the cap `MIN_ACTIVATION_BALANCE`. Two
such validators have one cap. -/
theorem getMax_eq_of_not_compounding {v v' : Validator}
    (h : EthCLSpecs.Heze.hasCompoundingWithdrawalCredential v = false)
    (h' : EthCLSpecs.Heze.hasCompoundingWithdrawalCredential v' = false) :
    EthCLSpecs.Heze.getMaxEffectiveBalance v' = EthCLSpecs.Heze.getMaxEffectiveBalance v := by
  unfold EthCLSpecs.Heze.getMaxEffectiveBalance
  rw [h, h']

end

/-- A loop whose every step keeps `Q` at a cost `c` keeps `Q` at the cost `c` per element. -/
theorem forIn_list_ops_budget [Preset] [HasherTag] {δ : Type} (Q : Nat → BeaconState → Prop)
    (op : δ → HezeRun PUnit) (hk : ∀ d, KeepsUncached (op d)) (c : Nat) :
    ∀ (l : List δ), (∀ d ∈ l, ∀ (B : Nat) (s s' : BeaconState), Q B s →
        (op d).run (pureState s) = .ok ((), pureState s') → Q (B + c) s') →
      ∀ (B : Nat) (s s' : BeaconState), Q B s →
        (forIn l PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
          : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s') →
        Q (B + l.length * c) s' := by
  intro l
  induction l with
  | nil =>
    intro _ B s s' hs h
    rw [List.forIn_nil] at h
    rw [pureState_inj (run_pure_state_eq _ _ _ _ h)]
    simpa using hs
  | cons d rest ih =>
    intro hop B s s' hs h
    rw [List.forIn_cons] at h
    obtain ⟨step, s1, hb, hr⟩ :=
      run_bind_eq_ok_pure (keepsUncached_bind (hk d) (fun _ => keepsUncached_pure _)) h
    obtain ⟨⟨⟩, s0, hop1, hp⟩ := run_bind_eq_ok_pure (hk d) hb
    injection hp with hp
    injection hp with hstep hs1
    subst hstep
    rw [← pureState_inj hs1] at hr
    have := ih (fun d' hd' => hop d' (List.mem_cons_of_mem _ hd')) (B + c) s0 s'
      (hop d List.mem_cons_self B s s0 hs hop1) hr
    rwa [List.length_cons, Nat.add_assoc, Nat.add_comm c, Nat.succ_mul] at *

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- A BLS change writes the withdrawal credentials of one validator, from the BLS prefix to
the execution prefix. Neither is the compounding prefix. -/
theorem processBlsToExecutionChange_run (sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange)
    (a b : BeaconState)
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState a) = .ok ((), pureState b)) :
    ∃ v c, a.validators.val[sbc.message.validatorIndex.toNat]? = some v ∧
      EthCLSpecs.Heze.hasCompoundingWithdrawalCredential v = false ∧
      EthCLSpecs.Heze.hasCompoundingWithdrawalCredential { v with withdrawalCredentials := c }
        = false ∧
      b = withValidators a (a.validators.set! sbc.message.validatorIndex.toNat
        { v with withdrawalCredentials := c }) := by
  unfold EthCLSpecs.Heze.processBlsToExecutionChange at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨⟨hb⟩, -, h⟩ :=
    run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  obtain ⟨hpre, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  have e := EthCLLib.Proofs.run_modifyThe_eq_ok h
  rw [modValidator_pureState] at e
  have hb : sbc.message.validatorIndex.toNat < a.validators.val.size := hb
  have hv : a.validators.val[sbc.message.validatorIndex.toNat]? =
      some (a.validators.val[sbc.message.validatorIndex.toNat]'hb) :=
    getElem?_pos a.validators.val _ hb
  refine ⟨_, Vector.ofFn (fun i : Fin 32 =>
    if i.val == 0 then EthCLSpecs.Heze.Const.eth1AddressWithdrawalPrefix
    else if i.val < 12 then 0
    else vget sbc.message.toExecutionAddress (i.val - 12)), hv, ?_, ?_, ?_⟩
  · unfold EthCLSpecs.Heze.hasCompoundingWithdrawalCredential
    have hp : EthCLSpecs.Heze.credPrefix
        (a.validators.val[sbc.message.validatorIndex.toNat]'hb).withdrawalCredentials =
        EthCLSpecs.Heze.Const.blsWithdrawalPrefix := beq_iff_eq.mp hpre
    exact beq_false_of_ne (by rw [hp]; decide)
  · unfold EthCLSpecs.Heze.hasCompoundingWithdrawalCredential EthCLSpecs.Heze.credPrefix
    simp [vget]
    decide
  · have := pureState_inj e
    rw [this, sszList_getElem!_eq, getElem!_pos a.validators.val _ hb]
    rfl

/-- **A BLS change keeps `OpsInv`.** -/
theorem OpsInv.bls {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState} {E CX CC Γp B : Nat}
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange)
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState s) = .ok ((), pureState s')) : OpsInv vals st₀ a₀ E CX CC Γp B s' := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  obtain ⟨v, c, hv, h1, h2, rfl⟩ := processBlsToExecutionChange_run sbc s s' h
  have hj : sbc.message.validatorIndex.toNat < sizeOf s := (Array.getElem?_eq_some_iff.mp hv).1
  have w : OneWrite s (withValidators s (s.validators.set! sbc.message.validatorIndex.toNat
      { v with withdrawalCredentials := c })) sbc.message.validatorIndex.toNat v
      { v with withdrawalCredentials := c } := by
    refine ⟨hj, fun k => getElem?_validators_set s _ k _ hj, hv, rfl, ?_⟩
    show (s.validators.set! _ _).val.size = s.validators.val.size
    exact SizzLean.Proofs.sszListSet!_size _ _ _
  exact ⟨⟨V, W, tag, I.sameReads w rfl (getMax_eq_of_not_compounding h1 h2) rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl⟩, hk.trans (w.acKeep rfl rfl rfl)⟩

/-- **An attestation keeps `OpsInv`, at the cost `attBudget sq`.** `sq * sq` is at most the
total active balance at the start of the block. -/
theorem OpsInv.attestation {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) {sq : Nat} (h0 : 0 < sq)
    (hsq : sq * sq ≤ (totBal a₀).toNat)
    (att : EthCLSpecs.Heze.Attestation)
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState s) = .ok ((), pureState s')) :
    OpsInv vals st₀ a₀ E CX CC Γp (B + attBudget sq) s' := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  obtain ⟨NX, ΓX, P, -, -⟩ := X.pre
  have ht := totBal_congr hk P.h64
  obtain ⟨he, hsl, hsz, hm⟩ := processAttestation_move vals X.nodup st₀ E X.consts att s s'
    I.shape h0 (by rw [ht]; exact hsq) h
  have hv : s'.validators = s.validators := by
    simp only [econView, Prod.mk.injEq] at he
    exact he.1
  exact ⟨⟨_, W, tag, I.balanceStep he hsz hm⟩, hk.trans (AcKeep.of_validators hsl hv)⟩

/-- **A payload attestation keeps `OpsInv`.** It reads the state only. -/
theorem OpsInv.payloadAttestation {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γp B : Nat} (hs : OpsInv vals st₀ a₀ E CX CC Γp B s)
    (pa : EthCLSpecs.Heze.PayloadAttestation)
    (h : (EthCLSpecs.Heze.processPayloadAttestation (StateTransition := HezeRun) pa).run
      (pureState s) = .ok ((), pureState s')) : OpsInv vals st₀ a₀ E CX CC Γp B s' := by
  have e : (pureState s').view = (pureState s).view := processPayloadAttestation_frame h
  change s' = s at e
  subst e
  exact hs

omit [Config] [CryptoBackend] in
/-- `forIn_list_ops_budget` for an array. -/
theorem forIn_array_ops_budget {δ : Type} (Q : Nat → BeaconState → Prop)
    (op : δ → HezeRun PUnit) (hk : ∀ d, KeepsUncached (op d)) (c : Nat) (xs : Array δ)
    (hop : ∀ d ∈ xs, ∀ (B : Nat) (s s' : BeaconState), Q B s →
      (op d).run (pureState s) = .ok ((), pureState s') → Q (B + c) s')
    (B : Nat) (s s' : BeaconState) (hs : Q B s)
    (h : (forIn xs PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
      : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s')) :
    Q (B + xs.size * c) s' := by
  rw [← Array.forIn_toList] at h
  have := forIn_list_ops_budget Q op hk c xs.toList
    (fun d hd => hop d (Array.mem_toList_iff.mp hd)) B s s' hs h
  rwa [Array.length_toList] at this

/-- **The operations of a block keep `OpsInv`**, at the cost `attBudget sq` per attestation. -/
theorem processOperations_ops {vals : List ValidatorIndex} {st₀ a₀ a b : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (hΓ : Γp ≤ Γc)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B a) {sq : Nat} (h0 : 0 < sq)
    (hsq : sq * sq ≤ (totBal a₀).toNat)
    (body : EthCLSpecs.Heze.BeaconBlockBody)
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run
      (pureState a) = .ok ((), pureState b)) :
    OpsInv vals st₀ a₀ E CX CC Γp (B + body.attestations.val.size * attBudget sq) b := by
  unfold EthCLSpecs.Heze.processOperations at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun ps _ =>
    keepsUncached_bind (keepsUncached_processProposerSlashing ps)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t1 := forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC Γp B) _
    keepsUncached_processProposerSlashing body.proposerSlashings.val
    (fun ps _ s s' hs hr => hs.proposerSlashing X hΓ ps hr) a s1 hs h1
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttesterSlashing a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t2 := forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC Γp B) _
    keepsUncached_processAttesterSlashing body.attesterSlashings.val
    (fun asl _ s s' hs hr => processAttesterSlashing_inv _
      (fun _ _ i hq hi hu hr => hq.slash X hΓ i hi hu hr) asl s s' hs hr) s1 s2 t1 h2
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t3 := forIn_array_ops_budget (fun B s => OpsInv vals st₀ a₀ E CX CC Γp B s) _
    keepsUncached_processAttestation (attBudget sq) body.attestations.val
    (fun d _ B s s' hs hr => hs.attestation X h0 hsq d hr) B s2 s3 t2 h3
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processVoluntaryExit a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t4 := forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC Γp _) _
    keepsUncached_processVoluntaryExit body.voluntaryExits.val
    (fun sve _ s s' hs hr => hs.exit X hΓ _ (processVoluntaryExit_run sve s s' hr)) s3 s4 t3 h4
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processBlsToExecutionChange a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t5 := forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC Γp _) _
    keepsUncached_processBlsToExecutionChange body.blsToExecutionChanges.val
    (fun sbc _ s s' hs hr => hs.bls sbc hr) s4 s5 t4 h5
  obtain ⟨⟨⟩, s6, h6, hp⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processPayloadAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  rw [pureState_inj (run_pure_state_eq _ _ _ _ hp)]
  exact forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC Γp _) _
    keepsUncached_processPayloadAttestation body.payloadAttestations.val
    (fun pa _ s s' hs hr => hs.payloadAttestation pa hr) s5 s6 t5 h6

end

end EthCLSpecs.Proofs.Heze
