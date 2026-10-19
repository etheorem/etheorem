import EthCLSpecs.Proofs.Heze.DriftDeposits

/-!
# `EthCLSpecs.Proofs.Heze.DriftEpochStep`: one epoch keeps the invariant

`process_epoch` runs its writers in the order of the spec. Each writer keeps `RunInv`
(`RunInv.processEpoch`). The rewards cost `rewBudget`, the correlation penalties cost
`slEpoch` of the epoch, and the deposits cost `churnA`. The other writers are paid by the
potentials or move no counted balance.

The deposit step reads the queue of pending deposits. The writers before it keep that queue
(`pdBox`), so the bounds on the queue at the start of the epoch hold there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

/-- The deposit churn and the queue of pending deposits of the view of a box. -/
def pdBox (st : State) := (st.view.depositBalanceToConsume, st.view.pendingDeposits)

/-- The inactivity scores of the view of a box. -/
def scBox (st : State) := st.view.inactivityScores

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `increaseBalance` returns a state value with the `pdBox` of its argument. -/
@[frame] theorem increaseBalance_ret_pd {u t t' b : BeaconState} {i : ValidatorIndex}
    {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    pdBox (pureState b) = pdBox (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the `pdBox` of its argument. -/
@[frame] theorem decreaseBalance_ret_pd {u t t' b : BeaconState} {i : ValidatorIndex}
    {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    pdBox (pureState b) = pdBox (pureState u) := by
  frame_invert h

/-- `applyDeltas` returns a state value with the `pdBox` of its argument. -/
@[frame] theorem applyDeltas_ret_pd {u t t' b : BeaconState} {r p : Array Gwei}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) r p (pureState u)).run
      (pureState t) = .ok (pureState b, pureState t')) :
    pdBox (pureState b) = pdBox (pureState u) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps `pdBox`. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame_pd {t t' : BeaconState} {a : _}
    {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps `pdBox`. -/
@[frame] theorem processEth1DataReset_frame_pd {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  frame_invert h

/-- `processSlashings` keeps `pdBox`. -/
@[frame] theorem processSlashings_frame_pd {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  frame_invert h

/-- `processInactivityUpdates` keeps `pdBox`. -/
@[frame] theorem processInactivityUpdates_frame_pd {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  frame_invert h

/-- `processRewardsAndPenalties` keeps `pdBox`. -/
@[frame] theorem processRewardsAndPenalties_frame_pd {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps `pdBox`. -/
@[frame] theorem initiateValidatorExit_frame_pd {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  frame_invert h

/-- `processRegistryUpdates` keeps `pdBox`. -/
@[frame] theorem processRegistryUpdates_frame_pd {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  frame_invert h

/-- `processJustificationAndFinalization` keeps `pdBox`. -/
@[frame] theorem processJustificationAndFinalization_frame_pd {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pdBox (pureState t') = pdBox (pureState t) := by
  jf_frame pdBox h

/-- `processJustificationAndFinalization` keeps the inactivity scores. -/
@[frame] theorem processJustificationAndFinalization_frame_sc {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    scBox (pureState t') = scBox (pureState t) := by
  jf_frame scBox h

end

section
variable [Preset] [HasherTag]

/-! ## Reading frames off a run -/

theorem econ_of_frame {a b : BeaconState} (h : econBox (pureState b) = econBox (pureState a)) :
    econView b = econView a := h

theorem slot_of_frame {a b : BeaconState}
    (h : windowView (pureState b) = windowView (pureState a)) : b.slot = a.slot :=
  congrArg (fun w => w.1.1) h

theorem pd_of_frame {a b : BeaconState} (h : pdBox (pureState b) = pdBox (pureState a)) :
    b.depositBalanceToConsume = a.depositBalanceToConsume ∧
      b.pendingDeposits = a.pendingDeposits := by
  simp only [pdBox, SizzLean.Proofs.view_uncachedBox, Prod.mk.injEq] at h
  exact h

omit [HasherTag] in
theorem validators_of_econ {a b : BeaconState} (h : econView b = econView a) :
    b.validators = a.validators := by
  simp only [econView, Prod.mk.injEq] at h
  exact h.1

/-- The correlation penalties of one epoch, over the registry of `st₀`. -/
def slEpoch (st₀ : BeaconState) (ep : Nat) : Nat := ((List.range (sizeOf st₀)).map (slBud st₀ ep)).sum

omit [HasherTag] in
theorem sum_slBud_le (st₀ : BeaconState) (ep n : Nat) :
    ((List.range n).map (slBud st₀ ep)).sum ≤ slEpoch st₀ ep := by
  unfold slEpoch
  by_cases hn : n ≤ sizeOf st₀
  · exact sublist_sum_le _ (List.range_sublist.mpr hn)
  · have e : n = sizeOf st₀ + (n - sizeOf st₀) := by omega
    rw [e, List.range_add, List.map_append, List.sum_append]
    have : ((List.map (fun x => sizeOf st₀ + x) (List.range (n - sizeOf st₀))).map
        (slBud st₀ ep)).sum = 0 := by
      rw [List.map_map]
      refine sum_zero_of _ fun x hx => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      unfold slBud
      simp only [Function.comp]
      rw [if_neg (fun h => by omega)]
    omega

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The bound of the move of one epoch, but the correlation penalties. -/
def epochBudget (sq U S : Nat) : Nat :=
  rewBudget sq U (S + EthCLSpecs.Heze.Const.inactivityScoreBias.toNat) + churnA

/-- **One epoch keeps the invariant.** The epoch starts at `e`, where the exit facts of
`StepPre` hold, `sq * sq` is at most the total active balance, `U` bounds the sum of the
effective balances, and `S` bounds each inactivity score. It ends at `e'`, where each balance
is below `2 ^ 64 - downN`. The epoch costs `epochBudget sq U S` plus the correlation
penalties `slEpoch` of its epoch. -/
theorem RunInv.processEpoch {vals : List ValidatorIndex} {st₀ e e' : BeaconState}
    {E CX CC NX ΓX : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (C : DriftConsts) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀)
    (cov : ∀ i, i < sizeOf e → UInt64.ofNat i ∈ vals)
    (P : StepPre st₀ e E CX NX ΓX) (hNX : sizeOf e + 1 ≤ NX) (hΓX : Γp ≤ ΓX)
    (I : RunInv vals st₀ E CX CC e V W tag Γp B)
    {sq U S : Nat} (h0 : 0 < sq)
    (hsq : sq * sq ≤ (totBal e).toNat)
    (hU : ebSum e ≤ U) (hinc : incN ≤ U) (hS : ∀ i, scoreN e i ≤ S)
    (hk2 : E < epochN st₀ + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2)
    (hep62 : epochN e + EthCLSpecs.Heze.Const.epochsPerSlashingsVector < 2 ^ 62)
    (hEf : E + 1 < farN) (hav : e.depositBalanceToConsume.toNat + churnA < 2 ^ 63)
    (hamt : ∀ i : Nat,
      (e.pendingDeposits.toArray[i]! : EthCLSpecs.Heze.PendingDeposit).amount.toNat < 2 ^ 63)
    (hsz : sizeOf e + EthCLSpecs.Heze.Const.pendingDepositsLimit < 2 ^ 64)
    (h : (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run (pureState e)
      = .ok ((), pureState e'))
    (hbal : ∀ i, i < sizeOf e' → balN e' i + downN < 2 ^ 64) (h64' : sizeOf e' < 2 ^ 64) :
    e'.slot = e.slot ∧ ∃ V' W' tag', RunInv vals st₀ E CX CC e' V' W' tag' Γp
      (B + epochBudget sq U S + slEpoch st₀ (epochN e)) := by
  have hslot : e'.slot = e.slot := congrArg Prod.fst (processEpoch_frame_spine h)
  refine ⟨hslot, ?_⟩
  rw [processEpoch_eq] at h
  obtain ⟨⟨⟩, p1, hP, h⟩ := run_bind_eq_ok_pure keepsUncached_processEpochPrefix h
  obtain ⟨⟨⟩, p2, hBP, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processBuilderPendingPayments h
  unfold processEpochPrefix at hP
  -- Justification and finalization: a frame.
  obtain ⟨⟨⟩, a1, h1, hP⟩ := run_bind_eq_ok_pure keepsUncached_processJustificationAndFinalization hP
  have ec1 := econ_of_frame (processJustificationAndFinalization_frame_econ h1)
  have sl1 := slot_of_frame (processJustificationAndFinalization_frame h1)
  have pd1 := pd_of_frame (processJustificationAndFinalization_frame_pd h1)
  have sc1 : a1.inactivityScores = e.inactivityScores :=
    processJustificationAndFinalization_frame_sc h1
  have I1 := I.of_econ ec1
  have K1 : AcKeep e a1 := AcKeep.of_validators sl1 (validators_of_econ ec1)
  -- The inactivity updates: the scores rise by at most the bias.
  obtain ⟨⟨⟩, a2, h2, hP⟩ := run_bind_eq_ok_pure keepsUncached_processInactivityUpdates hP
  obtain ⟨ha2, hsc2⟩ := processInactivityUpdates_scores a1 a2 (S := S)
    (fun i => by unfold scoreN; rw [sc1]; exact hS i) (by have := P.h64; rw [K1.size]; unfold sizeOf at *; omega) h2
  have ec2 : econView a2 = econView a1 := by rw [ha2]; rfl
  have I2 := I1.of_econ ec2
  have K2 : AcKeep e a2 := K1.trans (AcKeep.of_validators (by rw [ha2]) (validators_of_econ ec2))
  have pd2 := pd_of_frame (processInactivityUpdates_frame_pd h2)
  -- The rewards and penalties.
  obtain ⟨⟨⟩, a3, h3, hP⟩ := run_bind_eq_ok_pure keepsUncached_processRewardsAndPenalties hP
  have hT2 := totBal_congr K2 P.h64
  have hv2 : a2.validators = e.validators := (validators_of_econ ec2).trans (validators_of_econ ec1)
  obtain ⟨K3', V3, I3⟩ := I2.processRewardsAndPenalties vals hnd st₀ (S := S + _) h0
    (by have := P.h64; rw [K2.size]; unfold sizeOf at *; omega) (by rw [hT2]; exact hsq)
    (by unfold ebSum sizeOf ebN; rw [hv2]; exact hU) hinc (fun i _ => hsc2 i) h3
  have K3 := K2.trans K3'
  have pd3 := pd_of_frame (processRewardsAndPenalties_frame_pd h3)
  -- The registry updates.
  obtain ⟨⟨⟩, a4, h4, hP⟩ := run_bind_eq_ok_pure keepsUncached_processRegistryUpdates hP
  have X : OpsCtx vals st₀ a3 E CX Γp :=
    ⟨C, hnd, hshape₀, ⟨NX, ΓX, P.keep K3, by rw [K3.size]; exact hNX, hΓX⟩,
      fun i hi => cov i (by rw [← K3.size]; exact hi)⟩
  obtain ⟨⟨V4, W4, tag4, I4⟩, K4'⟩ := OpsInv.processRegistryUpdates X (Nat.le_refl _)
    ⟨⟨V3, W, tag, I3⟩, AcKeep.refl a3⟩ h4
  have K4 := K3.trans K4'
  have pd4 := pd_of_frame (processRegistryUpdates_frame_pd h4)
  -- The correlation penalties.
  obtain ⟨⟨⟩, a5, h5, hP⟩ := run_bind_eq_ok_pure keepsUncached_processSlashings hP
  obtain ⟨K5', V5, I5⟩ := I4.processSlashings vals hnd st₀ C (by rw [K4.epoch]; exact P.curE) hk2
    (by rw [K4.epoch]; exact hep62) h5
  have K5 := K4.trans K5'
  have pd5 := pd_of_frame (processSlashings_frame_pd h5)
  -- The eth1 reset: a frame.
  obtain ⟨⟨⟩, a6, h6, hP⟩ := run_bind_eq_ok_pure keepsUncached_processEth1DataReset hP
  have ec6 := econ_of_frame (processEth1DataReset_frame_econ h6)
  have I6 := I5.of_econ ec6
  have K6 := K5.trans (AcKeep.of_validators (slot_of_frame (processEth1DataReset_frame h6))
    (validators_of_econ ec6))
  have pd6 := pd_of_frame (processEth1DataReset_frame_pd h6)
  -- The pending deposits.
  obtain ⟨⟨⟩, a7, h7, hP⟩ := run_bind_eq_ok_pure keepsUncached_processPendingDeposits hP
  have hdb6 : a6.depositBalanceToConsume = e.depositBalanceToConsume :=
    pd6.1.trans (pd5.1.trans (pd4.1.trans (pd3.1.trans (pd2.1.trans pd1.1))))
  have hpd6 : a6.pendingDeposits = e.pendingDeposits :=
    pd6.2.trans (pd5.2.trans (pd4.2.trans (pd3.2.trans (pd2.2.trans pd1.2))))
  obtain ⟨V7, I7⟩ := I6.processPendingDeposits vals hnd st₀ C (by rw [K6.epoch]; exact P.curE) hEf
    (by rw [K6.epoch]; omega) (by rw [hdb6]; exact hav) (by rw [hpd6]; exact hamt)
    (by rw [hpd6, K6.size]; have := e.pendingDeposits.property; unfold SizzLean.Repr.SSZList.toArray; omega) h7
  have sl7 := slot_of_frame (processPendingDeposits_frame h7)
  -- The pending consolidations.
  have hep7 : epochN a7 ≤ E := by
    have : epochN a7 = epochN a6 := by
      show (EthCLSpecs.Heze.computeEpochAtSlot a7.slot).toNat =
        (EthCLSpecs.Heze.computeEpochAtSlot a6.slot).toNat
      rw [sl7]
    rw [this, K6.epoch]; exact P.curE
  obtain ⟨-, V8, I8⟩ := I7.processPendingConsolidations vals hnd st₀ C hep7 hP
  -- The builder payments: a frame.
  have I9 := I8.of_econ (econ_of_frame (processBuilderPendingPayments_frame_econ hBP))
  -- The effective balance updates, then the frames of the suffix.
  unfold processEpochSuffix at hSf
  obtain ⟨⟨⟩, a10, h10, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processEffectiveBalanceUpdates hSf
  have e10 : a10 = (List.range' 0 p2.validators.size).foldl ebuBody p2 :=
    processEffectiveBalanceUpdates_run p2 a10 h10
  obtain ⟨⟨⟩, a11, h11, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processSlashingsReset hSf
  obtain ⟨⟨⟩, a12, h12, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processRandaoMixesReset hSf
  obtain ⟨⟨⟩, a13, h13, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processHistoricalSummariesUpdate hSf
  obtain ⟨⟨⟩, a14, h14, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processParticipationFlagUpdates hSf
  obtain ⟨⟨⟩, a15, h15, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processSyncCommitteeUpdates hSf
  obtain ⟨⟨⟩, a16, h16, hSf⟩ := run_bind_eq_ok_pure keepsUncached_processProposerLookahead hSf
  have ecT : econView e' = econView a10 :=
    (econ_of_frame (processPtcWindow_frame_econ hSf)).trans <|
    (econ_of_frame (processProposerLookahead_frame_econ h16)).trans <|
    (econ_of_frame (processSyncCommitteeUpdates_frame_econ h15)).trans <|
    (econ_of_frame (processParticipationFlagUpdates_frame_econ h14)).trans <|
    (econ_of_frame (processHistoricalSummariesUpdate_frame_econ h13)).trans <|
    (econ_of_frame (processRandaoMixesReset_frame_econ h12)).trans <|
    (econ_of_frame (processSlashingsReset_frame_econ h11))
  -- The registry size and the balances at the end are those before the updates.
  have hvT : e'.validators = a10.validators := validators_of_econ ecT
  have hbT : e'.balances = a10.balances := by
    simp only [econView, Prod.mk.injEq] at ecT
    exact ecT.2.1
  have hfold : ∀ (l : List Nat) (t : BeaconState),
      (l.foldl ebuBody t).validators.size = t.validators.size ∧ (l.foldl ebuBody t).balances = t.balances := by
    intro l
    induction l with
    | nil => intro t; exact ⟨rfl, rfl⟩
    | cons j rest ih =>
      intro t
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (ebuBody t j)
      exact ⟨h1.trans (ebuBody_size t j), h2.trans (ebuBody_balances t j)⟩
  obtain ⟨hs10, hb10⟩ := hfold (List.range' 0 p2.validators.size) p2
  rw [← e10] at hs10 hb10
  have hsz2 : sizeOf p2 = sizeOf e' := by
    show p2.validators.val.size = e'.validators.val.size
    rw [hvT]; exact hs10.symm
  have I10 := I9.ebuStep C (by rw [hsz2]; exact h64')
    (fun i hi => by
      have := hbal i (by rw [← hsz2]; exact hi)
      unfold balN at this ⊢
      rw [hbT, hb10] at this
      exact this)
    (fun i hi => by
      have h1 := I9.shape.ebLe i hi
      have h2 : maxN p2 i ≤ maxEBN := by
        unfold maxN
        split
        · exact C.maxLe _
        · exact Nat.zero_le _
      have := C.upSmall
      have := C.maxEB62
      omega)
  rw [← e10] at I10
  refine ⟨_, _, _, (I10.of_econ ecT).mono_B ?_⟩
  -- The budget: the correlation penalties of the registry of `a4` are those of `st₀`.
  have hsl := sum_slBud_le st₀ (epochN a4) (sizeOf a4)
  rw [← K4.epoch]
  unfold epochBudget
  omega

end

end EthCLSpecs.Proofs.Heze
