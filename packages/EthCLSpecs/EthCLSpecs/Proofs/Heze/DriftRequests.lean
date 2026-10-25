import EthCLSpecs.Proofs.Heze.DriftBlock
import SizzLean.Proofs.SSZListPush

/-!
# `EthCLSpecs.Proofs.Heze.DriftRequests`: the execution requests of a parent payload

A parent payload carries withdrawal requests and consolidation requests. A withdrawal request
is a full exit (`initiate_validator_exit`), or a partial withdrawal. A partial withdrawal
reserves exit churn for its amount and queues the amount, withdrawable `MIN_VALIDATOR_
WITHDRAWABILITY_DELAY` epochs after the reserved epoch. That epoch lies after `E`, so the
queued amount does not count in `gPart`, and the reservation adds no exit to the ledger
(`RunInv.partialReserve`). The count `Γp` of such reservations grows by one.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok run_bind run_getThe
  except_bind_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei modifyState)
open SizzLean.Proofs (sszListPush_val sszListPush?_of_lt sszListPush?_of_le)

section
variable [Preset] [HasherTag]

/-- A successful append to the queue of partial withdrawals writes the longer queue. -/
theorem appendPartial_run (a b : BeaconState) (w : EthCLSpecs.Heze.PendingPartialWithdrawal)
    (h : (appendState pendingPartialWithdrawals w : HezeRun Unit).run (pureState a)
      = .ok ((), pureState b)) :
    ∃ hlt, b = { a with pendingPartialWithdrawals := a.pendingPartialWithdrawals.push w hlt } := by
  by_cases hlt : a.pendingPartialWithdrawals.val.size <
      EthCLSpecs.Heze.Const.pendingPartialWithdrawalsLimit
  · have hpush : (sszGet (pureState a) pendingPartialWithdrawals).push? w
        = some (a.pendingPartialWithdrawals.push w hlt) :=
      sszListPush?_of_lt a.pendingPartialWithdrawals w hlt
    simp only [run_bind, run_getThe, except_bind_ok, hpush, Option.map_some] at h
    injection h with h
    injection h with _ h
    exact ⟨hlt, (congrArg SizzLean.Cache.SSZ.Box.view h).symm⟩
  · have hpush : (sszGet (pureState a) pendingPartialWithdrawals).push? w = none :=
      sszListPush?_of_le a.pendingPartialWithdrawals w (by omega)
    simp only [run_bind, run_getThe, except_bind_ok, hpush, Option.map_none] at h
    cases h

/-- A successful append to the queue of consolidations writes the longer queue. -/
theorem appendConsolidation_run (a b : BeaconState) (q : EthCLSpecs.Heze.PendingConsolidation)
    (h : (appendState pendingConsolidations q : HezeRun Unit).run (pureState a)
      = .ok ((), pureState b)) :
    ∃ hlt, b = { a with pendingConsolidations := a.pendingConsolidations.push q hlt } := by
  by_cases hlt : a.pendingConsolidations.val.size < EthCLSpecs.Heze.Const.pendingConsolidationsLimit
  · have hpush : (sszGet (pureState a) pendingConsolidations).push? q
        = some (a.pendingConsolidations.push q hlt) :=
      sszListPush?_of_lt a.pendingConsolidations q hlt
    simp only [run_bind, run_getThe, except_bind_ok, hpush, Option.map_some] at h
    injection h with h
    injection h with _ h
    exact ⟨hlt, (congrArg SizzLean.Cache.SSZ.Box.view h).symm⟩
  · have hpush : (sszGet (pureState a) pendingConsolidations).push? q = none :=
      sszListPush?_of_le a.pendingConsolidations q (by omega)
    simp only [run_bind, run_getThe, except_bind_ok, hpush, Option.map_none] at h
    cases h

/-- **A step that changes only the exit churn ledger keeps the invariant**, with a new ledger
and a new bound on `earliest_exit_epoch`. -/
theorem RunInv.exitLedger {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp Γp' B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hv : b.validators = a.validators)
    (hbal : b.balances = a.balances) (hphi : phi vals E b = phi vals E a)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch)
    (L : Ledger vals st₀ b W tag true st₀.earliestExitEpoch.toNat st₀.exitBalanceToConsume.toNat
      b.earliestExitEpoch.toNat b.exitBalanceToConsume.toNat CX)
    (hee : b.earliestExitEpoch.toNat ≤ max st₀.earliestExitEpoch.toNat (E + lagN) +
      exitedCount b * maddX + Γp' * maddP) :
    RunInv vals st₀ E CX CC b V W tag Γp' B := by
  have e1 : ∀ i, capN b i = capN a i := fun i => by simp [capN, balN, maxN, hv, hbal]
  have e2 : ∀ i, ebN b i = ebN a i := fun i => by simp [ebN, hv]
  have e4 : ∀ i, actOf b i = actOf a i := fun i => by simp [actOf, hv]
  have e5 : ∀ i, exitOf b i = exitOf a i := fun i => by simp [exitOf, hv]
  have e6 : ∀ i, wdrOf b i = wdrOf a i := fun i => by simp [wdrOf, hv]
  have e7 : sizeOf b = sizeOf a := by simp [sizeOf, hv]
  have e9 : ∀ i, maxN b i = maxN a i := fun i => by simp [maxN, hv]
  have e10 := exitedCount_eq e7 e5
  have e11 : ∀ i, slashedOf b i = slashedOf a i := fun i => by simp [slashedOf, hv]
  refine ⟨fun i hi hl => by rw [e1]; exact I.cap i hi hl, by rw [hphi]; exact I.bud,
    fun i hi hl => by rw [e2]; exact I.track i hi hl, fun i h1 h2 => by rw [e4]; exact I.actOnce i h1 h2,
    fun i h1 h2 => by rw [e5]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => I.newExit i hi h1 h2 (by rw [← e5]; exact h3),
    L, by rw [hc1, hc2]; exact I.churnC.of_exit_eq e5, ?_,
    fun i hi hl hs => by rw [e6]; exact I.live i hi hl (by rw [← e7]; exact hs),
    by rw [e7]; exact I.sizeLe, hee, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [e6]; exact I.slashInv i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)⟩
  obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
  refine ⟨by rw [hv, hbal]; exact s1, fun i hi => ?_, fun i hi => ?_, fun i hi hx => ?_,
    fun i hi hs => ?_⟩
  · rw [e2, e9]; exact s2 i (by rw [← e7]; exact hi)
  · rw [e2]; exact s3 i (by rw [← e7]; exact hi)
  · rw [e6]; exact s4 i (by rw [← e7]; exact hi) (by rw [← e5]; exact hx)
  · rw [e5]; exact s5 i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [CryptoBackend] in
/-- **A partial withdrawal keeps the invariant**, with one more reservation in `Γp`. The run
reserves exit churn for `bal` and queues a withdrawal at the reserved epoch plus the delay. -/
theorem RunInv.partialReserve {vals : List ValidatorIndex} {st₀ a a1 b : BeaconState}
    {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (bal : Gwei) (x : EthCLSpecs.Heze.Epoch)
    (h1 : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) bal).run
      (pureState a) = .ok (x, pureState a1))
    (w : EthCLSpecs.Heze.PendingPartialWithdrawal)
    (hw : w.withdrawableEpoch = x + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay)
    (h2 : (appendState pendingPartialWithdrawals w : HezeRun Unit).run (pureState a1)
      = .ok ((), pureState b))
    (hCl : incN ≤ (exitChurn a).toNat)
    (hCu : (exitChurn a).toNat ≤ CX) (hinc : 0 < incN)
    (hcur : epochN st₀ ≤ epochN a) (hcurE : epochN a ≤ E)
    (hkE : E < epochN st₀ + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat)
    (hsmall : max st₀.earliestExitEpoch.toNat (E + lagN) + exitedCount a * maddX +
      (Γp + 1) * maddP < 2 ^ 62)
    (hc62 : max st₀.exitBalanceToConsume.toNat CX < 2 ^ 62) (hb62 : bal.toNat < 2 ^ 62)
    (hd62 : EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 62) :
    AcKeep a b ∧ RunInv vals st₀ E CX CC b V W tag (Γp + 1) B := by
  obtain ⟨act, c, hactE, -, hres, hs1⟩ := computeExitEpochAndUpdateChurn_run bal a h1
  subst hs1
  obtain ⟨hlt, hb⟩ := appendPartial_run _ b w h2
  unfold afterExitChurn at hb
  -- The fields of `b`.
  have hbv : b.validators = a.validators := by rw [hb]
  have hbbal : b.balances = a.balances := by rw [hb]
  have hbsl : b.slot = a.slot := by rw [hb]
  have hbee : b.earliestExitEpoch = x := by rw [hb]
  have hbebc : b.exitBalanceToConsume = (afterExitChurn a bal x c).exitBalanceToConsume := by
    rw [hb]; rfl
  have hbppw : b.pendingPartialWithdrawals.val.toList =
      a.pendingPartialWithdrawals.val.toList ++ [w] := by
    rw [hb, sszListPush_val, Array.toList_push]
  have hbpc : b.pendingConsolidations = a.pendingConsolidations := by rw [hb]
  have hbdbc : b.depositBalanceToConsume = a.depositBalanceToConsume := by rw [hb]
  have hbc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume := by rw [hb]
  have hbc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch := by rw [hb]
  clear hb
  generalize hC : (exitChurn a).toNat = C at hCl hCu
  -- The reservation on `Nat`, as in `RunInv.initiateExit`.
  have hee := I.eeLe
  have hmaxE := Nat.le_max_right st₀.earliestExitEpoch.toNat (E + lagN)
  have hcurlag : epochN a + lagN < 2 ^ 62 := by omega
  have hee62 : a.earliestExitEpoch.toNat < 2 ^ 62 := by
    have : Γp * maddP ≤ (Γp + 1) * maddP := Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  have hearl := earliest_toNat a hactE (by omega)
  have hebcle : a.exitBalanceToConsume.toNat ≤ max st₀.exitBalanceToConsume.toNat CX :=
    I.churnX.ebcLe
  have hC62 : C < 2 ^ 62 := by have := Nat.le_max_right st₀.exitBalanceToConsume.toNat CX; omega
  have hcons : (if a.earliestExitEpoch < umax a.earliestExitEpoch act
      then exitChurn a else a.exitBalanceToConsume).toNat =
      if a.earliestExitEpoch.toNat < max a.earliestExitEpoch.toNat (epochN a + lagN) then C
      else a.exitBalanceToConsume.toNat := by
    by_cases hlt : a.earliestExitEpoch.toNat < max a.earliestExitEpoch.toNat (epochN a + lagN)
    · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hearl]; exact hlt), if_pos hlt, hC]
    · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hearl]; exact hlt), if_neg hlt]
  obtain ⟨hx1, hx2⟩ := reserveChurn_toNat bal _ _ _ hb62
    (by rw [hcons]; split <;> omega) (by rw [hC]; omega) (by rw [hC]; exact hC62)
    (by rw [hearl]; omega) hres
  rw [hcons, hearl, hC] at hx1
  rw [hcons, hC] at hx2
  have hxN : x.toNat = resEpoch lagN a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat
      (epochN a) C bal.toNat := by
    rw [hx1]; rfl
  have htot : c.toNat =
      resTotal lagN a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C bal.toNat := by
    rw [hx2]; rfl
  -- The ledger: the reservation records no exit.
  have hexit : ∀ k, exitOf b k = exitOf a k := fun k => by simp [exitOf, hbv]
  have hS : ∀ X, churnSum vals st₀ b W tag true X = churnSum vals st₀ a W tag true X := fun X => by
    simp only [churnSum, hexit, sizeOf]; congr
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ledger_step (e₀ := epochN st₀) (ee₀ := st₀.earliestExitEpoch.toNat)
    (ebc₀ := st₀.exitBalanceToConsume.toNat) (Cmax := CX) (bal := bal.toNat) hcur (by omega) hCu
    I.churnX.mono I.churnX.held (Nat.le_add_right _ _)
  have hebc' : (afterExitChurn a bal x c).exitBalanceToConsume.toNat = resTotal lagN
      a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C bal.toNat - bal.toNat := by
    show (c - bal).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [htot]; exact hl4)), htot]
  -- The queued withdrawal lies after `E`.
  have hwN : w.withdrawableEpoch.toNat =
      x.toNat + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat := by
    rw [hw, UInt64.toNat_add, Nat.mod_eq_of_lt]
    have := resEpoch_le a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C bal.toNat
    have hbC : bal.toNat / C ≤ bal.toNat := Nat.div_le_self _ _
    omega
  have hxge : epochN a + lagN ≤ x.toNat := by rw [hxN]; exact hl3
  have hphi : phi vals E b = phi vals E a := by
    have hf : (List.filter (fun w => decide (w.withdrawableEpoch.toNat ≤ E)) [w]) = [] := by
      simp only [List.filter_cons, List.filter_nil]
      rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
    unfold phi gPart gCons gSl sizeOf slashedOf maxN wdrOf
    rw [hbppw, hbv, hbpc, hbdbc, List.filter_append, hf, List.append_nil]
  have hsz : sizeOf b = sizeOf a := by simp [sizeOf, hbv]
  have hle2 : a.earliestExitEpoch.toNat ≤ x.toNat := by rw [hxN]; exact hl2
  refine ⟨AcKeep.of_validators hbsl hbv,
    I.exitLedger hbv hbbal hphi hbc1 hbc2 ⟨?_, ?_, ?_, ?_, ?_⟩ ?_⟩
  · rw [hS, hbee, hxN, hbebc, hebc']
    exact hl1
  · intro k hk j1 j2 j3 j4
    rw [hexit] at j3 ⊢
    rw [hbee]
    exact Nat.le_trans (I.churnX.le_ee k hk j1 j2 j3 j4) hle2
  · intro X; rw [hS]; exact I.churnX.upTo X
  · rw [hbee]; exact Nat.le_trans I.churnX.mono hle2
  · rw [hbebc, hebc']
    have := resTotal_sub_le a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C
      bal.toNat
    have := I.churnX.ebcLe
    omega
  · rw [hbee, exitedCount_eq hsz hexit]
    have h1 := resEpoch_le a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C
      bal.toNat
    rw [← hxN] at h1
    have h2 : bal.toNat / C ≤ 2 ^ 62 / incN :=
      Nat.le_trans (Nat.div_le_div_right (Nat.le_of_lt hb62)) (Nat.div_le_div_left hCl hinc)
    have h3 : (Γp + 1) * maddP = Γp * maddP + maddP := Nat.succ_mul _ _
    have h4 : maddP = 2 ^ 62 / incN + 1 := rfl
    omega

end

end EthCLSpecs.Proofs.Heze
