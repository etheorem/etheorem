import EthCLSpecs.Proofs.Heze.DriftRewards

/-!
# `EthCLSpecs.Proofs.Heze.DriftDeposits`: the pending deposits of an epoch

`process_pending_deposits` scans the deposit queue. A deposit tops up the balance of a
known validator, or appends a new validator (`addValidatorToRegistry_run`,
`RunInv.addValidator`). A deposit that consumes churn moves the balances by at most its
amount. A deposit to a validator that is withdrawable by the next epoch consumes no churn, and
it moves no counted balance (`RunInv.applyPendingDeposit`).

The scan keeps `RunInv` at the budget plus the churn that it consumed. The last write sets
the deposit churn that carries over, and the potential `phi` reads it. So the epoch costs at
most `churnA`, the bound of the activation churn of one epoch
(`RunInv.processPendingDeposits`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei modifyState)

section
variable [Preset] [HasherTag]

/-- The registry and the balances. -/
def vbBox (s : State) := (s.view.validators, s.view.balances)

/-- The fields that the deposit scan reads or that the invariant reads, but the registry and
the balances. -/
def depView (u : BeaconState) :=
  (u.slot, u.pendingConsolidations, u.pendingPartialWithdrawals, u.depositBalanceToConsume,
    u.exitBalanceToConsume, u.earliestExitEpoch, u.consolidationBalanceToConsume,
    u.earliestConsolidationEpoch, u.pendingDeposits, u.finalizedCheckpoint, u.eth1DepositIndex,
    u.depositRequestsStartIndex)

def depBox (s : State) := depView s.view

/-- A successful append to the registry writes the longer registry. -/
theorem appendValidator_run (a : BeaconState) (v : Validator) {s' : BeaconState}
    (h : (appendState validators v : HezeRun Unit).run (pureState a) = .ok ((), pureState s')) :
    ∃ hlt, pureState s' = pureState { a with validators := a.validators.push v hlt } := by
  by_cases hlt : a.validators.val.size < EthCLSpecs.Heze.Const.validatorRegistryLimit
  · have hpush : (sszGet (pureState a) validators).push? v = some (a.validators.push v hlt) :=
      SizzLean.Proofs.sszListPush?_of_lt a.validators v hlt
    simp only [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe, EthCLLib.Proofs.except_bind_ok,
      hpush, Option.map_some] at h
    injection h with h
    injection h with _ h
    exact ⟨hlt, h.symm⟩
  · have hpush : (sszGet (pureState a) validators).push? v = none :=
      SizzLean.Proofs.sszListPush?_of_le a.validators v (by omega)
    simp only [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe, EthCLLib.Proofs.except_bind_ok,
      hpush, Option.map_none] at h
    cases h

/-- A successful append to the balances writes the longer list. -/
theorem appendBalance_run (a : BeaconState) (x : Gwei) {s' : BeaconState}
    (h : (appendState balances x : HezeRun Unit).run (pureState a) = .ok ((), pureState s')) :
    ∃ hlt, pureState s' = pureState { a with balances := a.balances.push x hlt } := by
  by_cases hlt : a.balances.val.size < EthCLSpecs.Heze.Const.validatorRegistryLimit
  · have hpush : (sszGet (pureState a) balances).push? x = some (a.balances.push x hlt) :=
      SizzLean.Proofs.sszListPush?_of_lt a.balances x hlt
    simp only [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe, EthCLLib.Proofs.except_bind_ok,
      hpush, Option.map_some] at h
    injection h with h
    injection h with _ h
    exact ⟨hlt, h.symm⟩
  · have hpush : (sszGet (pureState a) balances).push? x = none :=
      SizzLean.Proofs.sszListPush?_of_le a.balances x (by omega)
    simp only [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe, EthCLLib.Proofs.except_bind_ok,
      hpush, Option.map_none] at h
    cases h

/-- **`add_validator_to_registry` appends one validator and one balance**, and keeps the
fields of `depView`. -/
theorem addValidatorToRegistry_run (pk : EthCLSpecs.Heze.BLSPubkey) (wc : EthCLSpecs.Heze.Bytes32)
    (amt : Gwei) (t b : BeaconState) (hsz : t.balances.val.size = t.validators.val.size)
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amt).run
      (pureState t) = .ok ((), pureState b)) :
    (∃ hlt, b.validators = t.validators.push (EthCLSpecs.Heze.getValidatorFromDeposit pk wc amt) hlt) ∧
      (∃ hlt, b.balances = t.balances.push amt hlt) ∧ depView b = depView t := by
  have hd : depBox (pureState b) = depBox (pureState t) := by frame_invert h
  unfold EthCLSpecs.Heze.addValidatorToRegistry at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have h1 := run_get_bind_eq_ok _ _ _ h1
  try dsimp only at h1
  rcases run_ite_eq_ok h1 with ⟨-, h1⟩ | ⟨hne, -⟩
  · obtain ⟨hlt1, e1⟩ := appendValidator_run _ _ h1
    cases pureState_inj e1
    obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
    have h2 := run_get_bind_eq_ok _ _ _ h2
    try dsimp only at h2
    rcases run_ite_eq_ok h2 with ⟨-, h2⟩ | ⟨hne, -⟩
    · obtain ⟨hlt2, e2⟩ := appendBalance_run _ _ h2
      -- The last three writes keep the registry and the balances.
      have hv : vbBox (pureState b) = vbBox (pureState s2) := by frame_invert h
      cases pureState_inj e2
      simp only [vbBox, SizzLean.Proofs.view_uncachedBox, Prod.mk.injEq] at hv
      refine ⟨⟨hlt1, hv.1⟩, ⟨hlt2, hv.2⟩, ?_⟩
      simpa [depBox] using hd
    · simp [hsz] at hne
  · simp at hne

/-- **An appended validator keeps the invariant**, at the cost of its balance. The new
validator has no exit, is not slashed, and has an effective balance that is a multiple of the
increment, at most its balance and its cap. -/
theorem RunInv.addValidator {vals : List ValidatorIndex} {st₀ t b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat} (C : DriftConsts) (hnd : vals.Nodup)
    (I : RunInv vals st₀ E CX CC t V W tag Γp B) (v : Validator) (x : Gwei)
    (hv : b.validators.val = t.validators.val.push v) (hb : b.balances.val = t.balances.val.push x)
    (hd : depView b = depView t) (hE : E + 1 < farN)
    (hvx : v.exitEpoch.toNat = farN) (hvw : v.withdrawableEpoch.toNat = farN)
    (hvs : v.slashed = false) (hvle : v.effectiveBalance.toNat ≤ x.toNat)
    (hvm : v.effectiveBalance.toNat ≤ (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat)
    (hvmul : v.effectiveBalance.toNat % incN = 0) :
    RunInv vals st₀ E CX CC b (stepV V t b) W tag Γp (B + x.toNat) := by
  simp only [depView, Prod.mk.injEq] at hd
  obtain ⟨-, hq1, hq2, hdb, hx1, hx2, hc1, hc2, -⟩ := hd
  have hsz := I.shape.sizes
  -- The reads of `b`: the reads of `t`, and the new validator at `n`.
  have gv : ∀ k, b.validators.val[k]? = if k = sizeOf t then some v else t.validators.val[k]? :=
    fun k => by rw [hv, Array.getElem?_push]; rfl
  have gb : ∀ k, b.balances.val[k]? = if k = sizeOf t then some x else t.balances.val[k]? :=
    fun k => by rw [hb, Array.getElem?_push, hsz]; rfl
  have tnone : t.validators.val[sizeOf t]? = none := Array.getElem?_eq_none (Nat.le_refl _)
  have tbnone : t.balances.val[sizeOf t]? = none :=
    Array.getElem?_eq_none (by rw [hsz]; exact Nat.le_refl _)
  have rd : ∀ (f : Validator → Nat) (d k : Nat), k ≠ sizeOf t →
      (match b.validators.val[k]? with | some u => f u | none => d) =
        (match t.validators.val[k]? with | some u => f u | none => d) := fun f d k hk => by
    rw [gv k, if_neg hk]
  have rs : ∀ (f : Validator → Nat) (d : Nat),
      (match b.validators.val[sizeOf t]? with | some u => f u | none => d) = f v := fun f d => by
    rw [gv, if_pos rfl]
  have ebal : ∀ k, k ≠ sizeOf t → balN b k = balN t k := fun k hk => by
    unfold balN; rw [gb k, if_neg hk]
  have eeb : ∀ k, k ≠ sizeOf t → ebN b k = ebN t k := fun k hk => rd _ 0 k hk
  have emx : ∀ k, k ≠ sizeOf t → maxN b k = maxN t k := fun k hk => rd _ 0 k hk
  have ecap : ∀ k, k ≠ sizeOf t → capN b k = capN t k := fun k hk => by
    unfold capN; rw [ebal k hk, emx k hk]
  have eact : ∀ k, k ≠ sizeOf t → actOf b k = actOf t k := fun k hk => rd _ 0 k hk
  have eex : ∀ k, exitOf b k = exitOf t k := fun k => by
    by_cases hk : k = sizeOf t
    · subst hk; unfold exitOf; rw [gv, if_pos rfl, tnone]; exact hvx
    · exact rd _ _ k hk
  have ewd : ∀ k, wdrOf b k = wdrOf t k := fun k => by
    by_cases hk : k = sizeOf t
    · subst hk; unfold wdrOf; rw [gv, if_pos rfl, tnone]; exact hvw
    · exact rd _ _ k hk
  have esl : ∀ k, k ≠ sizeOf t → slashedOf b k = slashedOf t k := fun k hk => by
    unfold slashedOf; rw [gv k, if_neg hk]
  have sln : slashedOf b (sizeOf t) = false := by unfold slashedOf; rw [gv, if_pos rfl]; exact hvs
  have ebn : ebN b (sizeOf t) = v.effectiveBalance.toNat := rs _ 0
  have mxn : maxN b (sizeOf t) = (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat := rs _ 0
  have balb : balN b (sizeOf t) = x.toNat := by unfold balN; rw [gb, if_pos rfl]; rfl
  have capt : capN t (sizeOf t) = 0 := by unfold capN maxN; rw [tnone]; exact Nat.min_zero _
  have capb : capN b (sizeOf t) ≤ x.toNat := by unfold capN; rw [balb]; exact Nat.min_le_left _ _
  have hbsz : sizeOf b = sizeOf t + 1 := by
    show b.validators.val.size = _; rw [hv, Array.size_push]; rfl
  have e10 : exitedCount b = exitedCount t := by
    unfold exitedCount
    rw [hbsz, List.range_succ, List.filter_append, List.length_append]
    have hfar : exitOf b (sizeOf t) = farN := by rw [eex]; unfold exitOf; rw [tnone]
    have : (List.filter (fun i => decide (exitOf b i ≠ farN)) [sizeOf t]).length = 0 := by
      simp [hfar]
    rw [this, Nat.add_zero]
    simp only [eex]
  have hV : ∀ i, V i ≤ stepV V t b i := fun i => Nat.le_add_right _ _
  have hn₀ : sizeOf st₀ ≤ sizeOf t := I.sizeLe
  -- The move: only the new index moves, by at most its balance.
  have hmove : moveN vals st₀ E t b ≤ x.toNat := by
    unfold moveN
    refine sum_le_of_single _ (sizeOf t) _ _ (hnd.filter _) (fun i _ hij => ?_) (fun i _ => ?_)
    · rw [ecap _ hij, absDiff_self]
    · by_cases hi : i.toNat = sizeOf t
      · rw [hi, capt, absDiff_zero_right]; exact capb
      · rw [ecap _ hi, absDiff_self]; exact Nat.zero_le _
  -- The potentials do not grow.
  have hphi : phi vals E b ≤ phi vals E t := by
    have hg : gSl vals b ≤ gSl vals t := by
      unfold gSl
      refine sum_le_sum (fun i => ?_) vals
      dsimp only
      by_cases hi : i.toNat = sizeOf t
      · rw [if_pos (by omega : i.toNat < sizeOf b), if_neg (by omega : ¬ i.toNat < sizeOf t), hi, sln,
          mxn]
        simp only [Bool.false_eq_true, if_false]
        exact slashCost_mono (C.maxLe v)
      · by_cases hlt : i.toNat < sizeOf t
        · rw [if_pos (by omega : i.toNat < sizeOf b), if_pos hlt, esl _ hi, emx _ hi]
          exact Nat.le_refl _
        · rw [if_neg (by omega : ¬ i.toNat < sizeOf b), if_neg hlt]
          exact Nat.le_refl _
    have hc : gCons E b = gCons E t := by unfold gCons; rw [hq1]; simp only [ewd]
    unfold phi gPart
    rw [hc, hq2, hdb]
    omega
  refine ⟨fun i hi hl => ?_, ?_, fun i hi hl => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_,
    fun i hi h1 h2 h3 => ?_, by rw [hx1, hx2]; exact I.churnX.of_exit_eq eex,
    by rw [hc1, hc2]; exact I.churnC.of_exit_eq eex, ?_, fun i hi hl hs => ?_,
    by rw [hbsz]; omega, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => ?_⟩
  · have := absDiff_triangle (capN b i.toNat) (capN t i.toNat) (capN st₀ i.toNat)
    have := I.cap i hi hl
    unfold stepV
    rw [absDiff_comm (capN b i.toNat) (capN t i.toNat)] at *
    omega
  · rw [sum_stepV]
    have := I.bud
    omega
  · by_cases hin : i.toNat = sizeOf t
    · -- The new validator: `st₀` has no validator there.
      have h0 : st₀.validators.val[i.toNat]? = none := Array.getElem?_eq_none (by
        show sizeOf st₀ ≤ i.toNat; omega)
      have e0 : ebN st₀ i.toNat = 0 := by unfold ebN; rw [h0]
      have p0 : eps0 st₀ i.toNat = 0 := by
        unfold eps0 capN maxN ebN; simp only [h0, Nat.min_zero, absDiff_self]
      rw [e0, p0, hin, ebn]
      have hcap : v.effectiveBalance.toNat ≤ stepV V t b (sizeOf t) := by
        unfold stepV
        rw [capt, absDiff_zero_right]
        have : v.effectiveBalance.toNat ≤ capN b (sizeOf t) := by
          unfold capN; rw [balb, mxn]; exact Nat.le_min.mpr ⟨hvle, hvm⟩
        omega
      rw [← hin] at hcap ⊢
      rcases Nat.eq_zero_or_pos v.effectiveBalance.toNat with hz | hp
      · exact .inl hz
      · refine .inr ⟨?_, ?_⟩
        · have : incN ≤ v.effectiveBalance.toNat := Nat.le_of_dvd hp (Nat.dvd_of_mod_eq_zero hvmul)
          have := C.downLt
          omega
        · rw [absDiff_zero_right]; omega
    · rw [eeb _ hin]; exact (I.track i hi hl).mono (hV _)
  · have hi : i ≠ sizeOf t := by omega
    rw [eact _ hi]; exact I.actOnce i h1 h2
  · rw [eex]; exact I.exitOnce i h1 h2
  · exact Nat.le_trans (I.newExit i hi h1 h2 (by rw [← eex]; exact h3))
      (Nat.add_le_add_left (abound_mono (Nat.add_le_add_left (hV _) _)) _)
  · obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi hx => ?_, fun i hi hs => ?_⟩
    · show b.balances.val.size = b.validators.val.size
      rw [hb, hv, Array.size_push, Array.size_push, s1]
    · by_cases hin : i = sizeOf t
      · subst hin; rw [ebn, mxn]; exact hvm
      · rw [eeb _ hin, emx _ hin]; exact s2 i (by omega)
    · by_cases hin : i = sizeOf t
      · subst hin; rw [ebn]; exact hvmul
      · rw [eeb _ hin]; exact s3 i (by omega)
    · rw [ewd]
      by_cases hin : i = sizeOf t
      · subst hin; unfold wdrOf; rw [tnone]
      · exact s4 i (by omega) (by rw [← eex]; exact hx)
    · by_cases hin : i = sizeOf t
      · subst hin; rw [sln] at hs; cases hs
      · rw [eex]; exact s5 i (by omega) (by rw [← esl _ hin]; exact hs)
  · rw [ewd]
    by_cases hin : i.toNat = sizeOf t
    · rw [hin]; unfold wdrOf; rw [tnone]; exact hE
    · exact I.live i hi hl (by omega)
  · have hin : i ≠ sizeOf t := fun e => by subst e; rw [sln] at hs; cases hs
    rw [ewd]
    exact I.slashInv i (by omega) (by rw [← esl _ hin]; exact hs)

omit [HasherTag] in
/-- The facts of a validator from a deposit that `RunInv.addValidator` needs. -/
theorem getValidatorFromDeposit_facts (C : DriftConsts) (pk : EthCLSpecs.Heze.BLSPubkey)
    (wc : EthCLSpecs.Heze.Bytes32) (x : Gwei) :
    let v := EthCLSpecs.Heze.getValidatorFromDeposit pk wc x
    v.exitEpoch.toNat = farN ∧ v.withdrawableEpoch.toNat = farN ∧ v.slashed = false ∧
      v.effectiveBalance.toNat ≤ x.toNat ∧
      v.effectiveBalance.toNat ≤ (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat ∧
      v.effectiveBalance.toNat % incN = 0 := by
  intro v
  have hmod : x % EthCLSpecs.Heze.Const.effectiveBalanceIncrementG ≤ x := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; exact Nat.mod_le _ _
  have hsub : (x - x % EthCLSpecs.Heze.Const.effectiveBalanceIncrementG).toNat =
      x.toNat - x.toNat % incN := by
    rw [UInt64.toNat_sub_of_le _ _ hmod, UInt64.toNat_mod]; rfl
  have heb : v.effectiveBalance.toNat = min (x.toNat - x.toNat % incN)
      (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat := by
    show (umin _ _).toNat = _
    rw [umin_toNat, hsub]
    rfl
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [heb]; exact Nat.le_trans (Nat.min_le_left _ _) (Nat.sub_le _ _)
  · rw [heb]; exact Nat.min_le_right _ _
  · rw [heb]
    rcases Nat.le_total (x.toNat - x.toNat % incN) (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat
      with hle | hle
    · rw [Nat.min_eq_left hle]
      have := Nat.div_add_mod x.toNat incN
      have e : x.toNat - x.toNat % incN = incN * (x.toNat / incN) := by omega
      rw [e, Nat.mul_mod_right]
    · rw [Nat.min_eq_right hle]; exact C.maxMul v

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **One applied deposit keeps the invariant**, at the cost of its amount, or at no cost when
it tops up a validator that is withdrawable by `E + 1`. -/
theorem RunInv.applyPendingDeposit {vals : List ValidatorIndex} {st₀ t b : BeaconState}
    {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat} (C : DriftConsts)
    (hnd : vals.Nodup) (I : RunInv vals st₀ E CX CC t V W tag Γp B) (hE : E + 1 < farN)
    (h64 : sizeOf t < 2 ^ 64) (d : EthCLSpecs.Heze.PendingDeposit) (c : Nat)
    (hc : d.amount.toNat ≤ c ∨ ∃ vi, EthCLSpecs.Heze.validatorIndexByPubkey? (pureState t) d.pubkey
      = some vi ∧ wdrOf t vi ≤ E + 1)
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run (pureState t)
      = .ok ((), pureState b)) :
    depView b = depView t ∧ sizeOf b ≤ sizeOf t + 1 ∧
      ∃ V', RunInv vals st₀ E CX CC b V' W tag Γp (B + c) := by
  unfold EthCLSpecs.Heze.applyPendingDeposit at h
  have h := run_get_bind_eq_ok _ _ _ h
  try dsimp only at h
  split at h
  · rename_i vi hvi
    have hlt := validatorIndexByPubkey?_lt hvi
    obtain ⟨x, s1, h1, h⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
    have e := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h
    obtain ⟨-, hm, hx, hxs⟩ := moveN_increaseBalance vals hnd st₀ E t _ _ _ h1
    have hb : b = x := pureState_inj e
    subst hb
    have hv : b.validators = t.validators := by rw [hx]
    refine ⟨by rw [hx]; rfl, by unfold sizeOf; rw [hv]; omega, ?_⟩
    rcases hc with hc | ⟨vi', hvi', hw⟩
    · exact ⟨_, I.balanceStep (by rw [hx]) hxs (Nat.le_trans hm hc)⟩
    · rw [hvi] at hvi'
      injection hvi' with hvi'
      subst hvi'
      have hd64 : (UInt64.ofNat vi).toNat = vi := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by unfold sizeOf at h64; omega)
      have hcb := countedB_false_of_wdr I vi hlt hw
      have hm0 : moveN vals st₀ E t b = 0 := by
        obtain ⟨-, y, ey, -⟩ := increaseBalance_run_ok t _ _ _ h1
        rw [ey, hd64]
        exact moveN_set_uncounted vals st₀ E t vi y hcb
      exact ⟨_, I.balanceStep (by rw [hx]) hxs (by rw [hm0]; exact Nat.zero_le _)⟩
  · rename_i hnone
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨⟨hlt, hv⟩, ⟨hlt', hb⟩, hd⟩ := addValidatorToRegistry_run _ _ _ t b I.shape.sizes h
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := getValidatorFromDeposit_facts C d.pubkey
        d.withdrawalCredentials d.amount
      have hc' : d.amount.toNat ≤ c := by
        rcases hc with hc | ⟨vi, hvi, -⟩
        · exact hc
        · rw [hnone] at hvi; cases hvi
      have hbs : sizeOf b ≤ sizeOf t + 1 := by
        show b.validators.val.size ≤ _
        rw [hv, SizzLean.Proofs.sszListPush_val, Array.size_push]; exact Nat.le_refl _
      exact ⟨hd, hbs, _, (I.addValidator C hnd _ _ (by rw [hv]; rfl) (by rw [hb]; rfl) hd hE
        f1 f2 f3 f4 f5 f6).mono_B (Nat.add_le_add_left hc' _)⟩
    · have e := run_pure_state_eq _ _ _ _ h
      have hb := pureState_inj e
      subst hb
      exact ⟨rfl, Nat.le_succ _, V, I.mono_B (Nat.le_add_right _ _)⟩

omit [Config] [CryptoBackend] in
/-- **A write of the deposit queue and the deposit churn keeps the invariant**, when the
budget covers the new churn. -/
theorem RunInv.dbcStep {vals : List ValidatorIndex} {st₀ t : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B₁ B₂ : Nat}
    (I : RunInv vals st₀ E CX CC t V W tag Γp B₁)
    (q : SizzLean.Repr.SSZList EthCLSpecs.Heze.PendingDeposit EthCLSpecs.Heze.Const.pendingDepositsLimit)
    (x : Gwei) (hc : B₁ + x.toNat ≤ B₂ + t.depositBalanceToConsume.toNat) :
    RunInv vals st₀ E CX CC { t with pendingDeposits := q, depositBalanceToConsume := x }
      V W tag Γp B₂ := by
  have J := I.transferLe (b := { t with pendingDeposits := q, depositBalanceToConsume := x })
    (c := x.toNat) (fun _ => rfl)
    (by show x.toNat + gCons E t + gSl vals t + gPart E t ≤ phi vals E t + x.toNat
        unfold phi; omega)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => Nat.le_refl _) rfl rfl rfl rfl rfl rfl
  refine { J with bud := ?_ }
  have := I.bud
  have hp : phi vals E { t with pendingDeposits := q, depositBalanceToConsume := x } +
      t.depositBalanceToConsume.toNat = phi vals E t + x.toNat := by
    show x.toNat + gCons E t + gSl vals t + gPart E t + t.depositBalanceToConsume.toNat = _
    unfold phi; omega
  omega

/-- The bound of the activation churn of one epoch. -/
def churnA : Nat := EthCLSpecs.Heze.Const.maxPerEpochActivationChurnLimitGloas.toNat

omit [CryptoBackend] in
/-- A successful read of the activation churn limit is at most `churnA`. -/
theorem activationChurn_le (a : BeaconState) {c : Gwei}
    (h : EthCLSpecs.Heze.getActivationChurnLimit (pureState a) = .ok c) : c.toNat ≤ churnA := by
  unfold EthCLSpecs.Heze.getActivationChurnLimit at h
  obtain ⟨tot, htot, h⟩ := except_bind_eq_ok h
  have e := except_pure_ok h
  subst e
  unfold churnA
  rw [umin_toNat]
  exact Nat.min_le_left _ _

/-- **The pending deposits keep the invariant, at the cost `churnA`.** The deposits that
consume churn move the balances by at most the churn of the epoch plus the deposit churn
carried over, and the carry-over that stays is paid back to the potential. A deposit to a
validator that is withdrawable by the next epoch moves no counted balance. -/
theorem RunInv.processPendingDeposits (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    {a b : BeaconState} (C : DriftConsts) (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (hE : epochN a ≤ E) (hEf : E + 1 < farN) (h62 : epochN a < 2 ^ 62)
    (hav : a.depositBalanceToConsume.toNat + churnA < 2 ^ 63)
    (hamt : ∀ i : Nat,
      (a.pendingDeposits.toArray[i]! : EthCLSpecs.Heze.PendingDeposit).amount.toNat < 2 ^ 63)
    (hsz : sizeOf a + a.pendingDeposits.toArray.size < 2 ^ 64)
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState a) = .ok ((), pureState b)) :
    ∃ V', RunInv vals st₀ E CX CC b V' W tag Γp (B + churnA) := by
  unfold EthCLSpecs.Heze.processPendingDeposits at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  -- The churn read, the checked sum of the churn available, and the checked start slot of the
  -- finalized epoch keep the state.
  obtain ⟨churn, s0, hch0, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hch, rfl⟩ := liftErr_run_ok_spec hch0
  obtain ⟨av, s0, hav0, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok hav0
  obtain ⟨fs, s0, hfs, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := liftErr_run_ok_spec hfs
  obtain ⟨scan, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_ppdLoop _ _ _ _) h
  unfold EthCLSpecs.Heze.ppdLoop at h1
  -- The churn available to the epoch, without a wrap.
  have hca := activationChurn_le a hch
  have havN : (a.depositBalanceToConsume + churn).toNat =
      a.depositBalanceToConsume.toNat + churn.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  let AV : Gwei := a.depositBalanceToConsume + churn
  let Q : EthCLSpecs.Heze.DepositScan → BeaconState → Prop := fun s t =>
    (∃ V', RunInv vals st₀ E CX CC t V' W tag Γp (B + s.processed.toNat)) ∧
      s.processed.toNat ≤ AV.toNat ∧ depView t = depView a ∧ sizeOf t ≤ sizeOf a + s.ndi
  -- At the end of the scan: some spent churn `p` within the epoch's churn, and `p` at most
  -- the processed amount when the scan stopped on the churn.
  let R : EthCLSpecs.Heze.DepositScan → BeaconState → Prop := fun x t =>
    ∃ p, p ≤ AV.toNat ∧ (∃ V', RunInv vals st₀ E CX CC t V' W tag Γp (B + p)) ∧
      depView t = depView a ∧ (x.churnReached = true → p ≤ x.processed.toNat) ∧
      x.processed.toNat ≤ AV.toNat
  have hcur : (EthCLSpecs.Heze.currentEpochOf (pureState a)).toNat = epochN a := rfl
  have hAV : AV.toNat ≤ a.depositBalanceToConsume.toNat + churnA := by
    show (a.depositBalanceToConsume + _).toNat ≤ _; rw [havN]; omega
  have key := fuelLoop_state_inv Q R {} _
    (fun _ => by keeps_uncached_using [keepsUncached_applyPendingDeposit _]) ?step
    (fun x _ hq => ⟨x.processed.toNat, hq.2.1, hq.1, hq.2.2.1, fun h => (by cases h), Nat.zero_le _⟩)
    _ {} a scan s1
    ⟨⟨V, I.mono_B (Nat.le_add_right _ _)⟩, Nat.zero_le _, rfl, Nat.le_add_right _ _⟩ h1
  case step =>
    intro s t r t' hq hs
    dsimp only at hs
    obtain ⟨⟨V1, I1⟩, hp1, hd1, hs1⟩ := hq
    have hdone : ∀ x : EthCLSpecs.Heze.DepositScan, x.processed = s.processed →
        ∀ (r : Step EthCLSpecs.Heze.DepositScan EthCLSpecs.Heze.DepositScan) (t' : BeaconState),
        (pure (Step.done x) : HezeRun _).run (pureState t) = .ok (r, pureState t') →
        (∀ b', r = .next b' → Q b' t') ∧ (∀ y, r = .done y → R y t') := by
      intro x hx r t' h
      have e1 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
      have e2 := pureState_inj (run_pure_state_eq _ _ _ _ h)
      subst e1 e2
      refine ⟨fun b' hb' => (by cases hb'), fun y hy => ?_⟩
      injection hy with hy
      subst hy
      exact ⟨s.processed.toNat, hp1, ⟨V1, I1⟩, hd1, fun _ => by rw [hx]; exact Nat.le_refl _,
        by rw [hx]; exact hp1⟩
    have hnext : ∀ (x : EthCLSpecs.Heze.DepositScan) (t1 : BeaconState), Q x t1 →
        ∀ (r : Step EthCLSpecs.Heze.DepositScan EthCLSpecs.Heze.DepositScan) (t' : BeaconState),
        (pure (Step.next x) : HezeRun _).run (pureState t1) = .ok (r, pureState t') →
        (∀ b', r = .next b' → Q b' t') ∧ (∀ y, r = .done y → R y t') := by
      intro x t1 hq r t' h
      have e1 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
      have e2 := pureState_inj (run_pure_state_eq _ _ _ _ h)
      subst e1 e2
      refine ⟨fun b' hb' => ?_, fun y hy => (by cases hy)⟩
      injection hb' with hb'
      subst hb'
      exact hq
    rcases run_ite_eq_ok hs with ⟨-, hs⟩ | ⟨hlt, hs⟩
    · exact hdone s rfl _ _ hs
    have hlt' : s.ndi < a.pendingDeposits.toArray.size := by
      simp only [SizzLean.Proofs.view_uncachedBox] at hlt; omega
    have h64 : sizeOf t < 2 ^ 64 := by omega
    obtain ⟨⟨⟩, s2, e2, hs⟩ := run_bind_eq_ok _ _ _ _ hs
    have e2 := run_pure_state_eq _ _ _ _ e2
    subst e2
    have hs := run_get_bind_eq_ok _ _ _ hs
    rcases run_ite_eq_ok hs with ⟨-, hs⟩ | ⟨-, hs⟩
    · exact hdone s rfl _ _ hs
    obtain ⟨⟨⟩, s2, e2, hs⟩ := run_bind_eq_ok _ _ _ _ hs
    have e2 := run_pure_state_eq _ _ _ _ e2
    subst e2
    rcases run_ite_eq_ok hs with ⟨-, hs⟩ | ⟨-, hs⟩
    · exact hdone s rfl _ _ hs
    obtain ⟨⟨⟩, s2, e2, hs⟩ := run_bind_eq_ok _ _ _ _ hs
    have e2 := run_pure_state_eq _ _ _ _ e2
    subst e2
    -- The deposit, and the two flags.
    generalize hd : (pureState a).view.pendingDeposits.toArray[s.ndi]! = d at hs
    have hdamt : d.amount.toNat < 2 ^ 63 := by rw [← hd]; exact hamt _
    -- A deposit applied at the cost `c`.
    have happ : ∀ (c : Nat) (x : EthCLSpecs.Heze.DepositScan), x.ndi = s.ndi + 1 →
        (d.amount.toNat ≤ c ∨ ∃ vi, EthCLSpecs.Heze.validatorIndexByPubkey? (pureState t) d.pubkey
          = some vi ∧ wdrOf t vi ≤ E + 1) → s.processed.toNat + c = x.processed.toNat →
        x.processed.toNat ≤ AV.toNat →
        ∀ (r : Step EthCLSpecs.Heze.DepositScan EthCLSpecs.Heze.DepositScan) (t' : BeaconState),
        (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d >>= fun _ =>
          (pure (Step.next x) : HezeRun _)).run (pureState t) = .ok (r, pureState t') →
        (∀ b', r = .next b' → Q b' t') ∧ (∀ y, r = .done y → R y t') := by
      intro c x hxn hc hxp hxa r t' h
      obtain ⟨⟨⟩, t1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_applyPendingDeposit d) h
      obtain ⟨hd2, hsz2, V2, I2⟩ := I1.applyPendingDeposit C hnd hEf h64 d c hc h1
      refine hnext x t1 ⟨⟨V2, by rw [← hxp, ← Nat.add_assoc]; exact I2⟩, hxa, hd2.trans hd1, ?_⟩ _ _ h
      rw [hxn]; omega
    -- The churn branch: the deposit fits the churn left.
    have hfit : ¬ (s.processed + d.amount >
        (pureState a).view.depositBalanceToConsume + churn) →
        ∀ (r : Step EthCLSpecs.Heze.DepositScan EthCLSpecs.Heze.DepositScan) (t' : BeaconState),
        (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d >>= fun _ =>
          (pure (Step.next { s with ndi := s.ndi + 1, processed := s.processed + d.amount }) :
            HezeRun _)).run (pureState t) = .ok (r, pureState t') →
        (∀ b', r = .next b' → Q b' t') ∧ (∀ y, r = .done y → R y t') := by
      intro hc r t' hs
      have hle : s.processed + d.amount ≤ AV := UInt64.not_lt.mp hc
      have hsum : (s.processed + d.amount).toNat = s.processed.toNat + d.amount.toNat := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [UInt64.le_iff_toNat_le, hsum] at hle
      exact happ d.amount.toNat _ rfl (.inl (Nat.le_refl _)) hsum.symm (by rw [hsum]; exact hle) _ _ hs
    cases hidx : EthCLSpecs.Heze.validatorIndexByPubkey? (pureState t) d.pubkey with
    | none =>
      simp only [hidx, Bool.false_eq_true, if_false] at hs
      obtain ⟨tot, s3, h3, hs⟩ := run_bind_eq_ok _ _ _ _ hs
      obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok h3
      rcases run_ite_eq_ok hs with ⟨hc, hs⟩ | ⟨hc, hs⟩
      · exact hdone { s with churnReached := true } rfl _ _ hs
      · exact hfit hc _ _ hs
    | some vi =>
      simp only [hidx] at hs
      have hvi := validatorIndexByPubkey?_lt hidx
      rcases run_ite_eq_ok hs with ⟨hw, hs⟩ | ⟨-, hs⟩
      · -- A withdrawn validator: no churn.
        have hwd : wdrOf t vi ≤ E + 1 := by
          simp only [SizzLean.Proofs.view_uncachedBox, decide_eq_true_eq] at hw
          rw [sszList_getElem!_eq, getElem!_pos t.validators.val _ hvi] at hw
          unfold wdrOf
          rw [getElem?_pos t.validators.val _ hvi]
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_one, hcur,
            Nat.mod_eq_of_lt (by omega)] at hw
          show (t.validators.val[vi]).withdrawableEpoch.toNat ≤ E + 1
          omega
        exact happ 0 { s with ndi := s.ndi + 1 } rfl (.inr ⟨vi, hidx, hwd⟩) (Nat.add_zero _) hp1 _ _ hs
      rcases run_ite_eq_ok hs with ⟨-, hs⟩ | ⟨-, hs⟩
      · exact hnext { s with ndi := s.ndi + 1, postpone := s.postpone.push d } t
          ⟨⟨V1, I1⟩, hp1, hd1, by show sizeOf t ≤ sizeOf a + (s.ndi + 1); omega⟩ _ _ hs
      obtain ⟨tot, s3, h3, hs⟩ := run_bind_eq_ok _ _ _ _ hs
      obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok h3
      rcases run_ite_eq_ok hs with ⟨hc, hs⟩ | ⟨hc, hs⟩
      · exact hdone { s with churnReached := true } rfl _ _ hs
      · exact hfit hc _ _ hs
  obtain ⟨p, hp, ⟨V', I'⟩, hdt, hcr, hpr⟩ := key
  -- The queue rebuild keeps the state, and the last write sets the queue and the churn.
  obtain ⟨rem, -, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  have e := EthCLLib.Proofs.run_modifyThe_eq_ok h
  have hb := pureState_inj e
  subst hb
  simp only [depView, Prod.mk.injEq] at hdt
  obtain ⟨-, -, -, hdb, -⟩ := hdt
  refine ⟨V', I'.dbcStep _ _ ?_⟩
  have e1 : (pureState a).view.depositBalanceToConsume + churn = AV := rfl
  rw [hdb, e1]
  split
  · rename_i hc
    have := hcr hc
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hpr)]
    omega
  · show B + p + 0 ≤ _
    omega

end

end EthCLSpecs.Proofs.Heze
