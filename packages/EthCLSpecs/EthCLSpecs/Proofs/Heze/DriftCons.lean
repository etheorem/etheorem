import EthCLSpecs.Proofs.Heze.DriftRequests

/-!
# `EthCLSpecs.Proofs.Heze.DriftCons`: a consolidation keeps the invariant

A consolidation request reserves consolidation churn for the effective balance of its source,
sets the exit epoch and the withdrawable epoch of the source, and queues the consolidation.
It is the consolidation-churn analogue of `initiate_validator_exit`
(`RunInv.initiateExit`). The exit enters the consolidation ledger, so the ghost `tag` records
`false`. The queued source becomes withdrawable after `E + 1`, so `gCons` does not count it
(`RunInv.consolidate`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState run_bind_eq_ok run_pure_eq_ok run_get_bind_eq_ok run_ite_eq_ok
  run_pure_state_eq)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei modifyState)
open SizzLean.Proofs (sszListPush_val)

section
variable [Preset] [HasherTag] [Config]

/-- The state after `computeConsolidationEpochAndUpdateChurn bal`, which reserved the epoch `x`
and the consumed total `c`. -/
def afterConsChurn (a : BeaconState) (bal : Gwei) (x : EthCLSpecs.Heze.Epoch) (c : Gwei) :
    BeaconState :=
  { a with consolidationBalanceToConsume := c - bal, earliestConsolidationEpoch := x }

/-- The run of `computeConsolidationEpochAndUpdateChurn` on a plain state. A successful run
computed the activation epoch `act`, read the consolidation churn limit `consChurn a`, and
reserved the pair `(x, c)`, and it wrote that pair. -/
theorem computeConsolidationEpochAndUpdateChurn_run (bal : Gwei) (a : BeaconState)
    {x : EthCLSpecs.Heze.Epoch} {s' : BeaconState}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      bal).run (pureState a) = .ok (x, pureState s')) :
    ∃ act c : UInt64,
      (EthCLSpecs.Heze.computeActivationExitEpoch (EthCLSpecs.Heze.currentEpochOf (pureState a))
        : Except StateTransitionError UInt64) = .ok act ∧
      EthCLSpecs.Heze.getConsolidationChurnLimit (pureState a) = .ok (consChurn a) ∧
      (EthCLSpecs.Heze.reserveChurn bal
        (if a.earliestConsolidationEpoch < umax a.earliestConsolidationEpoch act
          then consChurn a else a.consolidationBalanceToConsume)
        (consChurn a)
        (umax a.earliestConsolidationEpoch act) : Except StateTransitionError _) = .ok (x, c) ∧
      s' = afterConsChurn a bal x c := by
  cases hact : (EthCLSpecs.Heze.computeActivationExitEpoch
      (EthCLSpecs.Heze.currentEpochOf (pureState a)) : Except StateTransitionError UInt64) with
  | error err =>
    rw [computeConsolidationEpochAndUpdateChurn_run_activation_error a bal err hact] at h
    cases h
  | ok act =>
    cases hch : EthCLSpecs.Heze.getConsolidationChurnLimit (pureState a) with
    | error err =>
      rw [computeConsolidationEpochAndUpdateChurn_run_churn_error a bal act err hact hch] at h
      cases h
    | ok churn =>
      have ec : consChurn a = churn := by
        unfold consChurn
        rw [hch]
      rw [ec]
      cases hres : (EthCLSpecs.Heze.reserveChurn bal
          (if a.earliestConsolidationEpoch < umax a.earliestConsolidationEpoch act
            then churn else a.consolidationBalanceToConsume)
          churn
          (umax a.earliestConsolidationEpoch act) : Except StateTransitionError _) with
      | error err =>
        rw [computeConsolidationEpochAndUpdateChurn_run_reserve_error a bal act churn err hact hch
          hres] at h
        cases h
      | ok p =>
        obtain ⟨ep, c⟩ := p
        rw [computeConsolidationEpochAndUpdateChurn_run_ok a bal act churn ep c hact hch hres]
          at h
        injection h with h
        injection h with h1 h2
        subst h1
        exact ⟨act, c, by first | exact hact | rfl, rfl, by first | exact hres | rfl,
          (EthCLLib.Proofs.pureState_inj h2).symm⟩

omit [Config] in
/-- The `uint64` epoch arithmetic of the restart epoch of the consolidation ledger. A successful
`compute_activation_exit_epoch` returns the sum `epoch + 1 + MAX_SEED_LOOKAHEAD`
(`computeActivationExitEpoch_eq`). -/
theorem earliestCons_toNat (a : BeaconState) {act : UInt64}
    (hact : (EthCLSpecs.Heze.computeActivationExitEpoch
      (EthCLSpecs.Heze.currentEpochOf (pureState a)) : Except StateTransitionError UInt64) = .ok act)
    (h : epochN a + lagN < 2 ^ 64) :
    (umax a.earliestConsolidationEpoch act).toNat =
      max a.earliestConsolidationEpoch.toNat (epochN a + lagN) := by
  rw [umax_toNat]
  congr 1
  rw [computeActivationExitEpoch_eq] at hact
  split at hact
  · cases hact
  split at hact
  · cases hact
  injection hact with hact
  subst hact
  have hc : (EthCLSpecs.Heze.currentEpochOf (pureState a)).toNat = epochN a := rfl
  unfold lagN at h ⊢
  rw [UInt64.toNat_add, UInt64.toNat_add, hc, UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- **A consolidation keeps the invariant.** The source `j` had no exit epoch. The state `b`
has the source exit at `x` and become withdrawable at `x + MIN_VALIDATOR_WITHDRAWABILITY_DELAY`,
the consolidation churn reserved for its effective balance, and the consolidation `q` of `j`
queued. The ghost `W` records the effective balance, and `tag` records the consolidation
churn. -/
theorem RunInv.consolidate {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀)
    (j : Nat) (v : Validator) (hv : a.validators.val[j]? = some v)
    (hfar : v.exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch) (act : UInt64)
    (x : EthCLSpecs.Heze.Epoch) (c : Gwei)
    (hactE : (EthCLSpecs.Heze.computeActivationExitEpoch
      (EthCLSpecs.Heze.currentEpochOf (pureState a)) : Except StateTransitionError UInt64) = .ok act)
    (hres : (EthCLSpecs.Heze.reserveChurn v.effectiveBalance
        (if a.earliestConsolidationEpoch < umax a.earliestConsolidationEpoch act
          then consChurn a
          else a.consolidationBalanceToConsume)
        (consChurn a)
        (umax a.earliestConsolidationEpoch act) : Except StateTransitionError _) = .ok (x, c))
    (q : EthCLSpecs.Heze.PendingConsolidation) (hq : q.sourceIndex.toNat = j)
    (hbval : ∀ k, b.validators.val[k]? = if j = k then
      some (exitVal v x EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay)
      else a.validators.val[k]?)
    (hbsz : b.validators.val.size = a.validators.val.size) (hbbal : b.balances = a.balances)
    (hbsl : b.slot = a.slot)
    (hbpc : b.pendingConsolidations.val.toList = a.pendingConsolidations.val.toList ++ [q])
    (hbppw : b.pendingPartialWithdrawals = a.pendingPartialWithdrawals)
    (hbdbc : b.depositBalanceToConsume = a.depositBalanceToConsume)
    (hbx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hbx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hbc1 : b.consolidationBalanceToConsume =
      (afterConsChurn a v.effectiveBalance x c).consolidationBalanceToConsume)
    (hbc2 : b.earliestConsolidationEpoch = x)
    (hCl : EthCLSpecs.Heze.Const.minActivationBalance.toNat ≤
      (consChurn a).toNat)
    (hCu : (consChurn a).toNat ≤ CC)
    (hmin : 0 < EthCLSpecs.Heze.Const.minActivationBalance.toNat)
    (hcur : epochN st₀ ≤ epochN a) (hcurE : epochN a ≤ E)
    (hkE : E < epochN st₀ + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat)
    (hsmall : max st₀.earliestConsolidationEpoch.toNat (E + lagN) + (exitedCount a + 1) * maddC
      < 2 ^ 62)
    (hc62 : max st₀.consolidationBalanceToConsume.toNat CC < 2 ^ 62)
    (hmax : ∀ k, k < sizeOf a → maxN a k ≤ maxEBN) (hmax62 : maxEBN < 2 ^ 62)
    (hd62 : EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 62) :
    AcKeep a b ∧ ∃ W' tag', RunInv vals st₀ E CX CC b V W' tag' Γp B := by
  have hjs : j < sizeOf a := (Array.getElem?_eq_some_iff.mp hv).1
  generalize hC : (consChurn a).toNat = C at hCl hCu
  let v' : Validator := exitVal v x EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay
  have w : OneWrite a b j v v' := ⟨hjs, hbval, hv, hbbal, hbsz⟩
  -- The reads that the write keeps.
  have hmx : ∀ k, maxN b k = maxN a k := fun k =>
    w.read (fun u => (EthCLSpecs.Heze.getMaxEffectiveBalance u).toNat) 0 rfl k
  have hcap : ∀ k, capN b k = capN a k := fun k => by
    unfold capN balN
    rw [w.bal, hmx]
  have heb : ∀ k, ebN b k = ebN a k := fun k => w.read (fun u => u.effectiveBalance.toNat) 0 rfl k
  have hact : ∀ k, actOf b k = actOf a k := fun k =>
    w.read (fun u => u.activationEpoch.toNat) 0 rfl k
  have hsl : ∀ k, slashedOf b k = slashedOf a k := fun k => by
    unfold slashedOf
    rw [w.get k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, w.old]; rfl
    · rw [if_neg hk]
  have hexit_ne : ∀ k, k ≠ j → exitOf b k = exitOf a k := fun k hk =>
    w.read_ne (fun u => u.exitEpoch.toNat) _ k hk
  have hwdr_ne : ∀ k, k ≠ j → wdrOf b k = wdrOf a k := fun k hk =>
    w.read_ne (fun u => u.withdrawableEpoch.toNat) _ k hk
  have hexit_j : exitOf b j = x.toNat := w.read_self (fun u => u.exitEpoch.toNat) _
  have hexit_a : exitOf a j = farN := by
    unfold exitOf; rw [hv]; simp only [hfar]; rfl
  -- The reservation on `Nat`.
  have hbal : v.effectiveBalance.toNat = ebN a j := by unfold ebN; rw [hv]
  have hbalm : ebN a j ≤ maxEBN := Nat.le_trans (I.shape.ebLe j hjs) (hmax j hjs)
  have hcee := I.ceeLe
  have hmaxE := Nat.le_max_right st₀.earliestConsolidationEpoch.toNat (E + lagN)
  have hcurlag : epochN a + lagN < 2 ^ 62 := by omega
  have hcee62 : a.earliestConsolidationEpoch.toNat < 2 ^ 62 := by
    have : exitedCount a * maddC ≤ (exitedCount a + 1) * maddC :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  have hearl := earliestCons_toNat a hactE (by omega)
  have hcbcle : a.consolidationBalanceToConsume.toNat ≤
      max st₀.consolidationBalanceToConsume.toNat CC := I.churnC.ebcLe
  have hC62 : C < 2 ^ 62 := by
    have := Nat.le_max_right st₀.consolidationBalanceToConsume.toNat CC; omega
  have hcons : (if a.earliestConsolidationEpoch < umax a.earliestConsolidationEpoch act
      then consChurn a
      else a.consolidationBalanceToConsume).toNat =
      if a.earliestConsolidationEpoch.toNat <
          max a.earliestConsolidationEpoch.toNat (epochN a + lagN) then C
      else a.consolidationBalanceToConsume.toNat := by
    by_cases hlt : a.earliestConsolidationEpoch.toNat <
        max a.earliestConsolidationEpoch.toNat (epochN a + lagN)
    · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hearl]; exact hlt), if_pos hlt, hC]
    · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hearl]; exact hlt), if_neg hlt]
  obtain ⟨hx1, hx2⟩ := reserveChurn_toNat v.effectiveBalance _ _ _ (by omega)
    (by rw [hcons]; split <;> omega) (by rw [hC]; omega) (by rw [hC]; exact hC62)
    (by rw [hearl]; omega) hres
  rw [hcons, hearl, hC, hbal] at hx1
  rw [hcons, hC, hbal] at hx2
  have hxN : x.toNat = resEpoch lagN a.earliestConsolidationEpoch.toNat
      a.consolidationBalanceToConsume.toNat (epochN a) C (ebN a j) := by
    rw [hx1]; rfl
  have htot : c.toNat =
      resTotal lagN a.earliestConsolidationEpoch.toNat a.consolidationBalanceToConsume.toNat
        (epochN a) C (ebN a j) := by
    rw [hx2]; rfl
  -- The ghosts after the consolidation.
  let W' : Nat → Nat := fupd W j (ebN a j)
  let tag' : Nat → Bool := fupd tag j false
  have hW : ∀ k, k ≠ j → W' k = W k := fun k hk => fupd_ne _ _ hk
  have htag : ∀ k, k ≠ j → tag' k = tag k := fun k hk => fupd_ne _ _ hk
  have hWj : W' j = ebN a j := fupd_self _ _ _
  have htagj : tag' j = false := fupd_self _ _ _
  -- The exits that the consolidation churn paid for grow by at most this exit.
  have hS : churnSum vals st₀ b W' tag' false farN ≤
      churnSum vals st₀ a W tag false farN + ebN a j := by
    unfold churnSum
    rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
    refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
    · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
    · rw [hk, hexit_a, hWj]
      split <;> simp
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ledger_step (e₀ := epochN st₀)
    (ee₀ := st₀.earliestConsolidationEpoch.toNat) (ebc₀ := st₀.consolidationBalanceToConsume.toNat)
    (Cmax := CC) hcur (by omega) hCu I.churnC.mono I.churnC.held hS
  have hcbc' : b.consolidationBalanceToConsume.toNat = resTotal lagN
      a.earliestConsolidationEpoch.toNat a.consolidationBalanceToConsume.toNat (epochN a) C
        (ebN a j) - ebN a j := by
    rw [hbc1]
    show (c - v.effectiveBalance).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [htot, hbal]; exact hl4)),
      htot, hbal]
  have hxge : epochN a + lagN ≤ x.toNat := by rw [hxN]; exact hl3
  have hxle : x.toNat ≤ max a.earliestConsolidationEpoch.toNat (epochN a + lagN) +
      (ebN a j / C + 1) := by
    rw [hxN]; exact resEpoch_le _ _ _ _ _
  have hdiv : ebN a j / C ≤ maxEBN / EthCLSpecs.Heze.Const.minActivationBalance.toNat :=
    Nat.le_trans (Nat.div_le_div_right hbalm) (Nat.div_le_div_left hCl hmin)
  have hx62 : x.toNat < 2 ^ 62 := by
    have h3 : (exitedCount a + 1) * maddC = exitedCount a * maddC + maddC := Nat.succ_mul _ _
    have h4 : maddC = maxEBN / EthCLSpecs.Heze.Const.minActivationBalance.toNat + 1 := rfl
    omega
  have hwdr_j : wdrOf b j = x.toNat + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat := by
    rw [show wdrOf b j = (x + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay).toNat from
      w.read_self (fun u => u.withdrawableEpoch.toNat) _, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hlag1 : 1 ≤ lagN := by unfold lagN; omega
  have hxlive : E + 1 < x.toNat + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat := by
    omega
  have hfarN : farN = 2 ^ 64 - 1 := rfl
  have hwdr_a : wdrOf a j = farN := I.shape.exitFar j hjs hexit_a
  -- The potentials stay: the new consolidation and the source lie after `E + 1`.
  have hphi : phi vals E b = phi vals E a := by
    have hg : gSl vals b = gSl vals a := by
      unfold gSl
      rw [w.size]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      rw [hsl, hmx]
    have hc : gCons E b = gCons E a := by
      unfold gCons
      rw [hbpc, List.filter_append]
      have hq' : List.filter (fun q => decide (wdrOf b q.sourceIndex.toNat ≤ E + 1)) [q] = [] := by
        simp only [List.filter_cons, List.filter_nil]
        rw [if_neg (by rw [hq, hwdr_j]; simp only [decide_eq_true_eq]; omega)]
      rw [hq', List.append_nil]
      congr 2
      refine List.filter_congr fun q _ => ?_
      by_cases hk : q.sourceIndex.toNat = j
      · rw [hk, hwdr_j, hwdr_a]
        simp only [decide_eq_decide]
        constructor <;> intro _ <;> omega
      · rw [hwdr_ne _ hk]
    unfold phi gPart
    rw [hg, hc, hbppw, hbdbc]
  have hexj_ne : exitOf b j ≠ farN := by rw [hexit_j]; omega
  have hcnt := exitedCount_set a b j hjs w.size hexit_a hexj_ne hexit_ne
  have hkeep : AcKeep a b := w.acKeep hbsl rfl (by
    have hvf : v.exitEpoch.toNat = farN := by rw [hfar]; rfl
    have hcN : (EthCLSpecs.Heze.currentEpochOf (pureState a)).toNat = epochN a := rfl
    rw [Bool.eq_iff_iff, isActive_iff, isActive_iff, hcN, hvf]
    show v.activationEpoch.toNat ≤ epochN a ∧ epochN a < x.toNat ↔ _
    constructor <;> intro hh <;> refine ⟨hh.1, ?_⟩ <;> omega)
  refine ⟨hkeep, W', tag', ⟨fun k hk hl => by rw [hcap]; exact I.cap k hk hl,
    by rw [hphi]; exact I.bud, fun k hk hl => by rw [heb]; exact I.track k hk hl,
    fun k h1 h2 => by rw [hact]; exact I.actOnce k h1 h2, ?exitOnce, ?newExit, ?churnX, ?churnC,
    ?shape, ?live, by rw [w.size]; exact I.sizeLe, ?eeLe, ?ceeLe, ?slashInv⟩⟩
  case slashInv =>
    intro k hk hs
    rw [hsl] at hs
    by_cases hkj : k = j
    · subst hkj
      exact absurd hexit_a (I.shape.slashedExit k hjs hs)
    · rw [hwdr_ne _ hkj]; exact I.slashInv k (by rw [← w.size]; exact hk) hs
  case exitOnce =>
    intro k h1 h2
    by_cases hk : k = j
    · subst hk
      exact absurd ((I.exitOnce _ h1 h2).symm.trans hexit_a) h2
    · rw [hexit_ne _ hk]; exact I.exitOnce k h1 h2
  case newExit =>
    intro k hk h1 h2 h3
    by_cases hkj : k.toNat = j
    · rw [hkj] at h1 h2 ⊢
      have hl : liveB st₀ E j = true := by
        have := hshape₀.exitFar j h1 h2
        unfold liveB
        unfold wdrOf at this
        cases hv0 : st₀.validators.val[j]? with
        | none => rfl
        | some v0 =>
          rw [hv0] at this
          dsimp only at this
          simp only [decide_eq_true_eq]
          have := hfarN
          omega
      have hb := (I.track k hk (by rw [hkj]; exact hl)).bound
      rw [hkj] at hb
      rw [hWj]
      have := le_add_absDiff (ebN st₀ j) (ebN a j)
      rw [absDiff_comm] at this
      unfold abound
      omega
    · rw [hW _ hkj]
      exact I.newExit k hk h1 h2 (by rw [← hexit_ne _ hkj]; exact h3)
  case churnC =>
    refine ⟨by rw [hbc2, hcbc', hxN]; exact hl1, fun k hk j1 j2 j3 j4 => ?_, fun X => ?_,
      by rw [hbc2]; exact Nat.le_trans I.churnC.mono (by rw [hxN]; exact hl2), ?_⟩
    · by_cases hkj : k.toNat = j
      · rw [hkj, hexit_j, hbc2]; exact Nat.le_refl _
      · rw [hexit_ne _ hkj, hbc2]
        rw [htag _ hkj] at j4
        exact Nat.le_trans (I.churnC.le_ee k hk j1 j2 (by rw [← hexit_ne _ hkj]; exact j3) j4)
          (by rw [hxN]; exact hl2)
    · by_cases hX : x.toNat ≤ X
      · have hmono : churnSum vals st₀ b W' tag' false X ≤ churnSum vals st₀ b W' tag' false farN := by
          unfold churnSum
          rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
          refine sum_map_le_sum_map _ _ (fun k => ?_) _
          split
          · rename_i hk
            simp only [decide_eq_true_eq] at hk
            have : exitOf b k.toNat < 2 ^ 64 := by
              unfold exitOf; split
              · exact UInt64.toNat_lt _
              · omega
            rw [if_pos (decide_eq_true ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, by omega⟩)]
            exact Nat.le_refl _
          · exact Nat.zero_le _
        have hlx : (x.toNat - ledgerBase (epochN st₀) st₀.earliestConsolidationEpoch.toNat) * CC ≤
            (X - ledgerBase (epochN st₀) st₀.earliestConsolidationEpoch.toNat) * CC :=
          Nat.mul_le_mul_right _ (by omega)
        rw [← hxN] at hl1
        omega
      · have hle : churnSum vals st₀ b W' tag' false X ≤ churnSum vals st₀ a W tag false X + 0 := by
          unfold churnSum
          rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
          refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
          · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
          · rw [hk, hexit_j, hexit_a]
            simp only [decide_eq_true_eq]
            rw [if_neg (by omega), if_neg (by omega)]
            exact Nat.le_refl _
        have := I.churnC.upTo X
        omega
    · rw [hcbc']
      have := resTotal_sub_le a.earliestConsolidationEpoch.toNat a.consolidationBalanceToConsume.toNat
        (epochN a) C (ebN a j)
      have := I.churnC.ebcLe
      omega
  case churnX =>
    -- The exit ledger reads no exit of this step: the exit carries the consolidation tag.
    have e : ∀ X, churnSum vals st₀ b W' tag' true X = churnSum vals st₀ a W tag true X := by
      intro X
      have h1 : churnSum vals st₀ b W' tag' true X ≤ churnSum vals st₀ a W tag true X + 0 := by
        unfold churnSum
        rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
        refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
        · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
        · rw [hk, htagj]
          simp
      have h2 : churnSum vals st₀ a W tag true X ≤ churnSum vals st₀ b W' tag' true X + 0 := by
        unfold churnSum
        rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
        refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
        · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
        · rw [hk, hexit_a]
          simp
      omega
    obtain ⟨l1, l2, l3, l4, l5⟩ := I.churnX
    refine ⟨by rw [e, hbx1, hbx2]; exact l1, fun k hk j1 j2 j3 j4 => ?_,
      fun X => by rw [e]; exact l3 X, by rw [hbx2]; exact l4, by rw [hbx1]; exact l5⟩
    have hkj : k.toNat ≠ j := fun hkj => by rw [hkj, htagj] at j4; cases j4
    rw [hexit_ne _ hkj, hbx2]
    rw [htag _ hkj] at j4
    exact l2 k hk j1 j2 (by rw [← hexit_ne _ hkj]; exact j3) j4
  case shape =>
    obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    refine ⟨by rw [w.bal, s1]; exact w.size.symm, fun k hk => by rw [heb, hmx]; exact s2 k (by
      rw [← w.size]; exact hk), fun k hk => by rw [heb]; exact s3 k (by rw [← w.size]; exact hk),
      fun k hk hx => ?_, fun k hk hs => ?_⟩
    · by_cases hkj : k = j
      · subst hkj; exact absurd hx hexj_ne
      · rw [hwdr_ne _ hkj]; exact s4 k (by rw [← w.size]; exact hk) (by rw [← hexit_ne _ hkj]; exact hx)
    · by_cases hkj : k = j
      · subst hkj; exact hexj_ne
      · rw [hexit_ne _ hkj]; exact s5 k (by rw [← w.size]; exact hk) (by rw [← hsl]; exact hs)
  case live =>
    intro k hk hl hs
    by_cases hkj : k.toNat = j
    · rw [hkj, hwdr_j]; exact hxlive
    · rw [hwdr_ne _ hkj]; exact I.live k hk hl (by rw [← w.size]; exact hs)
  case eeLe =>
    rw [hbx2, hcnt]
    have := I.eeLe
    have : exitedCount a * maddX ≤ (exitedCount a + 1) * maddX :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  case ceeLe =>
    rw [hbc2, hcnt]
    have h3 : (exitedCount a + 1) * maddC = exitedCount a * maddC + maddC := Nat.succ_mul _ _
    have h4 : maddC = maxEBN / EthCLSpecs.Heze.Const.minActivationBalance.toNat + 1 := rfl
    omega

end

/-! ## Switch to compounding -/

section
variable [Preset] [HasherTag]

/-- `modBalance` on a plain state writes one balance. -/
theorem modBalance_pureState (t : BeaconState) (i : ValidatorIndex) (f : Gwei → Gwei) :
    EthCLSpecs.Heze.modBalance (pureState t) i f =
      pureState { t with balances := t.balances.set! i.toNat (f t.balances[i.toNat]!) } := rfl

/-- A successful append to the queue of deposits writes the longer queue. -/
theorem appendDeposit_run (a b : BeaconState) (d : EthCLSpecs.Heze.PendingDeposit)
    (h : (appendState pendingDeposits d : HezeRun Unit).run (pureState a)
      = .ok ((), pureState b)) :
    ∃ hlt, b = { a with pendingDeposits := a.pendingDeposits.push d hlt } := by
  by_cases hlt : a.pendingDeposits.val.size < EthCLSpecs.Heze.Const.pendingDepositsLimit
  · have hpush : (sszGet (pureState a) pendingDeposits).push? d
        = some (a.pendingDeposits.push d hlt) :=
      SizzLean.Proofs.sszListPush?_of_lt a.pendingDeposits d hlt
    simp only [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe, EthCLLib.Proofs.except_bind_ok,
      hpush, Option.map_some] at h
    injection h with h
    injection h with _ h
    exact ⟨hlt, (congrArg SizzLean.Cache.SSZ.Box.view h).symm⟩
  · have hpush : (sszGet (pureState a) pendingDeposits).push? d = none :=
      SizzLean.Proofs.sszListPush?_of_le a.pendingDeposits d (by omega)
    simp only [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe, EthCLLib.Proofs.except_bind_ok,
      hpush, Option.map_none] at h
    cases h

/-- **A step that keeps the capped balances and every other read, and raises a cap, keeps the
invariant**, at the cost `c` by which the potentials grow. -/
theorem RunInv.transferLe {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B c : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (hcap : ∀ i, capN b i = capN a i) (hphi : phi vals E b ≤ phi vals E a + c)
    (hact : ∀ i, actOf b i = actOf a i) (hexit : ∀ i, exitOf b i = exitOf a i)
    (hwdr : ∀ i, wdrOf b i = wdrOf a i) (hslash : ∀ i, slashedOf b i = slashedOf a i)
    (heb : ∀ i, ebN b i = ebN a i) (hmax : ∀ i, maxN a i ≤ maxN b i)
    (hsize : sizeOf b = sizeOf a) (hbsz : b.balances.val.size = a.balances.val.size)
    (hx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch) :
    RunInv vals st₀ E CX CC b V W tag Γp (B + c) := by
  have e10 := exitedCount_eq hsize hexit
  refine ⟨fun i hi hl => by rw [hcap]; exact I.cap i hi hl, by have := I.bud; omega,
    fun i hi hl => by rw [heb]; exact I.track i hi hl,
    fun i h1 h2 => by rw [hact]; exact I.actOnce i h1 h2,
    fun i h1 h2 => by rw [hexit]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => I.newExit i hi h1 h2 (by rw [← hexit]; exact h3),
    by rw [hx1, hx2]; exact I.churnX.of_exit_eq hexit,
    by rw [hc1, hc2]; exact I.churnC.of_exit_eq hexit, ?_,
    fun i hi hl hs => by rw [hwdr]; exact I.live i hi hl (by rw [← hsize]; exact hs),
    by rw [hsize]; exact I.sizeLe, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [hwdr]; exact I.slashInv i (by rw [← hsize]; exact hi) (by rw [← hslash]; exact hs)⟩
  obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi hx => ?_, fun i hi hs => ?_⟩
  · rw [hbsz, s1]; exact hsize.symm
  · rw [heb]; exact Nat.le_trans (s2 i (by rw [← hsize]; exact hi)) (hmax i)
  · rw [heb]; exact s3 i (by rw [← hsize]; exact hi)
  · rw [hwdr]; exact s4 i (by rw [← hsize]; exact hi) (by rw [← hexit]; exact hx)
  · rw [hexit]; exact s5 i (by rw [← hsize]; exact hi) (by rw [← hslash]; exact hs)

/-- The credentials of a validator after its switch to compounding. -/
def switchVal (v : Validator) : Validator :=
  { v with withdrawalCredentials :=
      v.withdrawalCredentials.set 0 EthCLSpecs.Heze.Const.compoundingWithdrawalPrefix }

/-- The run of `switchToCompoundingValidator` on a plain state: the credentials of `i` turn
compounding, and a balance above `MIN_ACTIVATION_BALANCE` drops to it. -/
theorem switchToCompounding_run (i : ValidatorIndex) (a b : BeaconState)
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState a) = .ok ((), pureState b)) :
    ∃ v, a.validators.val[i.toNat]? = some v ∧
      b.validators = a.validators.set! i.toNat (switchVal v) ∧ b.slot = a.slot ∧
      b.pendingConsolidations = a.pendingConsolidations ∧
      b.pendingPartialWithdrawals = a.pendingPartialWithdrawals ∧
      b.depositBalanceToConsume = a.depositBalanceToConsume ∧
      b.exitBalanceToConsume = a.exitBalanceToConsume ∧
      b.earliestExitEpoch = a.earliestExitEpoch ∧
      b.consolidationBalanceToConsume = a.consolidationBalanceToConsume ∧
      b.earliestConsolidationEpoch = a.earliestConsolidationEpoch ∧
      ((b.balances = a.balances ∧ balN a i.toNat ≤ EthCLSpecs.Heze.Const.minActivationBalance.toNat) ∨
        (EthCLSpecs.Heze.Const.minActivationBalance.toNat < balN a i.toNat ∧
          b.balances = a.balances.set! i.toNat EthCLSpecs.Heze.Const.minActivationBalance)) := by
  unfold EthCLSpecs.Heze.switchToCompoundingValidator at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨v, s1, hv, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hv', rfl⟩ := sszGetIdx_run_ok hv
  simp only [SizzLean.Proofs.view_uncachedBox] at hv'
  refine ⟨v, hv', ?_⟩
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e2 := EthCLLib.Proofs.run_modifyThe_eq_ok h2
  rw [modValidator_pureState] at e2
  subst e2
  have hget : a.validators[i.toNat]! = v := by
    rw [sszList_getElem!_eq, getElem!_pos a.validators.val i.toNat
      (Array.getElem?_eq_some_iff.mp hv').1]
    exact (Array.getElem?_eq_some_iff.mp hv').2
  rw [hget] at h
  -- The queue of the excess balance.
  unfold EthCLSpecs.Heze.queueExcessActiveBalance at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨bal, s3, hbal, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hbal', rfl⟩ := sszGetIdx_run_ok hbal
  simp only [SizzLean.Proofs.view_uncachedBox] at hbal'
  have hbN : balN a i.toNat = bal.toNat := by
    unfold balN
    rw [show a.balances.val[i.toNat]? = some bal from hbal']
    rfl
  rcases run_ite_eq_ok h with ⟨hgt, h⟩ | ⟨hle, h⟩
  · obtain ⟨vv, s4, hvv, h⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨-, rfl⟩ := sszGetIdx_run_ok hvv
    obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e5 := EthCLLib.Proofs.run_modifyThe_eq_ok h5
    rw [modBalance_pureState] at e5
    subst e5
    obtain ⟨_, hb⟩ := appendDeposit_run _ _ _ h
    subst hb
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, .inr ⟨?_, rfl⟩⟩
    rw [hbN]
    exact UInt64.lt_iff_toNat_lt.mp hgt
  · have e := run_pure_state_eq _ _ _ _ h
    have hb := pureState_inj e
    subst hb
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, .inl ⟨rfl, ?_⟩⟩
    rw [hbN]
    exact Nat.le_of_not_lt fun hc => hle (UInt64.lt_iff_toNat_lt.mpr hc)

omit [HasherTag] in
/-- `slashCost` grows with the cap. -/
theorem slashCost_mono {m m' : Nat} (h : m ≤ m') : slashCost m ≤ slashCost m' := by
  unfold slashCost
  exact Nat.add_le_add (Nat.div_le_div_right h) (Nat.div_le_div_right h)

omit [HasherTag] in
/-- A switched validator has compounding credentials. -/
theorem switchVal_compounding (v : Validator) :
    EthCLSpecs.Heze.hasCompoundingWithdrawalCredential (switchVal v) = true := by
  unfold EthCLSpecs.Heze.hasCompoundingWithdrawalCredential EthCLSpecs.Heze.credPrefix switchVal
  simp [vget]

/-- **A switch to compounding keeps the invariant**, at the cost of one slashing at the largest
cap: the cap of the switched validator rises to `MAX_EFFECTIVE_BALANCE_ELECTRA`, and its capped
balance stays. -/
theorem RunInv.switch {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hnd : vals.Nodup) (j : Nat) (v : Validator)
    (hv : a.validators.val[j]? = some v)
    (hnc : EthCLSpecs.Heze.hasCompoundingWithdrawalCredential v = false)
    (hMin : EthCLSpecs.Heze.Const.minActivationBalance.toNat ≤ maxEBN)
    (hbv : b.validators = a.validators.set! j (switchVal v))
    (hq1 : b.pendingConsolidations = a.pendingConsolidations)
    (hq2 : b.pendingPartialWithdrawals = a.pendingPartialWithdrawals)
    (hd : b.depositBalanceToConsume = a.depositBalanceToConsume)
    (hx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch)
    (hbal : (b.balances = a.balances ∧
        balN a j ≤ EthCLSpecs.Heze.Const.minActivationBalance.toNat) ∨
      (EthCLSpecs.Heze.Const.minActivationBalance.toNat < balN a j ∧
        b.balances = a.balances.set! j EthCLSpecs.Heze.Const.minActivationBalance)) :
    RunInv vals st₀ E CX CC b V W tag Γp (B + slashCost maxEBN) := by
  have hjs : j < a.validators.val.size := (Array.getElem?_eq_some_iff.mp hv).1
  have hsz₀ : a.balances.val.size = a.validators.val.size := I.shape.sizes
  have hget : ∀ k, b.validators.val[k]? = if j = k then some (switchVal v) else a.validators.val[k]? :=
    fun k => by rw [hbv]; exact getElem?_validators_set a j k _ hjs
  -- A read that the switch keeps is kept everywhere.
  have hread : ∀ (f : Validator → Nat) (d : Nat), f (switchVal v) = f v → ∀ k : Nat,
      (match b.validators.val[k]? with | some u => f u | none => d) =
        (match a.validators.val[k]? with | some u => f u | none => d) := by
    intro f d hf k
    rw [hget k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, hv]; exact hf
    · rw [if_neg hk]
  have hread_ne : ∀ (f : Validator → Nat) (d : Nat) (k : Nat), k ≠ j →
      (match b.validators.val[k]? with | some u => f u | none => d) =
        (match a.validators.val[k]? with | some u => f u | none => d) := by
    intro f d k hk
    rw [hget k, if_neg (Ne.symm hk)]
  have heb : ∀ k, ebN b k = ebN a k := hread (fun u => u.effectiveBalance.toNat) 0 rfl
  have hact : ∀ k, actOf b k = actOf a k := hread (fun u => u.activationEpoch.toNat) 0 rfl
  have hexit : ∀ k, exitOf b k = exitOf a k := hread (fun u => u.exitEpoch.toNat) _ rfl
  have hwdr : ∀ k, wdrOf b k = wdrOf a k := hread (fun u => u.withdrawableEpoch.toNat) _ rfl
  have hslash : ∀ k, slashedOf b k = slashedOf a k := fun k => by
    unfold slashedOf
    rw [hget k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, hv]; rfl
    · rw [if_neg hk]
  have hsize : sizeOf b = sizeOf a := by
    show b.validators.val.size = a.validators.val.size
    rw [hbv]; exact SizzLean.Proofs.sszListSet!_size _ _ _
  -- The caps: `MIN_ACTIVATION_BALANCE` before, the largest cap after.
  have hmaxa : maxN a j = EthCLSpecs.Heze.Const.minActivationBalance.toNat := by
    unfold maxN EthCLSpecs.Heze.getMaxEffectiveBalance
    rw [hv]; simp only [hnc]; rfl
  have hmaxb : maxN b j = maxEBN := by
    unfold maxN EthCLSpecs.Heze.getMaxEffectiveBalance
    rw [hget j, if_pos rfl]; simp only [switchVal_compounding]; rfl
  have hmax_ne : ∀ k, k ≠ j → maxN b k = maxN a k := fun k hk =>
    hread_ne (fun u => (EthCLSpecs.Heze.getMaxEffectiveBalance u).toNat) 0 k hk
  have hmax : ∀ k, maxN a k ≤ maxN b k := fun k => by
    by_cases hk : k = j
    · subst hk; rw [hmaxa, hmaxb]; exact hMin
    · rw [hmax_ne k hk]; exact Nat.le_refl _
  have hbsz : b.balances.val.size = a.balances.val.size := by
    rcases hbal with ⟨hb, -⟩ | ⟨-, hb⟩
    · rw [hb]
    · rw [hb]; exact SizzLean.Proofs.sszListSet!_size _ _ _
  have hbal_ne : ∀ k, k ≠ j → balN b k = balN a k := fun k hk => by
    rcases hbal with ⟨hb, -⟩ | ⟨-, hb⟩
    · unfold balN; rw [hb]
    · unfold balN; rw [hb]
      show ((a.balances.val.setIfInBounds j _)[k]?.getD 0).toNat = _
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm hk)]
  have hcap : ∀ k, capN b k = capN a k := fun k => by
    unfold capN
    by_cases hk : k = j
    · subst hk
      rw [hmaxa, hmaxb]
      rcases hbal with ⟨hb, hle⟩ | ⟨hlt, hb⟩
      · unfold balN at hle ⊢; rw [hb]; omega
      · have : balN b k = EthCLSpecs.Heze.Const.minActivationBalance.toNat := by
          unfold balN; rw [hb]
          show ((a.balances.val.setIfInBounds k _)[k]?.getD 0).toNat = _
          rw [Array.getElem?_setIfInBounds_self, if_pos (by omega)]
          rfl
        rw [this]; omega
    · rw [hbal_ne k hk, hmax_ne k hk]
  -- The potentials: only the slashing cost of `j` grows.
  have hphi : phi vals E b ≤ phi vals E a + slashCost maxEBN := by
    have hg : gSl vals b ≤ gSl vals a + slashCost maxEBN := by
      unfold gSl
      rw [hsize]
      refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
      · rw [hslash, hmax_ne _ hk]
      · rw [hk, hslash, hmaxb]
        split
        · split <;> omega
        · omega
    have hc : gCons E b = gCons E a := by
      unfold gCons
      rw [hq1]
      simp only [hwdr]
    unfold phi gPart
    rw [hc, hq2, hd]
    omega
  exact I.transferLe hcap hphi hact hexit hwdr hslash heb hmax hsize hbsz hx1 hx2 hc1 hc2

end

end EthCLSpecs.Proofs.Heze
