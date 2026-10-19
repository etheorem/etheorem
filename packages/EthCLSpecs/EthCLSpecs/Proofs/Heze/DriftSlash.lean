import EthCLSpecs.Proofs.Heze.DriftExit
import EthCLSpecs.Proofs.Heze.BalanceMoves

/-!
# `EthCLSpecs.Proofs.Heze.DriftSlash`: a slashing keeps the invariant

`slash_validator` initiates the exit of one validator, marks it slashed, extends its
withdrawable epoch, records its effective balance in the slashings vector, takes the slashing
penalty, and pays the whistleblower reward to the proposer (`slashValidator_run`). The two
balance moves add up to at most `slashCost` of the cap of the validator. The slashing
potential `gSl` drops by that cost, since the validator turns slashed, so the step needs no
new budget (`RunInv.slash`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState run_bind_eq_ok run_pure_eq_ok run_get_bind_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- A validator after its slashing at epoch `ep`. -/
def slashVal (v : Validator) (ep : EthCLSpecs.Heze.Epoch) : Validator :=
  let w := umax v.withdrawableEpoch (ep + UInt64.ofNat EthCLSpecs.Heze.Const.epochsPerSlashingsVector)
  { v with slashed := true, withdrawableEpoch := w }

omit [HasherTag] [Config] [CryptoBackend] in
/-- Two balance writes in a row are one balance write. -/
theorem withBal_trans {x y z : BeaconState} (h1 : x = { y with balances := x.balances })
    (h2 : y = { z with balances := y.balances }) : x = { z with balances := x.balances } := by
  rw [h2] at h1
  exact h1

/-- The run of `slashValidator` on a plain state, in three parts: the exit, the write of the
slashed validator (and of the slashings vector), and two balance moves. The checked product
`whistleblower_reward * PROPOSER_WEIGHT` did not overflow. -/
theorem slashValidator_run (vals : List ValidatorIndex) (hnd : vals.Nodup) (st₀ : BeaconState)
    (E : Nat) (i : ValidatorIndex) (a b : BeaconState)
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState a)
      = .ok ((), pureState b)) :
    ∃ a1, (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
        (pureState a) = .ok ((), pureState a1) ∧
      ∃ v1, a1.validators.val[i.toNat]? = some v1 ∧
      (v1.effectiveBalance / UInt64.ofNat
          EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra).toNat *
        (UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight).toNat < 2 ^ 64 ∧ ∃ sl,
        let a2 : BeaconState := { withValidators a1 (a1.validators.set! i.toNat
          (slashVal v1 (EthCLSpecs.Heze.computeEpochAtSlot a.slot))) with slashings := sl }
        b = { a2 with balances := b.balances } ∧ b.balances.val.size = a2.balances.val.size ∧
        moveN vals st₀ E a2 b ≤
          (v1.effectiveBalance / UInt64.ofNat
            EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra).toNat +
          (v1.effectiveBalance / UInt64.ofNat
            EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra *
            UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight /
            UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat +
          (v1.effectiveBalance / UInt64.ofNat
            EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra -
            v1.effectiveBalance / UInt64.ofNat
            EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra *
            UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight /
            UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat := by
  unfold EthCLSpecs.Heze.slashValidator at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨⟨⟩, a1, h1, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure
    (keepsUncached_initiateValidatorExit i) h
  refine ⟨a1, h1, ?_⟩
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨v1, s, hv, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hv', rfl⟩ := sszGetIdx_run_ok hv
  simp only [SizzLean.Proofs.view_uncachedBox] at hv'
  refine ⟨v1, hv', ?_⟩
  simp only [modValidator_pureState] at h
  simp only [pureState_eq_ofValue, uncached_ofValue_view] at h
  simp only [box_view_uncached, uncached_ofValue_view, uncached_mk_eq] at h
  simp only [← pureState_eq_ofValue] at h
  -- The two checked sums keep the state and return the sums, since they did not overflow.
  obtain ⟨se, s0, hs0, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok hs0
  obtain ⟨sv, s0', hs0', h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok hs0'
  -- The penalty, then the two rewards of the proposer.
  obtain ⟨x1, s1, h1, h⟩ := run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) h
  obtain ⟨-, hm1, hx1, hs1⟩ := moveN_decreaseBalance vals hnd st₀ E _ _ _ _ h1
  obtain ⟨u1, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e2 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h2
  subst e2
  have h := run_get_bind_eq_ok _ _ _ h
  -- The checked product `whistleblower_reward * PROPOSER_WEIGHT` keeps the state.
  obtain ⟨_, s2', hs2', h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, hweq⟩ := checkedMul_run_ok hs2'
  have hwlt := hweq ▸ UInt64.toNat_lt _
  obtain ⟨x2, s3, h3, h⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  obtain ⟨-, hm2, hx2, hs2⟩ := moveN_increaseBalance vals hnd st₀ E _ _ _ _ h3
  obtain ⟨x3, s4, h4, h⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  obtain ⟨-, hm3, hx3, hs3⟩ := moveN_increaseBalance vals hnd st₀ E _ _ _ _ h4
  have e5 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h
  have hb : b = x3 := congrArg SizzLean.Cache.SSZ.Box.view e5
  subst hb
  -- `modValidator` read the validator `v1` at `i`.
  have hget : a1.validators[i.toNat]! = v1 := by
    rw [sszList_getElem!_eq, getElem!_pos a1.validators.val i.toNat
      (Array.getElem?_eq_some_iff.mp hv').1]
    exact (Array.getElem?_eq_some_iff.mp hv').2
  rw [hget] at hx1 hm1
  refine ⟨hwlt, a1.slashings.set! (umodIdx (EthCLSpecs.Heze.computeEpochAtSlot a.slot)
    EthCLSpecs.Heze.Const.epochsPerSlashingsVector) (vget a1.slashings (umodIdx
      (EthCLSpecs.Heze.computeEpochAtSlot a.slot) EthCLSpecs.Heze.Const.epochsPerSlashingsVector) +
        v1.effectiveBalance), ?_⟩
  dsimp only
  refine ⟨withBal_trans (withBal_trans hx3 hx2) hx1, ?_, ?_⟩
  · rw [hs3, hs2]
    exact hs1
  · refine Nat.le_trans (moveN_triangle vals st₀ E _ x1 b) ?_
    refine Nat.le_trans (Nat.add_le_add hm1 (Nat.le_trans (moveN_triangle vals st₀ E x1 x2 b)
      (Nat.add_le_add hm2 hm3))) ?_
    omega

end

/-- A sum over distinct indices that hold `j` once, whose summand drops by `c` at `j` alone. -/
theorem sum_add_single_eq (f g : ValidatorIndex → Nat) (j c : Nat) :
    ∀ l : List ValidatorIndex, l.Nodup → (∃ k ∈ l, k.toNat = j) →
      (∀ k ∈ l, k.toNat ≠ j → f k = g k) → (∀ k ∈ l, k.toNat = j → f k + c = g k) →
      (l.map f).sum + c = (l.map g).sum
  | [], _, ⟨_, hk, _⟩, _, _ => absurd hk List.not_mem_nil
  | x :: l, hnd, ⟨k, hk, hkj⟩, h0, h1 => by
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    by_cases hxj : x.toNat = j
    · have hrest : (l.map f).sum = (l.map g).sum := by
        congr 1
        refine List.map_congr_left fun y hy => h0 y (List.mem_cons_of_mem _ hy) fun hyj => hx ?_
        rw [UInt64.toNat_inj.mp (hxj.trans hyj.symm)]
        exact hy
      have := h1 x List.mem_cons_self hxj
      omega
    · rw [h0 x List.mem_cons_self hxj]
      have hk' : k ∈ l := by
        rcases List.mem_cons.mp hk with rfl | hk
        · exact absurd hkj hxj
        · exact hk
      have := sum_add_single_eq f g j c l hnd' ⟨k, hk', hkj⟩
        (fun k hk => h0 k (List.mem_cons_of_mem _ hk)) (fun k hk => h1 k (List.mem_cons_of_mem _ hk))
      omega

section
variable [Preset] [HasherTag]

omit [HasherTag] in
/-- The balance moves of one slashing are at most `slashCost` of a cap at least the effective
balance. `hmul` states that the checked product `whistleblower_reward * PROPOSER_WEIGHT` did
not overflow in a successful run. -/
theorem slash_amounts_le (C : DriftConsts) (eb : Gwei) (m : Nat) (hm : eb.toNat ≤ m)
    (hmul : (eb / UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra).toNat *
      (UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight).toNat < 2 ^ 64) :
    (eb / UInt64.ofNat EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra).toNat +
      (eb / UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra *
        UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight /
        UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat +
      (eb / UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra -
        eb / UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra *
        UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight /
        UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat ≤ slashCost m := by
  obtain ⟨q1, q2⟩ := C.slashQ
  -- `PROPOSER_WEIGHT` and `WEIGHT_DENOMINATOR` are the literals 8 and 64.
  have q3 : EthCLSpecs.Heze.Const.proposerWeight < 2 ^ 64 := by decide
  have q4 : EthCLSpecs.Heze.Const.weightDenominator < 2 ^ 64 := by decide
  have hpw : EthCLSpecs.Heze.Const.proposerWeight ≤ EthCLSpecs.Heze.Const.weightDenominator := by
    decide
  have e1 : (UInt64.ofNat EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra).toNat =
      EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra := EthCLLib.Proofs.toNat_ofNat_lt64 q1
  have e2 : (UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra).toNat =
      EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra := EthCLLib.Proofs.toNat_ofNat_lt64 q2
  have e3 : (UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight).toNat =
      EthCLSpecs.Heze.Const.proposerWeight := EthCLLib.Proofs.toNat_ofNat_lt64 q3
  have e4 : (UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat =
      EthCLSpecs.Heze.Const.weightDenominator := EthCLLib.Proofs.toNat_ofNat_lt64 q4
  generalize hq : eb.toNat / EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra = q
  have hwb : (eb / UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra).toNat = q := by
    rw [UInt64.toNat_div, e2, hq]
  rw [hwb, e3] at hmul
  have hmul : (eb / UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra *
      UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight).toNat = q * EthCLSpecs.Heze.Const.proposerWeight := by
    rw [UInt64.toNat_mul, hwb, e3]
    exact Nat.mod_eq_of_lt hmul
  have hpr : (eb / UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra *
      UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight /
      UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat =
      q * EthCLSpecs.Heze.Const.proposerWeight / EthCLSpecs.Heze.Const.weightDenominator := by
    rw [UInt64.toNat_div, hmul, e4]
  have hprq : q * EthCLSpecs.Heze.Const.proposerWeight / EthCLSpecs.Heze.Const.weightDenominator ≤ q :=
    Nat.div_le_of_le_mul (Nat.le_trans (Nat.mul_le_mul_left q hpw) (Nat.le_of_eq (Nat.mul_comm q _)))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hpr, hwb]; exact hprq)), hpr, hwb,
    UInt64.toNat_div, e1]
  unfold slashCost
  have h5 : eb.toNat / EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra ≤
      m / EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra := Nat.div_le_div_right hm
  have h6 : q ≤ m / EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra := by
    rw [← hq]; exact Nat.div_le_div_right hm
  omega

/-- **The slash write keeps the invariant**, with the budget lowered by the cost of the
slashing: the slashing potential drops by that cost. -/
theorem RunInv.slashWrite {vals : List ValidatorIndex} {st₀ a1 : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a1 V W tag Γp B) (hnd : vals.Nodup) (j : Nat) (v1 : Validator)
    (hv : a1.validators.val[j]? = some v1) (hjv : UInt64.ofNat j ∈ vals) (hj64 : j < 2 ^ 64)
    (hunsl : v1.slashed = false) (hexv : v1.exitEpoch.toNat ≠ farN) (ep : EthCLSpecs.Heze.Epoch)
    (hep : epochN st₀ ≤ ep.toNat)
    (hep62 : ep.toNat + EthCLSpecs.Heze.Const.epochsPerSlashingsVector < 2 ^ 64)
    (sl : Vector Gwei EthCLSpecs.Heze.Const.epochsPerSlashingsVector) :
    slashCost (maxN a1 j) ≤ B ∧ RunInv vals st₀ E CX CC
      { withValidators a1 (a1.validators.set! j (slashVal v1 ep)) with slashings := sl }
      V W tag Γp (B - slashCost (maxN a1 j)) := by
  generalize hb : ({ withValidators a1 (a1.validators.set! j (slashVal v1 ep)) with slashings := sl }
    : BeaconState) = b
  have hjs : j < sizeOf a1 := (Array.getElem?_eq_some_iff.mp hv).1
  have w : OneWrite a1 b j v1 (slashVal v1 ep) := by
    subst hb
    refine ⟨hjs, fun k => getElem?_validators_set a1 j k _ hjs, hv, rfl, ?_⟩
    show (a1.validators.set! j _).val.size = a1.validators.val.size
    exact SizzLean.Proofs.sszListSet!_size _ _ _
  -- The reads that the write keeps.
  have hmx : ∀ k, maxN b k = maxN a1 k := fun k =>
    w.read (fun u => (EthCLSpecs.Heze.getMaxEffectiveBalance u).toNat) 0 rfl k
  have hcap : ∀ k, capN b k = capN a1 k := fun k => by unfold capN balN; rw [w.bal, hmx]
  have heb : ∀ k, ebN b k = ebN a1 k := fun k => w.read (fun u => u.effectiveBalance.toNat) 0 rfl k
  have hact : ∀ k, actOf b k = actOf a1 k := fun k => w.read (fun u => u.activationEpoch.toNat) 0 rfl k
  have hexit : ∀ k, exitOf b k = exitOf a1 k := fun k => w.read (fun u => u.exitEpoch.toNat) _ rfl k
  have hwdr_ne : ∀ k, k ≠ j → wdrOf b k = wdrOf a1 k := fun k hk =>
    w.read_ne (fun u => u.withdrawableEpoch.toNat) _ k hk
  have hsl_ne : ∀ k, k ≠ j → slashedOf b k = slashedOf a1 k := fun k hk => by
    unfold slashedOf; rw [w.get k, if_neg (Ne.symm hk)]
  have hwdr_j : wdrOf b j = max (wdrOf a1 j) (ep.toNat + EthCLSpecs.Heze.Const.epochsPerSlashingsVector) := by
    have e1 : wdrOf b j = (slashVal v1 ep).withdrawableEpoch.toNat :=
      w.read_self (fun u => u.withdrawableEpoch.toNat) _
    have e2 : wdrOf a1 j = v1.withdrawableEpoch.toNat := by unfold wdrOf; rw [hv]
    rw [e1, e2]
    unfold slashVal
    dsimp only
    rw [umax_toNat, UInt64.toNat_add, Nat.mod_eq_of_lt (by
      rw [UInt64.toNat_ofNat']; have := Nat.mod_le EthCLSpecs.Heze.Const.epochsPerSlashingsVector (2 ^ 64)
      omega), UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hwdr_le : ∀ k, wdrOf a1 k ≤ wdrOf b k := fun k => by
    by_cases hk : k = j
    · subst hk; rw [hwdr_j]; exact Nat.le_max_left _ _
    · rw [hwdr_ne _ hk]; exact Nat.le_refl _
  have hsl_j : slashedOf b j = true := by
    unfold slashedOf; rw [w.get j, if_pos rfl]; rfl
  have hsl_a : slashedOf a1 j = false := by unfold slashedOf; rw [hv]; exact hunsl
  have he10 := exitedCount_eq w.size hexit
  -- The slashing potential drops by the cost of this slashing.
  have hgSl : gSl vals b + slashCost (maxN a1 j) = gSl vals a1 := by
    unfold gSl
    rw [w.size]
    refine sum_add_single_eq _ _ j _ vals hnd ⟨_, hjv, EthCLLib.Proofs.toNat_ofNat_lt64 hj64⟩
      (fun k _ hk => by rw [hsl_ne _ hk, hmx]) (fun k _ hk => ?_)
    rw [hk, hsl_j, hsl_a, hmx, if_pos hjs]
    simp only [↓reduceIte, Bool.false_eq_true, Nat.zero_add]
    rw [if_pos hjs]
  have hgCons : gCons E b ≤ gCons E a1 := by
    unfold gCons
    refine Nat.mul_le_mul_left _ ?_
    rw [show b.pendingConsolidations = a1.pendingConsolidations by rw [← hb]; rfl,
      length_filter_eq_sum, length_filter_eq_sum]
    refine sum_map_le_sum_map _ _ (fun q => ?_) _
    by_cases hq : wdrOf b q.sourceIndex.toNat ≤ E + 1
    · rw [if_pos (decide_eq_true hq), if_pos (decide_eq_true (Nat.le_trans (hwdr_le _) hq))]
      exact Nat.le_refl _
    · rw [if_neg (by simpa using hq)]; exact Nat.zero_le _
  have hphi : phi vals E b + slashCost (maxN a1 j) ≤ phi vals E a1 := by
    unfold phi gPart
    rw [show b.depositBalanceToConsume = a1.depositBalanceToConsume by rw [← hb]; rfl,
      show b.pendingPartialWithdrawals = a1.pendingPartialWithdrawals by rw [← hb]; rfl]
    omega
  have hbud := I.bud
  have ex1 : b.exitBalanceToConsume = a1.exitBalanceToConsume := by rw [← hb]; rfl
  have ex2 : b.earliestExitEpoch = a1.earliestExitEpoch := by rw [← hb]; rfl
  have ec1 : b.consolidationBalanceToConsume = a1.consolidationBalanceToConsume := by rw [← hb]; rfl
  have ec2 : b.earliestConsolidationEpoch = a1.earliestConsolidationEpoch := by rw [← hb]; rfl
  refine ⟨by omega, fun k hk hl => by rw [hcap]; exact I.cap k hk hl, by omega,
    fun k hk hl => by rw [heb]; exact I.track k hk hl, fun k h1 h2 => by rw [hact]; exact I.actOnce k h1 h2,
    fun k h1 h2 => by rw [hexit]; exact I.exitOnce k h1 h2,
    fun k hk h1 h2 h3 => I.newExit k hk h1 h2 (by rw [← hexit]; exact h3),
    by rw [ex1, ex2]; exact I.churnX.of_exit_eq hexit, by rw [ec1, ec2]; exact I.churnC.of_exit_eq hexit,
    ?_, fun k hk hl hs => Nat.lt_of_lt_of_le (I.live k hk hl (by rw [← w.size]; exact hs)) (hwdr_le _),
    by rw [w.size]; exact I.sizeLe, by rw [ex2, he10]; exact I.eeLe, by rw [ec2, he10]; exact I.ceeLe,
    fun k hk hs => ?_⟩
  · obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    refine ⟨by rw [w.bal, s1]; exact w.size.symm, fun k hk => by rw [heb, hmx]; exact s2 k (by
      rw [← w.size]; exact hk), fun k hk => by rw [heb]; exact s3 k (by rw [← w.size]; exact hk),
      fun k hk hx => ?_, fun k hk hs => ?_⟩
    · by_cases hkj : k = j
      · subst hkj
        rw [hexit] at hx
        exact absurd (by unfold exitOf at hx; rw [hv] at hx; exact hx) hexv
      · rw [hwdr_ne _ hkj]; exact s4 k (by rw [← w.size]; exact hk) (by rw [← hexit]; exact hx)
    · rw [hexit]
      by_cases hkj : k = j
      · subst hkj; unfold exitOf; rw [hv]; exact hexv
      · exact s5 k (by rw [← w.size]; exact hk) (by rw [← hsl_ne _ hkj]; exact hs)
  · by_cases hkj : k = j
    · subst hkj
      refine .inr ?_
      rw [hwdr_j]
      have := Nat.le_max_right (wdrOf a1 k) (ep.toNat + EthCLSpecs.Heze.Const.epochsPerSlashingsVector)
      omega
    · rw [hwdr_ne _ hkj]
      exact I.slashInv k (by rw [← w.size]; exact hk) (by rw [← hsl_ne _ hkj]; exact hs)

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **A slashing keeps the invariant**, with the budget it starts with: the slashing potential
pays for its two balance moves. It needs an unslashed validator, as its callers check. -/
theorem RunInv.slash {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat} (C : DriftConsts) (i : ValidatorIndex)
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀)
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState a)
      = .ok ((), pureState b))
    (hunsl : slashedOf a i.toNat = false) (hiv : i ∈ vals)
    (hCl : incN ≤ (exitChurn a).toNat)
    (hCu : (exitChurn a).toNat ≤ CX)
    (hcur : epochN st₀ ≤ epochN a) (hcurE : epochN a ≤ E)
    (hkE : E < epochN st₀ + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat)
    (hsmall : max st₀.earliestExitEpoch.toNat (E + lagN) + (exitedCount a + 1) * maddX +
      Γp * maddP < 2 ^ 62)
    (hc62 : max st₀.exitBalanceToConsume.toNat CX < 2 ^ 62)
    (hep62 : epochN a + EthCLSpecs.Heze.Const.epochsPerSlashingsVector < 2 ^ 64) :
    AcKeep a b ∧ ∃ V' W' tag', RunInv vals st₀ E CX CC b V' W' tag' Γp B := by
  obtain ⟨a1, h1, v1, hv1, hwlt, sl, hb, hsz, hm⟩ := slashValidator_run vals hnd st₀ E i a b h
  have hmaxa : ∀ k, k < sizeOf a → maxN a k ≤ maxEBN := fun k hk => by
    unfold maxN; split
    · exact C.maxLe _
    · exact Nat.zero_le _
  obtain ⟨hk1, W1, tag1, I1⟩ := I.initiateExit i hnd hshape₀ h1 hCl hCu C.incPos hcur hcurE hkE
    hsmall hc62 hmaxa C.maxEB62
  -- The validator after the exit: unslashed, with an exit epoch.
  have hv1f : v1.slashed = false ∧ v1.exitEpoch.toNat ≠ farN := by
    obtain ⟨v, hv, hcase⟩ := initiateValidatorExit_run i a a1 h1
    have hsv : v.slashed = false := by unfold slashedOf at hunsl; rw [hv] at hunsl; exact hunsl
    rcases hcase with ⟨hne, rfl⟩ | ⟨-, _act, x, _c, -, -, -, hno, rfl⟩
    · rw [hv] at hv1
      cases hv1
      refine ⟨hsv, fun he => hne (UInt64.toNat_inj.mp ?_)⟩
      rw [he]; rfl
    · have hj : i.toNat < a.validators.val.size := (Array.getElem?_eq_some_iff.mp hv).1
      dsimp only at hv1
      rw [getElem?_validators_set a _ _ _ hj, if_pos rfl] at hv1
      cases hv1
      refine ⟨hsv, ?_⟩
      show x.toNat ≠ farN
      have : EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat ≥ 1 := by omega
      unfold farN
      omega
  have hi64 : i.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hep : epochN st₀ ≤ (EthCLSpecs.Heze.computeEpochAtSlot a.slot).toNat := hcur
  obtain ⟨hcB, I2⟩ := I1.slashWrite hnd i.toNat v1 hv1 (by rw [UInt64.ofNat_toNat]; exact hiv) hi64
    hv1f.1 hv1f.2 (EthCLSpecs.Heze.computeEpochAtSlot a.slot) hep (by exact hep62) sl
  -- The two balance moves cost at most the slashing.
  have hcost := slash_amounts_le C v1.effectiveBalance (maxN a1 i.toNat)
    (by have := I1.shape.ebLe _ (Array.getElem?_eq_some_iff.mp hv1).1
        unfold ebN maxN at this; rw [hv1] at this; unfold maxN; rw [hv1]; exact this)
    hwlt
  have I3 := I2.balanceStep (b := b) (by rw [hb]) hsz (Nat.le_trans hm hcost)
  rw [Nat.sub_add_cancel hcB] at I3
  -- The slash write keeps the epochs and the effective balance, and the rest moves balances.
  have hj1 : i.toNat < sizeOf a1 := (Array.getElem?_eq_some_iff.mp hv1).1
  have w : OneWrite a1 { withValidators a1 (a1.validators.set! i.toNat
      (slashVal v1 (EthCLSpecs.Heze.computeEpochAtSlot a.slot))) with slashings := sl }
      i.toNat v1 (slashVal v1 (EthCLSpecs.Heze.computeEpochAtSlot a.slot)) := by
    refine ⟨hj1, fun k => getElem?_validators_set a1 _ k _ hj1, hv1, rfl, ?_⟩
    show (a1.validators.set! i.toNat _).val.size = a1.validators.val.size
    exact SizzLean.Proofs.sszListSet!_size _ _ _
  have hk2 := w.acKeep rfl rfl rfl
  have hk3 := AcKeep.of_validators (a := { withValidators a1 (a1.validators.set! i.toNat
      (slashVal v1 (EthCLSpecs.Heze.computeEpochAtSlot a.slot))) with slashings := sl }) (b := b)
    (by rw [hb]) (by rw [hb])
  exact ⟨hk1.trans (hk2.trans hk3), _, W1, tag1, I3⟩

/-- The facts at a state `a` that an exit or a slashing at `a` needs: the bounds of the exit
churn of one epoch, the epoch of `a` within the run, and the bounds that keep the churn
arithmetic below `2 ^ 62`. `NX` bounds the exited count plus one, and `ΓX` bounds `Γp`.
`AcKeep` carries these facts along a block (`StepPre.keep`). -/
structure StepPre (st₀ a : BeaconState) (E CX NX ΓX : Nat) : Prop where
  cl : incN ≤ (exitChurn a).toNat
  cu : (exitChurn a).toNat ≤ CX
  cur : epochN st₀ ≤ epochN a
  curE : epochN a ≤ E
  kE : E < epochN st₀ + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat
  small : max st₀.earliestExitEpoch.toNat (E + lagN) + NX * maddX + ΓX * maddP < 2 ^ 62
  c62 : max st₀.exitBalanceToConsume.toNat CX < 2 ^ 62
  ep62 : epochN a + EthCLSpecs.Heze.Const.epochsPerSlashingsVector < 2 ^ 64
  h64 : a.validators.val.size < 2 ^ 64

omit [CryptoBackend] in
/-- **A step that keeps the reads of the total active balance keeps `StepPre`.** -/
theorem StepPre.keep {st₀ a b : BeaconState} {E CX NX ΓX : Nat} (P : StepPre st₀ a E CX NX ΓX)
    (hk : AcKeep a b) : StepPre st₀ b E CX NX ΓX := by
  have hc := exitChurn_congr hk P.h64
  have he := hk.epoch
  have hs : b.validators.val.size = a.validators.val.size := hk.size
  exact ⟨by rw [hc]; exact P.cl, by rw [hc]; exact P.cu, by rw [he]; exact P.cur,
    by rw [he]; exact P.curE, P.kE, P.small, P.c62, by rw [he]; exact P.ep62,
    by rw [hs]; exact P.h64⟩

omit [CryptoBackend] in
/-- The churn bound of one exit, from the bounds of `StepPre`. -/
theorem StepPre.small_at {st₀ a : BeaconState} {E CX NX ΓX Γp : Nat} (P : StepPre st₀ a E CX NX ΓX)
    (hn : exitedCount a + 1 ≤ NX) (hg : Γp ≤ ΓX) :
    max st₀.earliestExitEpoch.toNat (E + lagN) + (exitedCount a + 1) * maddX +
      Γp * maddP < 2 ^ 62 := by
  have := Nat.mul_le_mul_right maddX hn
  have := Nat.mul_le_mul_right maddP hg
  have := P.small
  omega

/-- `RunInv.initiateExit`, from `StepPre`. -/
theorem RunInv.exitStep {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B NX ΓX : Nat} (C : DriftConsts) (i : ValidatorIndex)
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀)
    (P : StepPre st₀ a E CX NX ΓX) (hn : exitedCount a + 1 ≤ NX) (hg : Γp ≤ ΓX)
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState a) = .ok ((), pureState b)) :
    AcKeep a b ∧ ∃ W' tag', RunInv vals st₀ E CX CC b V W' tag' Γp B :=
  I.initiateExit i hnd hshape₀ h P.cl P.cu C.incPos P.cur P.curE P.kE (P.small_at hn hg) P.c62
    (fun k _ => by unfold maxN; split; exact C.maxLe _; exact Nat.zero_le _) C.maxEB62

/-- `RunInv.slash`, from `StepPre`. -/
theorem RunInv.slashStep {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B NX ΓX : Nat} (C : DriftConsts) (i : ValidatorIndex)
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀)
    (P : StepPre st₀ a E CX NX ΓX) (hn : exitedCount a + 1 ≤ NX) (hg : Γp ≤ ΓX)
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState a)
      = .ok ((), pureState b))
    (hunsl : slashedOf a i.toNat = false) (hiv : i ∈ vals) :
    AcKeep a b ∧ ∃ V' W' tag', RunInv vals st₀ E CX CC b V' W' tag' Γp B :=
  I.slash C i hnd hshape₀ h hunsl hiv P.cl P.cu P.cur P.curE P.kE (P.small_at hn hg) P.c62 P.ep62

end

end EthCLSpecs.Proofs.Heze
