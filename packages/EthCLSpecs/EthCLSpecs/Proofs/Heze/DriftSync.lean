import EthCLSpecs.Proofs.Heze.BalanceMoves
import EthCLSpecs.Proofs.Heze.DriftChurn

/-!
# `EthCLSpecs.Proofs.Heze.DriftSync`: the move of `process_sync_aggregate`

The sync aggregate pays each participant one reward and the proposer one reward per
participant, and takes one penalty from each absent member. Each reward and each penalty is
at most the participant reward plus the proposer reward. The base reward per increment is at
most `inc · BASE_REWARD_FACTOR / sq` when `sq * sq` is at most the total active balance
(`brpi_le`). Here `inc` is the `Gwei` increment that the body reads. The body forms the reward
amounts in `uint64`, with two checked products, and divides by each constant as a `uint64`.
So the bound needs `SYNC_COMMITTEE_SIZE < 2 ^ 64`. The move of one aggregate is then at most
`syncBudget sq U` (`processSyncAggregate_move`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure run_bind_eq_ok run_pure_eq_ok run_get_bind_eq_ok
  run_assert_bind_eq_ok run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

/-- A successful read of the base reward per increment is at most
`inc · BASE_REWARD_FACTOR / s` when `s * s` is at most the total active balance and `s > 0`.
`inc` is the `Gwei` increment that the body multiplies. The checked product did not overflow,
so the numerator is the `Nat` product. -/
theorem brpi_le (a : BeaconState) {s : Nat} (hs0 : 0 < s) (hs : s * s ≤ (totBal a).toNat)
    {p : Gwei} (hp : EthCLSpecs.Heze.getBaseRewardPerIncrement (pureState a) = .ok p) :
    p.toNat ≤ EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat *
        EthCLSpecs.Heze.Const.baseRewardFactor / s := by
  unfold EthCLSpecs.Heze.getBaseRewardPerIncrement at hp
  obtain ⟨num, hnum, hp⟩ := except_bind_eq_ok hp
  obtain ⟨rfl, hnumN⟩ := except_checkedMul_ok hnum
  obtain ⟨tot, htot, hp⟩ := except_bind_eq_ok hp
  injection hp with hp
  subst hp
  rw [totBal_of_ok htot] at hs
  have hq : (UInt64.ofNat (isqrt tot.toNat)).toNat = isqrt tot.toNat :=
    EthCLLib.Proofs.toNat_ofNat_lt64 (Nat.lt_of_le_of_lt (isqrt_le_self _) tot.toNat_lt)
  have hbrf : (UInt64.ofNat EthCLSpecs.Heze.Const.baseRewardFactor).toNat ≤
      EthCLSpecs.Heze.Const.baseRewardFactor := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_le _ _
  rw [UInt64.toNat_div, hq, hnumN]
  exact Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ hbrf))
    (Nat.div_le_div_left (le_isqrt hs) hs0)

omit [Preset] [HasherTag] in
/-- `List.mapM` returns a list of the length of its input. -/
theorem listMapM_run_length {σ ε β γ : Type} {f : β → StateT σ (Except ε) γ} :
    ∀ (ys : List β) (s s' : σ) (l : List γ), (ys.mapM f).run s = .ok (l, s') →
      l.length = ys.length
  | [], s, s', l, h => by
    rw [List.mapM_nil] at h
    rw [(EthCLLib.Proofs.run_pure_eq_ok_state h).1]
    rfl
  | b :: ys, s, s', l, h => by
    rw [List.mapM_cons] at h
    obtain ⟨_, s2, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
    obtain ⟨_, s3, hbs, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
    rw [(EthCLLib.Proofs.run_pure_eq_ok_state h).1, List.length_cons,
      listMapM_run_length ys s2 s3 _ hbs, List.length_cons]

omit [Preset] [HasherTag] in
/-- `Array.mapM` returns an array of the size of its input. -/
theorem mapM_run_size {σ ε β γ : Type} {f : β → StateT σ (Except ε) γ} (xs : Array β)
    {s s' : σ} {a : Array γ} (h : (xs.mapM f).run s = .ok (a, s')) : a.size = xs.size := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h
  obtain ⟨l, s1, h1, h2⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
  rw [(EthCLLib.Proofs.run_pure_eq_ok_state h2).1]
  simp only [List.size_toArray]
  rw [listMapM_run_length _ _ _ _ h1, Array.length_toList]

/-- The bound on the move of one sync aggregate. `s * s` is a lower bound and `U` an upper
bound on the total active balance. -/
def syncBudget (s U : Nat) : Nat :=
  let brpi := EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat *
    EthCLSpecs.Heze.Const.baseRewardFactor / s
  let mpr := brpi * (U / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat) *
    EthCLSpecs.Heze.Const.syncRewardWeight / EthCLSpecs.Heze.Const.weightDenominator /
      EthCLSpecs.Heze.Const.slotsPerEpoch
  let pr := mpr / EthCLSpecs.Heze.Const.syncCommitteeSize
  let ppr := pr * EthCLSpecs.Heze.Const.proposerWeight /
    (EthCLSpecs.Heze.Const.weightDenominator - EthCLSpecs.Heze.Const.proposerWeight)
  EthCLSpecs.Heze.Const.syncCommitteeSize * (pr + ppr)

theorem processSyncAggregate_move [Config] [CryptoBackend] (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) (E : Nat) (agg : EthCLSpecs.Heze.SyncAggregate) (a b : BeaconState)
    {s U : Nat} (hs0 : 0 < s) (hs : s * s ≤ (totBal a).toNat) (hU : (totBal a).toNat ≤ U)
    (hscs : EthCLSpecs.Heze.Const.syncCommitteeSize < 2 ^ 64)
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState a) = .ok ((), pureState b)) :
    moveN vals st₀ E a b ≤ syncBudget s U ∧ b = { a with balances := b.balances } ∧
      b.balances.val.size = a.balances.val.size := by
  unfold EthCLSpecs.Heze.processSyncAggregate at h
  have h := run_get_bind_eq_ok _ _ _ h
  extract_lets _ bits _ _ _ _ _ jp at h
  -- Each key choice passes its keys to `jp` on the start state.
  obtain ⟨_, h⟩ : ∃ y, (jp y).run (pureState a) = .ok ((), pureState b) := by
    split at h
    · rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_pure,
        EthCLLib.Proofs.except_bind_ok] at h
      exact ⟨_, h⟩
    · split at h
      · obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
        obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
        obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
        rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_pure,
          EthCLLib.Proofs.except_bind_ok] at h
        exact ⟨_, h⟩
      · rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_pure,
          EthCLLib.Proofs.except_bind_ok] at h
        exact ⟨_, h⟩
  simp only [jp] at h
  obtain ⟨root, h1, h⟩ :=
    run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The two reads of the totals succeed and keep the state.
  cases htot : EthCLSpecs.Heze.getTotalActiveBalance (pureState a) with
  | error e =>
    rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_error _ _ (by rw [htot]; rfl),
      EthCLLib.Proofs.except_bind_error] at h
    cases h
  | ok tot =>
  rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_ok _ _ (by rw [htot]; rfl),
    EthCLLib.Proofs.except_bind_ok] at h
  cases hbr : EthCLSpecs.Heze.getBaseRewardPerIncrement (pureState a) with
  | error e =>
    rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_error _ _ (by rw [hbr]; rfl),
      EthCLLib.Proofs.except_bind_error] at h
    cases h
  | ok brpi =>
  rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_ok _ _ (by rw [hbr]; rfl),
    EthCLLib.Proofs.except_bind_ok] at h
  have et := totBal_of_ok htot
  -- The two checked products of the reward amounts keep the state and did not overflow.
  obtain ⟨tbr, s1a, htbr, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, htbrN⟩ := checkedMul_run_ok htbr
  obtain ⟨wr, s1b, hwr, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, hwrN⟩ := checkedMul_run_ok hwr
  -- The search for the committee indices reads the state only, and finds one index per key.
  obtain ⟨ci, s1, hci, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e1 : s1 = pureState a := mapM_run_state_eq (fun _ _ _ _ hb => by
    split at hb
    · exact (EthCLLib.Proofs.run_pure_eq_ok_state hb).2
    · unfold EthCLLib.Spec.throwArithmetic at hb
      rw [EthCLLib.Proofs.run_liftErr_of_error _ _ rfl] at hb
      cases hb) _ hci
  subst e1
  have hsz : ci.size = EthCLSpecs.Heze.Const.syncCommitteeSize := by
    rw [mapM_run_size _ hci, Vector.size_toArray]
  obtain ⟨r, s2, hloop, hset⟩ := run_bind_eq_ok _ _ _ _ h
  have hb : pureState b = r := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
  -- The participant reward `pr` and the proposer reward `ppr` of the spec, in `uint64`.
  obtain ⟨pr, hpr⟩ : ∃ pr : Gwei, pr = brpi * (tot / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG) *
      UInt64.ofNat EthCLSpecs.Heze.Const.syncRewardWeight /
      UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator /
      UInt64.ofNat EthCLSpecs.Heze.Const.slotsPerEpoch /
      UInt64.ofNat EthCLSpecs.Heze.Const.syncCommitteeSize := ⟨_, rfl⟩
  obtain ⟨ppr, hppr⟩ : ∃ ppr : Gwei, ppr = pr * UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight /
      UInt64.ofNat (EthCLSpecs.Heze.Const.weightDenominator -
        EthCLSpecs.Heze.Const.proposerWeight) := ⟨_, rfl⟩
  rw [← hpr, ← hppr] at hloop
  -- The loop threads plain states, and its accumulator is a plain state.
  have hloop' := forIn'_range_move_le_inv (fun x y : State => moveN vals st₀ E x.view y.view)
    (fun x y z => moveN_triangle vals st₀ E _ _ _) (fun x => moveN_self vals st₀ E _)
    (fun x : State => ∃ y : BeaconState, x = pureState y ∧ y = { a with balances := y.balances } ∧
      y.balances.val.size = a.balances.val.size)
    (fun s : State => ∃ u : BeaconState, s = pureState u)
    (pr.toNat + ppr.toNat) _ _ ?step _ _ _ _ ⟨a, rfl, rfl, rfl⟩ ⟨a, rfl⟩ hloop
  case step =>
    intro i hi acc s s' st ⟨y, hy, hya, hysz⟩ ⟨u, hu⟩ hbody
    subst hy hu
    rcases run_ite_eq_ok hbody with ⟨-, hbody⟩ | ⟨-, hbody⟩
    · obtain ⟨x1, s3, h1, hbody⟩ :=
        run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) hbody
      obtain ⟨-, hm1, hx1, hs1⟩ := moveN_increaseBalance vals hnd st₀ E y _ _ _ h1
      obtain ⟨x2, s4, h2, hbody⟩ :=
        run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) hbody
      obtain ⟨-, hm2, hx2, hs2⟩ := moveN_increaseBalance vals hnd st₀ E x1 _ _ _ h2
      obtain ⟨_, s5, h5, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
      have e5 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h5
      have e6 := run_pure_eq_ok _ _ _ _ hbody
      have e7 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hbody
      subst e5 e6 e7
      refine ⟨⟨x2, rfl, ?_, by rw [hs2, hs1, hysz]⟩, ⟨_, rfl⟩, ?_⟩
      · rw [hx2, hx1, hya]
      · have := moveN_triangle vals st₀ E y x1 x2
        show moveN vals st₀ E y x2 ≤ _
        omega
    · obtain ⟨x1, s3, h1, hbody⟩ :=
        run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) hbody
      obtain ⟨-, hm1, hx1, hs1⟩ := moveN_decreaseBalance vals hnd st₀ E y _ _ _ h1
      obtain ⟨_, s5, h5, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
      have e5 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h5
      have e6 := run_pure_eq_ok _ _ _ _ hbody
      have e7 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hbody
      subst e5 e6 e7
      refine ⟨⟨x1, rfl, ?_, by rw [hs1, hysz]⟩, ⟨_, rfl⟩, ?_⟩
      · rw [hx1, hya]
      · show moveN vals st₀ E y x1 ≤ _
        omega
  obtain ⟨⟨y, hy, hya, hysz⟩, -, hm⟩ := hloop'
  subst hy
  have hyb : b = y := congrArg SizzLean.Cache.SSZ.Box.view hb
  subst hyb
  refine ⟨?_, hya, hysz⟩
  have hm' : moveN vals st₀ E a b ≤ (pr.toNat + ppr.toNat) * EthCLSpecs.Heze.Const.syncCommitteeSize := by
    rw [← hsz]
    exact hm
  -- Each reward is at most its bound in the budget. The two checked products did not
  -- overflow, and every divisor is below `2 ^ 64`, so the `uint64` amounts are the `Nat` ones.
  have hbr := brpi_le a hs0 hs hbr
  rw [et] at hU
  have eSRW : (UInt64.ofNat EthCLSpecs.Heze.Const.syncRewardWeight).toNat =
      EthCLSpecs.Heze.Const.syncRewardWeight := EthCLLib.Proofs.toNat_ofNat_lt64 (by decide)
  have eWD : (UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat =
      EthCLSpecs.Heze.Const.weightDenominator := EthCLLib.Proofs.toNat_ofNat_lt64 (by decide)
  have ePW : (UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight).toNat =
      EthCLSpecs.Heze.Const.proposerWeight := EthCLLib.Proofs.toNat_ofNat_lt64 (by decide)
  have eWDPW : (UInt64.ofNat (EthCLSpecs.Heze.Const.weightDenominator -
      EthCLSpecs.Heze.Const.proposerWeight)).toNat =
      EthCLSpecs.Heze.Const.weightDenominator - EthCLSpecs.Heze.Const.proposerWeight :=
    EthCLLib.Proofs.toNat_ofNat_lt64 (by decide)
  have eSPE : (UInt64.ofNat EthCLSpecs.Heze.Const.slotsPerEpoch).toNat =
      EthCLSpecs.Heze.Const.slotsPerEpoch :=
    EthCLLib.Proofs.toNat_ofNat_lt64 EthCLSpecs.Heze.Const.slotsPerEpochLt
  have eSCS : (UInt64.ofNat EthCLSpecs.Heze.Const.syncCommitteeSize).toNat =
      EthCLSpecs.Heze.Const.syncCommitteeSize := EthCLLib.Proofs.toNat_ofNat_lt64 hscs
  have e1 : (tot / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG).toNat =
      tot.toNat / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat := UInt64.toNat_div _ _
  have e2 : (brpi * (tot / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG)).toNat =
      brpi.toNat * (tot.toNat / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat) := by
    rw [htbrN, e1]
  have e3 : (brpi * (tot / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG) *
      UInt64.ofNat EthCLSpecs.Heze.Const.syncRewardWeight).toNat =
      brpi.toNat * (tot.toNat / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat) *
        EthCLSpecs.Heze.Const.syncRewardWeight := by
    rw [hwrN, e2, eSRW]
  have hpr' : pr.toNat ≤ (EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat *
      EthCLSpecs.Heze.Const.baseRewardFactor / s *
      (U / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat) *
      EthCLSpecs.Heze.Const.syncRewardWeight / EthCLSpecs.Heze.Const.weightDenominator /
      EthCLSpecs.Heze.Const.slotsPerEpoch / EthCLSpecs.Heze.Const.syncCommitteeSize) := by
    rw [hpr, UInt64.toNat_div, UInt64.toNat_div, UInt64.toNat_div, e3, eWD, eSPE, eSCS]
    exact Nat.div_le_div_right (Nat.div_le_div_right (Nat.div_le_div_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul hbr (Nat.div_le_div_right hU)))))
  have hppr' : ppr.toNat ≤ (EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat *
      EthCLSpecs.Heze.Const.baseRewardFactor / s *
      (U / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat) *
      EthCLSpecs.Heze.Const.syncRewardWeight / EthCLSpecs.Heze.Const.weightDenominator /
      EthCLSpecs.Heze.Const.slotsPerEpoch / EthCLSpecs.Heze.Const.syncCommitteeSize) *
      EthCLSpecs.Heze.Const.proposerWeight /
      (EthCLSpecs.Heze.Const.weightDenominator - EthCLSpecs.Heze.Const.proposerWeight) := by
    rw [hppr, UInt64.toNat_div, eWDPW]
    refine Nat.div_le_div_right (Nat.le_trans ?_ (Nat.mul_le_mul_right _ hpr'))
    rw [UInt64.toNat_mul, ePW]
    exact Nat.mod_le _ _
  unfold syncBudget
  dsimp only
  rw [Nat.mul_comm EthCLSpecs.Heze.Const.syncCommitteeSize]
  exact Nat.le_trans hm' (Nat.mul_le_mul_right _ (Nat.add_le_add hpr' hppr'))

end

end EthCLSpecs.Proofs.Heze
