import EthCLSpecs.Proofs.Heze.DriftEpoch

/-!
# `EthCLSpecs.Proofs.Heze.DriftRewards`: the rewards and penalties of an epoch

`process_rewards_and_penalties` applies four pairs of delta arrays to the balances: one pair
for each participation flag, and the inactivity penalties. `applyDeltas_move` bounds the move
of one pair by the sum of its entries.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

variable [Config] [CryptoBackend] in
/-- **One pair of delta arrays moves the capped balances by at most the sum of its entries.** -/
theorem applyDeltas_move (vals : List ValidatorIndex) (hnd : vals.Nodup) (st₀ : BeaconState)
    (E : Nat) (rw pn : Array Gwei) (y w : BeaconState) {x w' : BeaconState}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) rw pn (pureState y)).run
      (pureState w) = .ok (pureState x, pureState w')) :
    moveN vals st₀ E y x ≤
      ((List.range y.validators.val.size).map fun i => rw[i]!.toNat + pn[i]!.toNat).sum ∧
      x = { y with balances := x.balances } ∧ x.balances.val.size = y.balances.val.size := by
  unfold EthCLSpecs.Heze.applyDeltas at h
  dsimp only at h
  obtain ⟨r1, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e1 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst e1
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
  -- The loop threads plain states, and its accumulator is a plain state.
  have hloop := forIn_move_le_inv (fun x z : State => moveN vals st₀ E x.view z.view)
    (fun x z w => moveN_triangle vals st₀ E _ _ _) (fun x => moveN_self vals st₀ E _)
    (fun x : State => ∃ z : BeaconState, x = pureState z ∧ z = { y with balances := z.balances } ∧
      z.balances.val.size = y.balances.val.size)
    (fun s : State => ∃ u : BeaconState, s = pureState u)
    (fun i => rw[i]!.toNat + pn[i]!.toNat) _ _ ?step _ _ _ _ ⟨y, rfl, rfl, rfl⟩ ⟨w, rfl⟩ h1
  case step =>
    intro i hi acc s s'' st ⟨z, hz, hzy, hzsz⟩ ⟨u, hu⟩ hbody
    subst hz hu
    obtain ⟨x1, s2, h2, hbody⟩ :=
      run_bind_eq_ok_ret (EthCLSpecs.Proofs.Heze.returnsUncached_increaseBalance _ _ _) hbody
    obtain ⟨-, hm1, hx1, hs1⟩ := moveN_increaseBalance vals hnd st₀ E z _ _ _ h2
    obtain ⟨x2, s3, h3, hbody⟩ :=
      run_bind_eq_ok_ret (EthCLSpecs.Proofs.Heze.returnsUncached_decreaseBalance _ _ _) hbody
    obtain ⟨-, hm2, hx2, hs2⟩ := moveN_decreaseBalance vals hnd st₀ E x1 _ _ _ h3
    obtain ⟨_, s4, h4, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
    have e4 := run_pure_state_eq _ _ _ _ h4
    have e5 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbody
    have e6 := run_pure_state_eq _ _ _ _ hbody
    subst e4 e5 e6
    refine ⟨⟨x2, rfl, by rw [hx2, hx1, hzy], by rw [hs2, hs1, hzsz]⟩, ⟨_, rfl⟩, ?_⟩
    have := moveN_triangle vals st₀ E z x1 x2
    show moveN vals st₀ E z x2 ≤ rw[i]!.toNat + pn[i]!.toNat
    omega
  obtain ⟨⟨x', hx, hxy, hxsz⟩, -, hm⟩ := hloop
  obtain rfl := EthCLLib.Proofs.pureState_inj hx
  refine ⟨?_, hxy, hxsz⟩
  have := hm
  simp only [SizzLean.Proofs.view_uncachedBox] at this
  rw [List.range_eq_range']
  simpa [Std.Legacy.Range.size] using this

omit [Preset] [HasherTag] in
/-- A successful `sszGetIdx` in `Except` found the entry. -/
theorem sszGetIdx_ok {α : Type} {cap n : Nat} {xs : SizzLean.Repr.SSZList α cap} {x : α}
    (h : (sszGetIdx xs n : Except StateTransitionError α) = .ok x) : xs.val[n]? = some x := by
  unfold sszGetIdx liftErr at h
  split at h
  · rename_i y hy
    injection h with h
    exact h ▸ hy
  · cases h

omit [Preset] [HasherTag] in
/-- An entry that exists is the entry `[i]!` reads. -/
theorem sszList_getElem!_of_some {α : Type} [Inhabited α] {cap i : Nat}
    {xs : SizzLean.Repr.SSZList α cap} {x : α} (h : xs.val[i]? = some x) : xs[i]! = x := by
  obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp h
  rw [sszList_getElem!_eq, getElem!_pos xs.val i hi, he]

/-- The base reward per increment of `a`. A fault gives `0`, as in `totBal`. -/
def brpiOf (a : BeaconState) : Nat :=
  match EthCLSpecs.Heze.getBaseRewardPerIncrement (pureState a) with
  | .ok p => p.toNat
  | .error _ => 0

/-- The base reward of index `j`. -/
def brOf (a : BeaconState) (j : Nat) : Nat :=
  ebN a j / incN * brpiOf a

/-- A successful read of a base reward returns `brOf`. The product is checked, so it does not
wrap. -/
theorem getBaseReward_eq (a : BeaconState) (vi : ValidatorIndex) (br : Gwei)
    (h : EthCLSpecs.Heze.getBaseReward (pureState a) vi = .ok br) :
    br.toNat = brOf a vi.toNat := by
  unfold EthCLSpecs.Heze.getBaseReward at h
  obtain ⟨v, hv, h⟩ := except_bind_eq_ok h
  obtain ⟨p, hp, h⟩ := except_bind_eq_ok h
  obtain ⟨rfl, hN⟩ := except_checkedMul_ok h
  have hy : a.validators.val[vi.toNat]? = some v := sszGetIdx_ok hv
  rw [hN, UInt64.toNat_div]
  unfold brOf ebN brpiOf incN
  rw [hy, hp]

omit [Preset] [HasherTag] in
/-- A write into an array keeps a bound on each entry, when the written value meets it. -/
theorem getElem!_set!_le {a : Array Gwei} {f : Nat → Nat} (ha : ∀ j, a[j]!.toNat ≤ f j)
    (i : Nat) (v : Gwei) (hv : v.toNat ≤ f i) (j : Nat) : (a.set! i v)[j]!.toNat ≤ f j := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by simpa using hj
    rw [getElem!_pos _ j hj']
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds hj]
    split
    · rename_i hij; subst hij; exact hv
    · have := ha j; rwa [getElem!_pos a j hj] at this
  · have hj' : ¬ j < (a.set! i v).size := by simpa using hj
    rw [getElem!_neg _ j hj']
    have := ha j
    rwa [getElem!_neg a j hj] at this

omit [Preset] [HasherTag] in
theorem getElem!_replicate_zero (n j : Nat) : (Array.replicate n (0 : Gwei))[j]!.toNat = 0 := by
  by_cases hj : j < n
  · rw [getElem!_pos _ j (by simpa using hj)]; simp
  · rw [getElem!_neg _ j (by simpa using hj)]; rfl

/-- The total balance of the unslashed participants of flag `f` in the previous epoch. A fault
of either read gives `0`, as in `tgtBal`. -/
def flagTotOf (a : BeaconState) (f : Nat) : Gwei :=
  match EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState a) f
      (EthCLSpecs.Heze.previousEpochOf (pureState a)) with
  | .ok idx =>
    match EthCLSpecs.Heze.getTotalBalance (pureState a) idx with
    | .ok g => g
    | .error _ => 0
  | .error _ => 0

/-- The reward ratio of a flag, plus one: the unslashed participating increments over the
active increments. -/
def fdR (a : BeaconState) (f : Nat) : Nat :=
  (flagTotOf a f).toNat / incN / ((totBal a).toNat / incN) + 1

omit [Preset] [HasherTag] in
/-- `x * u / (d * w) ≤ x * (u / d + 1) / w`. -/
theorem mul_div_mul_le (x u d w : Nat) : x * u / (d * w) ≤ x * (u / d + 1) / w := by
  rw [← Nat.div_div_eq_div_mul]
  refine Nat.div_le_div_right ?_
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · refine Nat.div_le_of_le_mul ?_
    have := Nat.lt_mul_div_succ u hd
    calc x * u ≤ x * (d * (u / d + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = d * (x * (u / d + 1)) := by rw [Nat.mul_left_comm]

/-- **Each entry of the flag deltas is at most the base reward times the flag weight times
the reward ratio.** The divisor `active_increments * WEIGHT_DENOMINATOR` is a checked product,
so in a successful run it does not wrap. -/
theorem getFlagIndexDeltas_le (a : BeaconState) (f : Nat) (rw pn : Array Gwei)
    (h : EthCLSpecs.Heze.getFlagIndexDeltas (pureState a) f = .ok (rw, pn)) (j : Nat) :
    rw[j]!.toNat ≤ brOf a j * EthCLSpecs.Heze.Const.participationFlagWeights[f]! * fdR a f /
        EthCLSpecs.Heze.Const.weightDenominator ∧
      pn[j]!.toNat ≤ brOf a j * EthCLSpecs.Heze.Const.participationFlagWeights[f]! * fdR a f /
        EthCLSpecs.Heze.Const.weightDenominator := by
  unfold EthCLSpecs.Heze.getFlagIndexDeltas at h
  dsimp only at h
  obtain ⟨idx, hidx, h⟩ := except_bind_eq_ok h
  obtain ⟨tb, htb, h⟩ := except_bind_eq_ok h
  obtain ⟨ta, hta, h⟩ := except_bind_eq_ok h
  obtain ⟨r, h1, h⟩ := except_bind_eq_ok h
  rcases r with ⟨p', r'⟩
  have e := except_pure_ok h
  injection e with e1 e2
  subst e1 e2
  rw [← Array.forIn_toList] at h1
  -- The two totals equal the value handles.
  have htf : flagTotOf a f = tb := by simp only [flagTotOf, hidx, htb]
  have hta' : totBal a = ta := totBal_of_ok hta
  have hR : fdR a f = tb.toNat / incN / (ta.toNat / incN) + 1 := by unfold fdR; rw [htf, hta']
  have hof : ∀ n : Nat, (UInt64.ofNat n).toNat ≤ n := fun n => by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_le _ _
  have hwdN : (UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat =
      EthCLSpecs.Heze.Const.weightDenominator := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by decide)
  have hR1 : 1 ≤ fdR a f := Nat.le_add_left 1 _
  let D : Nat → Nat := fun j => brOf a j * EthCLSpecs.Heze.Const.participationFlagWeights[f]! *
    fdR a f / EthCLSpecs.Heze.Const.weightDenominator
  have key := except_forIn_list_inv
    (fun acc : MProd (Array Gwei) (Array Gwei) => ∀ j, acc.snd[j]!.toNat ≤ D j ∧ acc.fst[j]!.toNat ≤ D j)
    _ _ (fun vi _ b r' hb hf => by
      obtain ⟨br, hg, hf⟩ := except_bind_eq_ok hf
      have ebr := getBaseReward_eq a vi br hg
      -- `UInt64.ofNat` does not raise the weight.
      have hbw : br.toNat *
          (UInt64.ofNat EthCLSpecs.Heze.Const.participationFlagWeights[f]!).toNat ≤
          brOf a vi.toNat * EthCLSpecs.Heze.Const.participationFlagWeights[f]! := by
        rw [ebr]; exact Nat.mul_le_mul_left _ (hof _)
      split at hf
      · obtain ⟨leak, -, hf⟩ := except_bind_eq_ok hf
        split at hf
        · obtain ⟨w1, hw1, hf⟩ := except_bind_eq_ok hf
          obtain ⟨w2, hw2, hf⟩ := except_bind_eq_ok hf
          obtain ⟨w3, hw3, hf⟩ := except_bind_eq_ok hf
          obtain ⟨-, -, hf⟩ := except_bind_eq_ok hf
          have e := except_pure_ok hf
          subst e
          obtain ⟨rfl, hm1⟩ := except_checkedMul_ok hw1
          obtain ⟨rfl, hm2⟩ := except_checkedMul_ok hw2
          obtain ⟨rfl, hm3⟩ := except_checkedMul_ok hw3
          have hrw : (br *
              UInt64.ofNat EthCLSpecs.Heze.Const.participationFlagWeights[f]! *
              (tb / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG) /
              (ta / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG *
                UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator)).toNat ≤ D vi.toNat := by
            rw [UInt64.toNat_div, hm2, hm1, hm3, hwdN, UInt64.toNat_div, UInt64.toNat_div]
            show _ ≤ brOf a vi.toNat * EthCLSpecs.Heze.Const.participationFlagWeights[f]! *
              fdR a f / EthCLSpecs.Heze.Const.weightDenominator
            rw [hR]
            exact Nat.le_trans (mul_div_mul_le _ _ _ _)
              (Nat.div_le_div_right (Nat.mul_le_mul_right _ hbw))
          exact fun j => ⟨getElem!_set!_le (fun j => (hb j).1) _ _ hrw j, (hb j).2⟩
        · obtain ⟨-, -, hf⟩ := except_bind_eq_ok hf
          have e := except_pure_ok hf
          subst e
          exact hb
      · split at hf
        · obtain ⟨w1, hw1, hf⟩ := except_bind_eq_ok hf
          obtain ⟨-, -, hf⟩ := except_bind_eq_ok hf
          have e := except_pure_ok hf
          subst e
          obtain ⟨rfl, hm1⟩ := except_checkedMul_ok hw1
          have hpn : (br *
              UInt64.ofNat EthCLSpecs.Heze.Const.participationFlagWeights[f]! /
              UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator).toNat ≤ D vi.toNat := by
            rw [UInt64.toNat_div, hm1, hwdN]
            exact Nat.div_le_div_right (Nat.le_trans hbw (Nat.le_mul_of_pos_right _ hR1))
          exact fun j => ⟨(hb j).1, getElem!_set!_le (fun j => (hb j).2) _ _ hpn j⟩
        · obtain ⟨-, -, hf⟩ := except_bind_eq_ok hf
          have e := except_pure_ok hf
          subst e
          exact hb)
    _ _ (fun j => by simp only [getElem!_replicate_zero]; exact ⟨Nat.zero_le _, Nat.zero_le _⟩) h1
  exact key j

end

section
variable [Preset] [HasherTag] [Config]

/-- The divisor of an inactivity penalty, as the `uint64` product computes it. -/
def ipDenom : Nat :=
  (EthCLSpecs.Heze.Const.inactivityScoreBias *
    UInt64.ofNat EthCLSpecs.Heze.Const.inactivityPenaltyQuotientBellatrix).toNat

/-- **Each inactivity penalty is at most the effective balance times the score bound.** The
score read found the entry, and the product is checked. -/
theorem getInactivityPenaltyDeltas_le (a : BeaconState) {S : Nat} {ip : Array Gwei}
    (hip : EthCLSpecs.Heze.getInactivityPenaltyDeltas (pureState a) = .ok ip)
    (hS : ∀ i, i < sizeOf a → (a.inactivityScores[i]!).toNat ≤ S) (j : Nat) :
    ip[j]!.toNat ≤ ebN a j * S / ipDenom := by
  unfold EthCLSpecs.Heze.getInactivityPenaltyDeltas at hip
  simp only [SizzLean.Proofs.view_uncachedBox] at hip
  obtain ⟨mt, -, hip⟩ := except_bind_eq_ok hip
  obtain ⟨r, h1, hip⟩ := except_bind_eq_ok hip
  have e := except_pure_ok hip
  subst e
  rw [← Array.forIn_toList] at h1
  refine except_forIn_list_inv (fun p : Array Gwei => ∀ j, p[j]!.toNat ≤ ebN a j * S / ipDenom)
    _ _ (fun vi _ b r' hb hf => ?_) _ _
    (fun j => by rw [getElem!_replicate_zero]; exact Nat.zero_le _) h1 j
  split at hf
  · obtain ⟨score, hsc, hf⟩ := except_bind_eq_ok hf
    obtain ⟨num, hnum, hf⟩ := except_bind_eq_ok hf
    -- The checked denominator, formed in the loop after the numerator, is `ipDenom`.
    obtain ⟨den, hden, hf⟩ := except_bind_eq_ok hf
    obtain ⟨rfl, -⟩ := except_checkedMul_ok hden
    obtain ⟨-, -, hf⟩ := except_bind_eq_ok hf
    have e := except_pure_ok hf
    subst e
    obtain ⟨rfl, hm⟩ := except_checkedMul_ok hnum
    have hsc' : a.inactivityScores.val[vi.toNat]? = some score := sszGetIdx_ok hsc
    refine getElem!_set!_le hb _ _ ?_
    rw [UInt64.toNat_div, hm]
    refine Nat.div_le_div_right ?_
    rw [sszList_getElem!_eq]
    by_cases hi : vi.toNat < a.validators.val.size
    · rw [getElem!_pos a.validators.val _ hi]
      have he : ebN a vi.toNat = (a.validators.val[vi.toNat]).effectiveBalance.toNat := by
        unfold ebN; rw [getElem?_pos a.validators.val _ hi]
      rw [← he, ← sszList_getElem!_of_some hsc']
      exact Nat.mul_le_mul_left _ (hS _ hi)
    · rw [getElem!_neg a.validators.val _ hi]
      show 0 * _ ≤ _
      rw [Nat.zero_mul]
      exact Nat.zero_le _
  · obtain ⟨-, -, hf⟩ := except_bind_eq_ok hf
    have e := except_pure_ok hf
    subst e
    exact hb

end

/-! ## Sums of the deltas -/

theorem add_div_le (x y d : Nat) : x / d + y / d ≤ (x + y) / d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · rw [Nat.le_div_iff_mul_le hd, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)

theorem sum_div_le {α : Type} (g : α → Nat) (d : Nat) :
    ∀ l : List α, (l.map fun x => g x / d).sum ≤ (l.map g).sum / d := by
  intro l
  induction l with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans (Nat.add_le_add_left ih _) (add_div_le _ _ _)

theorem sum_mul_right {α : Type} (g : α → Nat) (c : Nat) :
    ∀ l : List α, (l.map fun x => g x * c).sum = (l.map g).sum * c := by
  intro l
  induction l with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem sum_le_sum {α : Type} {g h : α → Nat} (hgh : ∀ x, g x ≤ h x) :
    ∀ l : List α, (l.map g).sum ≤ (l.map h).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hgh x) ih

theorem sublist_sum_le {α : Type} (g : α → Nat) {l₁ l₂ : List α} (h : l₁.Sublist l₂) :
    (l₁.map g).sum ≤ (l₂.map g).sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons₂ a _ ih => simp only [List.map_cons, List.sum_cons]; omega

section
variable [Preset] [HasherTag]

/-- The sum of the effective balances of the registry. -/
def ebSum (a : BeaconState) : Nat := ((List.range (sizeOf a)).map (ebN a)).sum

omit [HasherTag] in
theorem eb!_eq (a : BeaconState) (k : Nat) :
    (a.validators[k]!).effectiveBalance.toNat = ebN a k := by
  rw [sszList_getElem!_eq]
  unfold ebN
  by_cases hk : k < a.validators.val.size
  · rw [getElem!_pos a.validators.val _ hk, getElem?_pos a.validators.val _ hk]
  · rw [getElem!_neg a.validators.val _ hk, Array.getElem?_eq_none (by omega)]
    rfl

/-- **The total balance of the unslashed participants of a flag is at most `U`.** -/
theorem flagTot_le (a : BeaconState) (f : Nat) {U : Nat} (h64 : sizeOf a < 2 ^ 64)
    (hU : ebSum a ≤ U) (hinc : incN ≤ U) : (flagTotOf a f).toNat ≤ U := by
  unfold flagTotOf
  split
  · rename_i idx hidx
    split
    · rename_i g hg
      rw [getTotalBalance_ok_toNat hg]
      refine Nat.max_le.mpr ⟨?_, hinc⟩
      rw [getUnslashedParticipatingIndices_ok_toList hidx, getActiveValidatorIndices_toList]
      refine Nat.le_trans (sublist_sum_le _ List.filter_sublist) ?_
      refine Nat.le_trans (sublist_sum_le _ (List.filter_sublist.map _)) ?_
      rw [List.map_map]
      refine Nat.le_trans (Nat.le_of_eq ?_) hU
      unfold ebSum sizeOf
      congr 1
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      unfold sizeOf at h64
      simp only [Function.comp, effBal]
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      unfold ebN
      rw [getElem!_pos a.validators.val _ hi, getElem?_pos a.validators.val _ hi]
    · exact Nat.zero_le _
  · exact Nat.zero_le _

/-! ## The budget of the rewards -/

/-- The bound of the base reward per increment, when `sq * sq` is at most the total active
balance. -/
def brpiB (sq : Nat) : Nat :=
  incN * EthCLSpecs.Heze.Const.baseRewardFactor / sq

/-- The lower bound of the active increments. -/
def aLo (sq : Nat) : Nat := max 1 (sq * sq / incN)

/-- The bound of the reward ratio `fdR`. -/
def rRatio (sq U : Nat) : Nat := U / incN / aLo sq + 1

/-- The bound of the move of the deltas of one flag. -/
def flagBudget (sq U : Nat) : Nat :=
  2 * (U / incN * brpiB sq * rRatio sq U)

theorem fdR_le (a : BeaconState) (f : Nat) {sq U : Nat} (h64 : sizeOf a < 2 ^ 64)
    (hsq : sq * sq ≤ (totBal a).toNat)
    (hU : ebSum a ≤ U) (hinc : incN ≤ U) : fdR a f ≤ rRatio sq U := by
  unfold fdR rRatio
  refine Nat.add_le_add_right ?_ 1
  have htb := flagTot_le a f h64 hU hinc
  rcases Nat.eq_zero_or_pos ((totBal a).toNat / incN) with hz | hp
  · rw [hz, Nat.div_zero]; exact Nat.zero_le _
  · refine Nat.div_le_div (Nat.div_le_div_right htb) ?_ (by unfold aLo; omega)
    unfold aLo
    exact Nat.max_le.mpr ⟨hp, Nat.div_le_div_right hsq⟩

theorem sum_brOf_le (a : BeaconState) {sq U : Nat} (h0 : 0 < sq)
    (hsq : sq * sq ≤ (totBal a).toNat)
    (hU : ebSum a ≤ U) :
    ((List.range (sizeOf a)).map (brOf a)).sum ≤
      U / incN * brpiB sq := by
  unfold brOf
  rw [sum_mul_right (fun j => ebN a j / incN)]
  refine Nat.mul_le_mul (Nat.le_trans (sum_div_le _ _ _) (Nat.div_le_div_right hU)) ?_
  unfold brpiOf
  split
  · rename_i p hp
    exact brpi_le a h0 hsq hp
  · exact Nat.zero_le _

omit [Preset] [HasherTag] in
theorem weight_le (f : Nat) :
    EthCLSpecs.Heze.Const.participationFlagWeights[f]! ≤ EthCLSpecs.Heze.Const.weightDenominator :=
  Nat.le_trans (flagWeight_le f) (by unfold wSum; decide)

/-- **The deltas of one flag move the balances by at most `flagBudget`.** -/
theorem flagPair_sum_le (a : BeaconState) (f : Nat) (rw pn : Array Gwei)
    (h : EthCLSpecs.Heze.getFlagIndexDeltas (pureState a) f = .ok (rw, pn)) {sq U : Nat}
    (h0 : 0 < sq) (h64 : sizeOf a < 2 ^ 64)
    (hsq : sq * sq ≤ (totBal a).toNat)
    (hU : ebSum a ≤ U) (hinc : incN ≤ U) :
    ((List.range a.validators.val.size).map fun i => rw[i]!.toNat + pn[i]!.toNat).sum ≤
      flagBudget sq U := by
  have hd := getFlagIndexDeltas_le a f rw pn h
  have hwd : 0 < EthCLSpecs.Heze.Const.weightDenominator := by decide
  -- Each entry is at most `brOf a i * fdR a f`, as the weight is at most the denominator.
  have hD : ∀ i, brOf a i * EthCLSpecs.Heze.Const.participationFlagWeights[f]! * fdR a f /
      EthCLSpecs.Heze.Const.weightDenominator ≤ brOf a i * fdR a f := fun i => by
    refine Nat.div_le_of_le_mul ?_
    rw [Nat.mul_right_comm, Nat.mul_comm EthCLSpecs.Heze.Const.weightDenominator]
    exact Nat.mul_le_mul_left _ (weight_le f)
  have h1 : ((List.range a.validators.val.size).map fun i => rw[i]!.toNat + pn[i]!.toNat).sum ≤
      ((List.range (sizeOf a)).map fun i => brOf a i * fdR a f * 2).sum :=
    sum_le_sum (fun i => by have := hD i; have := hd i; omega) _
  rw [sum_mul_right, sum_mul_right] at h1
  refine Nat.le_trans h1 ?_
  unfold flagBudget
  rw [Nat.mul_comm _ 2]
  exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul (sum_brOf_le a h0 hsq hU) (fdR_le a f h64 hsq hU hinc))

end

section
variable [Preset] [HasherTag] [Config]

/-- The bound of the move of the inactivity penalties, when each score is at most `S`. -/
def inactBudget (U S : Nat) : Nat := U * S / ipDenom

/-- The bound of the move of `process_rewards_and_penalties`. -/
def rewBudget (sq U S : Nat) : Nat := 3 * flagBudget sq U + inactBudget U S

theorem inactPair_sum_le (a : BeaconState) {U S : Nat} {ip : Array Gwei}
    (hip : EthCLSpecs.Heze.getInactivityPenaltyDeltas (pureState a) = .ok ip)
    (hS : ∀ i, i < sizeOf a → (a.inactivityScores[i]!).toNat ≤ S) (hU : ebSum a ≤ U) :
    ((List.range a.validators.val.size).map fun i =>
      (Array.replicate a.validators.val.size (0 : Gwei))[i]!.toNat + ip[i]!.toNat).sum ≤
      inactBudget U S := by
  have h1 := sum_le_sum (g := fun i =>
      (Array.replicate a.validators.val.size (0 : Gwei))[i]!.toNat + ip[i]!.toNat)
    (h := fun i => ebN a i * S / ipDenom)
    (fun i => by
      dsimp only
      rw [getElem!_replicate_zero, Nat.zero_add]
      exact getInactivityPenaltyDeltas_le a hip hS i)
    (List.range a.validators.val.size)
  refine Nat.le_trans h1 (Nat.le_trans (sum_div_le _ _ _) (Nat.div_le_div_right ?_))
  rw [sum_mul_right]
  exact Nat.mul_le_mul_right _ hU

omit [Preset] [HasherTag] [Config] in
/-- Each result of a successful `mapM` in `Except` is a result of the function at an element. -/
theorem except_mapM_ok {α β ε : Type} (g : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM g = .ok r →
      r.length = l.length ∧ ∀ y ∈ r, ∃ x ∈ l, g x = .ok y := by
  intro l
  induction l with
  | nil =>
    intro r h
    simp only [List.mapM_nil] at h
    injection h with h
    subst h
    exact ⟨rfl, fun y hy => absurd hy List.not_mem_nil⟩
  | cons x rest ih =>
    intro r h
    rw [List.mapM_cons] at h
    cases hx : g x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      cases hr : rest.mapM g with
      | error e => rw [hr] at h; cases h
      | ok ys =>
        rw [hr] at h
        injection h with h
        subst h
        obtain ⟨hl, hm⟩ := ih ys hr
        refine ⟨by simp [hl], fun z hz => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨w, hw, hg⟩ := hm z hz
          exact ⟨w, List.mem_cons_of_mem _ hw, hg⟩

end

/-- A loop with no accumulator keeps a predicate `Q k` of the state that moves one position
on per step, when `Q` is monotone in the position. Each step keeps the uncached box. -/
theorem forIn_state_count [Preset] [HasherTag] {δ : Type} (Q : Nat → BeaconState → Prop)
    (hmono : ∀ k t, Q k t → Q (k + 1) t) (f : δ → PUnit → HezeRun (ForInStep PUnit))
    (hk : ∀ d, KeepsUncached (f d PUnit.unit)) :
    ∀ (l : List δ), (∀ d ∈ l, ∀ k t r t', Q k t →
        (f d PUnit.unit).run (pureState t) = .ok (r, pureState t') → Q (k + 1) t') →
      ∀ k t r t', Q k t → (forIn l PUnit.unit f).run (pureState t) = .ok (r, pureState t') →
        Q (k + l.length) t' := by
  have hmono' : ∀ j k t, Q k t → Q (k + j) t := fun j => by
    induction j with
    | zero => intro k t h; exact h
    | succ j ih => intro k t h; exact hmono _ _ (ih k t h)
  intro l
  induction l with
  | nil =>
    intro _ k t r t' hq h
    rw [List.forIn_nil] at h
    have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h)
    subst e
    exact hq
  | cons d rest ih =>
    intro hf k t r t' hq h
    rw [List.forIn_cons] at h
    obtain ⟨st, t1, h1, h2⟩ := run_bind_eq_ok_pure (hk d) h
    have hq1 := hf d List.mem_cons_self k t st t1 hq h1
    cases st with
    | done b =>
      have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h2)
      subst e
      have := hmono' rest.length _ _ hq1
      have e : k + 1 + rest.length = k + (rest.length + 1) := by omega
      rw [List.length_cons, ← e]
      exact this
    | yield b =>
      cases b
      have hq2 := ih (fun d' hd' => hf d' (List.mem_cons_of_mem _ hd')) _ t1 r t' hq1 h2
      have e : k + 1 + rest.length = k + (rest.length + 1) := by omega
      rw [List.length_cons, ← e]
      exact hq2

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **The rewards and penalties keep the invariant, at the cost `rewBudget sq U S`.** `sq * sq`
is at most the total active balance, `U` bounds the sum of the effective balances, and `S`
bounds each inactivity score. -/
theorem RunInv.processRewardsAndPenalties (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    {a b : BeaconState} (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    {sq U S : Nat} (h0 : 0 < sq) (h64 : sizeOf a < 2 ^ 64)
    (hsq : sq * sq ≤ (totBal a).toNat)
    (hU : ebSum a ≤ U) (hinc : incN ≤ U)
    (hS : ∀ i, i < sizeOf a → (a.inactivityScores[i]!).toNat ≤ S)
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState a) = .ok ((), pureState b)) :
    AcKeep a b ∧ ∃ V', RunInv vals st₀ E CX CC b V' W tag Γp (B + rewBudget sq U S) := by
  unfold EthCLSpecs.Heze.processRewardsAndPenalties at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · have e := run_pure_state_eq _ _ _ _ h
    have hb := pureState_inj e
    subst hb
    exact ⟨AcKeep.refl _, V, I.mono_B (Nat.le_add_right _ _)⟩
  obtain ⟨fd, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hfd, rfl⟩ := liftErr_run_ok_spec h1
  obtain ⟨ip, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hip, rfl⟩ := liftErr_run_ok_spec h2
  obtain ⟨hlen, hmem⟩ := except_mapM_ok _ _ _ hfd
  -- Each pass reads the state, applies one pair of delta arrays, and writes the result
  -- (`keepsUncached_processRewardsAndPenalties`).
  obtain ⟨⟨⟩, t, h2, h⟩ := run_bind_eq_ok_pure
    (EthCLLib.Proofs.keepsUncached_forIn_list _ (fun x _ => by
      rcases x with ⟨rewards, penalties⟩
      refine EthCLLib.Proofs.keepsUncached_get_bind (fun v => ?_)
      refine EthCLLib.Proofs.returnsUncachedFrom_bind (returnsUncached_applyDeltas _ _ _)
        (fun w w' => ?_)
      exact EthCLLib.Proofs.keepsUncachedFrom_bind (EthCLLib.Proofs.keepsUncachedFrom_set w' w)
        (fun _ w'' => EthCLLib.Proofs.keepsUncachedFrom_pure w'' _)) _ _) h
  -- The flag loop: each pair moves at most `flagBudget sq U`.
  let Q : Nat → BeaconState → Prop := fun k t =>
    t = { a with balances := t.balances } ∧ t.balances.val.size = a.balances.val.size ∧
      moveN vals st₀ E a t ≤ k * flagBudget sq U
  have hloop := forIn_state_count Q
    (fun k t ⟨q1, q2, q3⟩ => ⟨q1, q2, Nat.le_trans q3 (Nat.mul_le_mul_right _ (Nat.le_succ k))⟩) _
    (fun x => by
      rcases x with ⟨rewards, penalties⟩
      refine EthCLLib.Proofs.keepsUncached_get_bind (fun v => ?_)
      refine EthCLLib.Proofs.returnsUncachedFrom_bind (returnsUncached_applyDeltas _ _ _)
        (fun w w' => ?_)
      exact EthCLLib.Proofs.keepsUncachedFrom_bind (EthCLLib.Proofs.keepsUncachedFrom_set w' w)
        (fun _ w'' => EthCLLib.Proofs.keepsUncachedFrom_pure w'' _)) fd
    (fun x hx k t r t' ⟨q1, q2, q3⟩ hb => by
      have hb := run_get_bind_eq_ok _ _ _ hb
      obtain ⟨z, s3, h3, hb⟩ :=
        run_bind_eq_ok_ret (EthCLSpecs.Proofs.Heze.returnsUncached_applyDeltas _ _ _) hb
      obtain ⟨hm, hz, hzs⟩ := applyDeltas_move vals hnd st₀ E _ _ t _ h3
      obtain ⟨⟨⟩, s4, h4, hb⟩ := run_bind_eq_ok _ _ _ _ hb
      have e4 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h4
      subst e4
      have e5 := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ hb)
      subst e5
      obtain ⟨f, -, hf⟩ := hmem x hx
      have hv : t.validators = a.validators := by rw [q1]
      have hbud := flagPair_sum_le a f x.fst x.snd hf h0 h64 hsq hU hinc
      rw [← hv] at hbud
      refine ⟨by rw [hz, q1], by rw [hzs, q2], ?_⟩
      have := moveN_triangle vals st₀ E a t t'
      rw [Nat.succ_mul]
      omega)
    0 a _ _ ⟨rfl, rfl, by rw [moveN_self]; exact Nat.zero_le _⟩ h2
  obtain ⟨q1, q2, q3⟩ := hloop
  rw [hlen, List.length_range, Nat.zero_add] at q3
  -- The inactivity penalties.
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨z, s3, h3, h⟩ :=
    run_bind_eq_ok_ret (EthCLSpecs.Proofs.Heze.returnsUncached_applyDeltas _ _ _) h
  obtain ⟨hm, hz, hzs⟩ := applyDeltas_move vals hnd st₀ E _ _ t _ h3
  have e := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h
  have hzb : b = z := pureState_inj e
  subst hzb
  have hv : t.validators = a.validators := by rw [q1]
  have hbud := inactPair_sum_le a hip hS hU
  simp only [SizzLean.Proofs.view_uncachedBox] at hm
  rw [hv] at hm
  have hm' : moveN vals st₀ E t b ≤ inactBudget U S := Nat.le_trans hm hbud
  have hmv : moveN vals st₀ E a b ≤ rewBudget sq U S := by
    have := moveN_triangle vals st₀ E a t b
    unfold rewBudget
    omega
  have hb1 : b = { a with balances := b.balances } := by rw [hz, q1]
  have hb2 : b.balances.val.size = a.balances.val.size := by rw [hzs, q2]
  have hvb : b.validators = a.validators := by rw [hb1]
  have hsl : b.slot = a.slot := by rw [hb1]
  exact ⟨AcKeep.of_validators hsl hvb, _, I.balanceStep (by rw [hb1]) hb2 hmv⟩

end

/-! ## The inactivity scores -/

section
variable [Preset] [HasherTag]

/-- The inactivity score of index `i`. -/
def scoreN (u : BeaconState) (i : Nat) : Nat := (u.inactivityScores[i]!).toNat

omit [Preset] [HasherTag] in
theorem sub_umin_le (x y : UInt64) : (x - umin y x).toNat ≤ x.toNat := by
  have hle : umin y x ≤ x := by
    rw [UInt64.le_iff_toNat_le, umin_toNat]; exact Nat.min_le_right _ _
  rw [UInt64.toNat_sub_of_le _ _ hle]
  exact Nat.sub_le _ _

omit [Preset] [HasherTag] in
theorem scores_set!_le {cap : Nat} (xs : SizzLean.Repr.SSZList UInt64 cap) (i : Nat) (v : UInt64) :
    (xs.set! i v)[i]!.toNat ≤ max v.toNat xs[i]!.toNat := by
  by_cases hi : i < xs.size
  · rw [SizzLean.Proofs.sszListSet!_getElem!_self _ _ _ hi]; exact Nat.le_max_left _ _
  · rw [SizzLean.Proofs.sszListSet!_eq_of_size_le _ _ _ (by omega)]; exact Nat.le_max_right _ _

/-- A loop of score writes, each at a distinct index and each raising its score by at most
`c`, keeps every score at most `S + c` when each score starts at most `S`. -/
theorem score_loop_le (g : ValidatorIndex → PUnit → HezeRun (ForInStep PUnit))
    (hk : ∀ d, KeepsUncached (g d PUnit.unit)) {a : BeaconState} {S c : Nat}
    (hg : ∀ vi t r t', (g vi PUnit.unit).run (pureState t) = .ok (r, pureState t') →
      r = .yield PUnit.unit ∧ t' = { t with inactivityScores := t'.inactivityScores } ∧
        (∀ i, i ≠ vi.toNat → scoreN t' i = scoreN t i) ∧
        scoreN t' vi.toNat ≤ scoreN t vi.toNat + c) :
    ∀ (l : List ValidatorIndex), l.Nodup → ∀ t : BeaconState,
      t = { a with inactivityScores := t.inactivityScores } →
      (∀ vi ∈ l, scoreN t vi.toNat ≤ S) → (∀ i, scoreN t i ≤ S + c) →
      ∀ r t', (forIn l PUnit.unit g).run (pureState t) = .ok (r, pureState t') →
      t' = { a with inactivityScores := t'.inactivityScores } ∧ ∀ i, scoreN t' i ≤ S + c := by
  intro l
  induction l with
  | nil =>
    intro _ t ht _ hc r t' h
    rw [List.forIn_nil] at h
    have e := pureState_inj (run_pure_state_eq _ _ _ _ h)
    subst e
    exact ⟨ht, hc⟩
  | cons x rest ih =>
    intro hnd t ht hl hc r t' h
    rw [List.forIn_cons] at h
    obtain ⟨st, t1, h1, h⟩ := run_bind_eq_ok_pure (hk x) h
    obtain ⟨rfl, ht1, hne, hself⟩ := hg x t st t1 h1
    dsimp only at h
    have hx : x ∉ rest := (List.nodup_cons.mp hnd).1
    have h1 : ∀ vi ∈ rest, scoreN t1 vi.toNat ≤ S := fun vi hvi => by
      have hvx : vi.toNat ≠ x.toNat := fun e => hx (by
        have := UInt64.toNat_inj.mp e; rw [← this]; exact hvi)
      rw [hne _ hvx]; exact hl vi (List.mem_cons_of_mem _ hvi)
    have h2 : ∀ i, scoreN t1 i ≤ S + c := fun i => by
      by_cases hi : i = x.toNat
      · subst hi; have := hl x List.mem_cons_self; omega
      · rw [hne _ hi]; exact hc i
    exact ih (List.nodup_cons.mp hnd).2 t1 (by rw [ht1, ht]) h1 h2 r t' h

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [CryptoBackend] in
/-- **The inactivity updates raise each score by at most the bias**, and keep every other
field. -/
theorem processInactivityUpdates_scores (a b : BeaconState) {S : Nat}
    (hS : ∀ i, scoreN a i ≤ S) (h64 : sizeOf a ≤ 2 ^ 64)
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState a) = .ok ((), pureState b)) :
    b = { a with inactivityScores := b.inactivityScores } ∧
      ∀ i, scoreN b i ≤ S + EthCLSpecs.Heze.Const.inactivityScoreBias.toNat := by
  unfold EthCLSpecs.Heze.processInactivityUpdates at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  have hstay : ∀ {x : HezeRun Unit}, x = pure () → x.run (pureState a) = .ok ((), pureState b) →
      b = { a with inactivityScores := b.inactivityScores } ∧
        ∀ i, scoreN b i ≤ S + EthCLSpecs.Heze.Const.inactivityScoreBias.toNat := by
    intro x hx h
    subst hx
    have hb := pureState_inj (run_pure_state_eq _ _ _ _ h)
    subst hb
    exact ⟨rfl, fun i => Nat.le_trans (hS i) (Nat.le_add_right _ _)⟩
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hstay rfl h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hstay rfl h
  obtain ⟨mt, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := liftErr_run_ok_spec h1
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e := run_pure_state_eq _ _ _ _ h
  subst e
  rw [← Array.forIn_toList] at h2
  have hnd : (EthCLSpecs.Heze.getEligibleValidatorIndices (pureState a)).toList.Nodup :=
    EthCLLib.Proofs.indicesWhere_nodup _ _ (by unfold sizeOf at h64; simpa using h64)
  -- One step reads the score, raises it by at most the bias, and writes it back.
  have hL := score_loop_le (a := a) (S := S)
    (c := EthCLSpecs.Heze.Const.inactivityScoreBias.toNat) _ ?hk ?step _ hnd a rfl
    (fun vi _ => hS _) (fun i => Nat.le_trans (hS i) (Nat.le_add_right _ _)) _ _ h2
  case hk =>
    intro d
    keeps_uncached
  case step =>
      intro vi t r t' hb
      have hb := run_get_bind_eq_ok _ _ _ hb
      obtain ⟨cur, s1, h1, hb⟩ := run_bind_eq_ok _ _ _ _ hb
      obtain ⟨hcur, rfl⟩ := sszGetIdx_run_ok h1
      obtain ⟨cur2, s2, h2, hb⟩ := run_bind_eq_ok _ _ _ _ hb
      have hc2 : cur2.toNat ≤ cur.toNat + EthCLSpecs.Heze.Const.inactivityScoreBias.toNat ∧
          s2 = pureState t := by
        split at h2
        · have e1 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h2
          subst e1
          exact ⟨Nat.le_trans (sub_umin_le _ _) (Nat.le_add_right _ _),
            run_pure_state_eq _ _ _ _ h2⟩
        · obtain ⟨e2, e1, -⟩ := checkedAdd_run_ok h2
          subst e1
          refine ⟨?_, e2⟩
          rw [UInt64.toNat_add]
          exact Nat.mod_le _ _
      obtain ⟨hc2, rfl⟩ := hc2
      obtain ⟨leak, s3, h3, hb⟩ := run_bind_eq_ok _ _ _ _ hb
      obtain ⟨-, rfl⟩ := liftErr_run_ok_spec h3
      obtain ⟨⟨⟩, s4, h4, hb⟩ := run_bind_eq_ok _ _ _ _ hb
      have e4 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h4
      subst e4
      have e5 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
      have e6 := run_pure_state_eq _ _ _ _ hb
      subst e5
      let cur3 : UInt64 := if (!leak) = true then
        cur2 - umin EthCLSpecs.Heze.Const.inactivityScoreRecoveryRate cur2 else cur2
      have ht' : t' = { t with inactivityScores := t.inactivityScores.set! vi.toNat cur3 } :=
        pureState_inj e6
      subst ht'
      have hcur' : t.inactivityScores[vi.toNat]! = cur :=
        sszList_getElem!_of_some (xs := t.inactivityScores) hcur
      refine ⟨rfl, rfl, fun i hi =>
        congrArg UInt64.toNat (SizzLean.Proofs.sszListSet!_getElem!_ne _ _ _ _ (Ne.symm hi)),
        Nat.le_trans (scores_set!_le _ _ _) (Nat.max_le.mpr ⟨?_, Nat.le_add_right _ _⟩)⟩
      show _ ≤ (t.inactivityScores[vi.toNat]!).toNat + _
      rw [hcur']
      show (if (!leak) = true then
        cur2 - umin EthCLSpecs.Heze.Const.inactivityScoreRecoveryRate cur2 else cur2).toNat ≤ _
      split
      · exact Nat.le_trans (sub_umin_le _ _) hc2
      · exact hc2
  exact hL

end

end EthCLSpecs.Proofs.Heze
