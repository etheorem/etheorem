import EthCLSpecs.Proofs.Heze.DriftOps
import EthCLSpecs.Proofs.Heze.DriftSync
import EthCLSpecs.Proofs.Heze.LatestMessages
import EthCLSpecs.Proofs.Heze.Participation

/-!
# `EthCLSpecs.Proofs.Heze.DriftAttest`: the move of one attestation

`process_attestation` sets participation flags and pays the proposer one reward. The flags and
the builder payment weight lie outside `econView`, so the reward is the only move. The reward
sums, over the attesting indices and their new flags, a base reward times a flag weight, and
divides by the proposer denominator.

This module bounds the reward by a count. `get_attesting_indices` collects one index per set
bit that it reads, at increasing positions of the aggregation bits, so it collects at most as
many indices as the bitlist holds (`getAttestingIndices_size_le`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei Attestation
  getAttestingIndices getBeaconCommittee)

/-- A loop over `range' s n` in `Except` keeps a predicate `P k` of the position `k` and the
accumulator, when `P` is monotone in the position and each body run moves it one position
on. -/
theorem except_forIn_range'_inv {β ε : Type} (P : Nat → β → Prop)
    (f : Nat → β → Except ε (ForInStep β)) (hmono : ∀ k k' b, k ≤ k' → P k b → P k' b) :
    ∀ (n s : Nat), (∀ k, s ≤ k → k < s + n → ∀ b r, P k b → f k b = .ok r → P (k + 1) r.value) →
      ∀ (init r : β), P s init → forIn (List.range' s n) init f = .ok r → P (s + n) r := by
  intro n
  induction n with
  | zero =>
    intro s _ init r hinit h
    rw [List.range'_zero, List.forIn_nil] at h
    cases h
    exact hinit
  | succ n ih =>
    intro s hf init r hinit h
    rw [List.range'_succ, List.forIn_cons] at h
    cases hfs : f s init with
    | error e =>
      rw [hfs] at h
      cases h
    | ok st =>
      rw [hfs] at h
      have hst := hf s (Nat.le_refl _) (by omega) init st hinit hfs
      cases st with
      | done b =>
        cases h
        exact hmono _ _ _ (by omega) hst
      | yield b =>
        have := ih (s + 1) (fun k h1 h2 => hf k (by omega) (by omega)) b r hst h
        rwa [show s + 1 + n = s + (n + 1) by omega] at this

section
variable [Preset] [HasherTag]

/-- **`get_attesting_indices` collects at most as many indices as the aggregation bits
hold.** -/
theorem getAttestingIndices_size_le (st : BeaconState) (att : Attestation)
    (A : Array ValidatorIndex) (h : getAttestingIndices (pureState st) att = .ok A) :
    A.size ≤ att.aggregationBits.val.size := by
  unfold getAttestingIndices at h
  dsimp only at h
  -- The invariant of the outer loop: the output is no longer than the offset or the bits.
  let Q : MProd Nat (Array ValidatorIndex) → Prop := fun r =>
    r.snd.size ≤ r.fst ∧ r.snd.size ≤ att.aggregationBits.val.size
  obtain ⟨r, hloop, hfin⟩ := except_bind_eq_ok h
  have hA : A = r.snd := by
    obtain ⟨o, out⟩ := r
    cases hfin
    rfl
  subst hA
  rw [← Array.forIn_toList] at hloop
  refine (except_forIn_list_inv Q _ _ ?_ _ _ ⟨Nat.le_refl _, Nat.zero_le _⟩ hloop).2
  -- One committee: the inner loop over its positions.
  intro ci _ b st' hb hrun
  -- `getBeaconCommittee` returns the committee `c`. The size bound holds for every `c`.
  obtain ⟨c, -, hrun⟩ := except_bind_eq_ok hrun
  obtain ⟨out, hinner, hrun⟩ := except_bind_eq_ok hrun
  have hst' : st'.value = ⟨b.fst + c.size, out⟩ := by
    cases hrun
    rfl
  rw [hst']
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hinner
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hinner
  have := except_forIn_range'_inv
    (fun k out => out.size ≤ b.fst + k ∧ out.size ≤ att.aggregationBits.val.size) _
    (fun k k' o hk ho => ⟨by omega, ho.2⟩) _ 0 ?_ _ _ ⟨by have := hb.1; omega, hb.2⟩ hinner
  · simp only [Nat.zero_add] at this
    exact this
  intro k _ _ o st'' ho hbody
  obtain ⟨bit, hbit, hbody⟩ := except_bind_eq_ok hbody
  -- A push follows a read of the bit at `offset + k`, which lies inside the bitlist.
  split at hbody
  · cases hbody
    have hin : b.fst + k < att.aggregationBits.val.size := by
      unfold bitlistGetIdx at hbit
      revert hbit
      cases hk : att.aggregationBits.val[b.fst + k]? with
      | none => intro hbit; cases hbit
      | some _ => intro _; exact (Array.getElem?_eq_some_iff.mp hk).1
    simp only [ForInStep.value, Array.size_push]
    omega
  · cases hbody
    simp only [ForInStep.value]
    exact ⟨by have := ho.1; omega, ho.2⟩

end

/-! ## The bound of one reward -/

/-- The sum of the three flag weights. -/
def wSum : Nat := EthCLSpecs.Heze.Const.timelySourceWeight +
  EthCLSpecs.Heze.Const.timelyTargetWeight + EthCLSpecs.Heze.Const.timelyHeadWeight

/-- Each flag weight is at most the sum of the three. -/
theorem flagWeight_le (k : Nat) : EthCLSpecs.Heze.Const.participationFlagWeights[k]! ≤ wSum := by
  unfold wSum
  rcases k with _ | _ | _ | k <;>
    simp [EthCLSpecs.Heze.Const.participationFlagWeights] <;> omega

section
variable [Preset] [HasherTag]

/-- The bound of one base reward, when `s * s` is at most the total active balance. -/
def brMax (s : Nat) : Nat :=
  maxEBN / incN * (incN * EthCLSpecs.Heze.Const.baseRewardFactor / s)

/-- The divisor of the proposer reward of an attestation. -/
def attDenom : Nat :=
  (EthCLSpecs.Heze.Const.weightDenominator - EthCLSpecs.Heze.Const.proposerWeight) *
    EthCLSpecs.Heze.Const.weightDenominator / EthCLSpecs.Heze.Const.proposerWeight

/-- The bound of the move of one attestation: the largest count of attesting indices, three
flags each, at the largest base reward and flag weight. -/
def attBudget (s : Nat) : Nat :=
  EthCLSpecs.Heze.Const.maxValidatorsPerCommittee * EthCLSpecs.Heze.Const.maxCommitteesPerSlot *
    (3 * (brMax s * wSum)) / attDenom

/-- **A base reward is at most `brMax s`.** A successful read found the validator, read the
base reward per increment without a fault, and formed the checked product without an
overflow. -/
theorem getBaseReward_le (C : DriftConsts) (a : BeaconState) (hshape : ShapeOK a) {s : Nat}
    (hs0 : 0 < s) (hs : s * s ≤ (totBal a).toNat)
    (vi : ValidatorIndex) (br : Gwei)
    (h : EthCLSpecs.Heze.getBaseReward (pureState a) vi = .ok br) : br.toNat ≤ brMax s := by
  unfold EthCLSpecs.Heze.getBaseReward at h
  obtain ⟨v, hv, h⟩ := except_bind_eq_ok h
  obtain ⟨p, hp, h⟩ := except_bind_eq_ok h
  obtain ⟨rfl, hbrN⟩ := except_checkedMul_ok h
  rw [hbrN, UInt64.toNat_div]
  unfold sszGetIdx liftErr at hv
  split at hv
  · rename_i y hy
    injection hv with hv
    subst hv
    have hy' : a.validators.val[vi.toNat]? = some y := hy
    have hi : vi.toNat < sizeOf a := (Array.getElem?_eq_some_iff.mp hy').1
    have heb : y.effectiveBalance.toNat ≤ maxEBN := by
      have h1 := hshape.ebLe _ hi
      unfold ebN maxN at h1
      rw [hy'] at h1
      exact Nat.le_trans h1 (C.maxLe y)
    unfold brMax
    exact Nat.mul_le_mul (Nat.div_le_div_right heb) (brpi_le a hs0 hs hp)
  · cases hv

end

/-- `moveN` from a state reads its capped balances alone. -/
theorem moveN_congr_left [Preset] (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat)
    {a a' : BeaconState} (b : BeaconState) (h : ∀ i, capN a' i = capN a i) :
    moveN vals st₀ E a' b = moveN vals st₀ E a b := by
  unfold moveN
  simp only [h]

/-! ## The run of one attestation -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The state box of a loop accumulator: the uncached box of a value with the reads and the
slot of `a`. -/
def AccOK (a : BeaconState) (x : State) : Prop :=
  ∃ t, x = pureState t ∧ econView t = econView a ∧ t.slot = a.slot

/-- **One attestation moves the capped balances by at most `attBudget s`**, and it writes no
other read of the invariant. -/
theorem processAttestation_move (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) (E : Nat) (C : DriftConsts) (att : Attestation) (a b : BeaconState)
    (hshape : ShapeOK a) {s : Nat} (hs0 : 0 < s) (hs : s * s ≤ (totBal a).toNat)
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState a) = .ok ((), pureState b)) :
    econView b = econView { a with balances := b.balances } ∧ b.slot = a.slot ∧
      b.balances.val.size = a.balances.val.size ∧ moveN vals st₀ E a b ≤ attBudget s := by
  unfold EthCLSpecs.Heze.processAttestation at h
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  -- The checks and the reads before the loop. The loop starts from the box of `a`.
  -- Each read keeps the uncached box, so the threaded state stays a plain state.
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  -- The flag list, the indices of the indexed attestation, its list, and its validity read.
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨idx, _, hidx, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨r, _, hr, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  have hL := getAttestingIndices_size_le _ att idx (liftErr_run_ok_spec hidx).1
  rw [← Array.forIn_toList] at hr
  -- The loop over the attesting indices: the box stays, and the numerator grows by at most
  -- three flags per index.
  have hloop := forIn_move_le
    (fun x y : MProd Gwei (MProd State Gwei) => y.1.toNat - x.1.toNat)
    (fun _ _ _ => by dsimp only; omega) (fun _ => Nat.sub_self _)
    (fun x : MProd Gwei (MProd State Gwei) => AccOK a x.2.1)
    (fun _ => 3 * (brMax s * wSum)) _ idx.toList ?step _ _ _ _ ⟨a, rfl, rfl, rfl⟩ hr
  case step =>
    intro vi _ rr _ _ stp hP hb
    obtain ⟨r1, _, hin, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hin
    have hin2 := forIn_move_le
      (fun x y : MProd Gwei (MProd State Bool) => y.1.toNat - x.1.toNat)
      (fun _ _ _ => by dsimp only; omega) (fun _ => Nat.sub_self _)
      (fun x : MProd Gwei (MProd State Bool) => AccOK a x.2.1)
      (fun _ => brMax s * wSum) _ _ ?fstep _ _ _ _ hP hin
    case fstep =>
      intro k _ q _ _ stq hq hbq
      -- A flag outside the list leaves the accumulator.
      rcases EthCLLib.Proofs.run_ite_eq_ok hbq with ⟨-, hbq⟩ | ⟨-, hbq⟩
      rotate_left
      · obtain ⟨_, _, -, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
        have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbq
        subst this
        exact ⟨hq, by simp only [ForInStep.value]; omega⟩
      -- A flag in the list reads the entry. A new flag adds a checked reward.
      rcases EthCLLib.Proofs.run_ite_eq_ok hbq with ⟨-, hbq⟩ | ⟨-, hbq⟩ <;>
      · obtain ⟨_, _, -, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
        rcases EthCLLib.Proofs.run_ite_eq_ok hbq with ⟨-, hbq⟩ | ⟨-, hbq⟩
        · obtain ⟨br, _, hbr, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
          obtain ⟨rw', _, hrw, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
          obtain ⟨pn', _, hpn, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
          obtain ⟨_, _, -, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
          have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbq
          subst this
          have hbr' := getBaseReward_le C a hshape hs0 hs vi br (liftErr_run_ok_spec hbr).1
          obtain ⟨-, rfl, hmul⟩ := checkedMul_run_ok hrw
          obtain ⟨-, rfl, hadd⟩ := checkedAdd_run_ok hpn
          obtain ⟨t, ht, he, hsl⟩ := hq
          refine ⟨?_, ?_⟩
          · simp only [ForInStep.value]
            rw [ht]
            split <;> exact ⟨_, rfl, he, hsl⟩
          · simp only [ForInStep.value]
            rw [UInt64.toNat_add, Nat.mod_eq_of_lt hadd, hmul]
            have hof : ∀ n : Nat, (UInt64.ofNat n).toNat ≤ n := fun n => by
              rw [UInt64.toNat_ofNat']; exact Nat.mod_le _ _
            have := Nat.mul_le_mul hbr' (Nat.le_trans (hof _) (flagWeight_le k))
            omega
        · obtain ⟨_, _, -, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
          have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbq
          subst this
          exact ⟨hq, by simp only [ForInStep.value]; omega⟩
    obtain ⟨hP1, hM1⟩ := hin2
    have h3 : ((List.range' [:3].start [:3].size [:3].step).map fun _ => brMax s * wSum).sum =
        3 * (brMax s * wSum) := by
      simp [Std.Legacy.Range.size, List.range']
      omega
    rw [h3] at hM1
    -- The weight step reads the validator and adds a checked sum, or it skips.
    rcases EthCLLib.Proofs.run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
    · obtain ⟨_, _, -, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
      obtain ⟨_, _, -, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
      obtain ⟨_, _, -, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
      subst this
      exact ⟨hP1, by simp only [ForInStep.value]; omega⟩
    · obtain ⟨_, _, -, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
      subst this
      exact ⟨hP1, by simp only [ForInStep.value]; omega⟩
  obtain ⟨⟨t, ht, he, hsl⟩, hMr⟩ := hloop
  -- The payment write, then the proposer reward.
  rw [ht] at h
  obtain ⟨x, _, hinc, hset⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  have e9 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
  obtain ⟨-, hmx, hx, hsz⟩ := moveN_increaseBalance vals hnd st₀ E _ _ _ _ hinc
  have hb : b = x := congrArg SizzLean.Cache.SSZ.Box.view e9
  subst hb
  simp only [econView, Prod.mk.injEq] at he
  obtain ⟨hv, hbal, he3⟩ := he
  refine ⟨?_, by rw [hx]; exact hsl, by rw [hsz]; exact congrArg (·.val.size) hbal, ?_⟩
  · rw [congrArg econView hx]
    simp only [econView, Prod.mk.injEq, true_and]
    exact ⟨hv, he3⟩
  · -- The payment write keeps the capped balances of `a`.
    refine Nat.le_trans (Nat.le_trans (Nat.le_of_eq ?_) hmx) ?_
    · exact (moveN_congr_left vals st₀ E b fun i => by
        unfold capN balN maxN
        simp only [uncached_ofValue_view]
        rw [hv, hbal]).symm
    -- The numerator: at most three flags per attesting index, and at most as many indices as
    -- the aggregation bits hold.
    dsimp only at hMr
    simp only [List.map_const', List.sum_replicate_nat, Array.length_toList] at hMr
    have hcap' : idx.size ≤ EthCLSpecs.Heze.Const.maxValidatorsPerCommittee *
        EthCLSpecs.Heze.Const.maxCommitteesPerSlot :=
      Nat.le_trans hL att.aggregationBits.property
    have hnum := Nat.le_trans hMr (Nat.mul_le_mul_right (3 * (brMax s * wSum)) hcap')
    -- The reward is a `Gwei` quotient by the proposer denominator, a small constant.
    rw [UInt64.toNat_div, EthCLLib.Proofs.toNat_ofNat_lt64 (by decide)]
    exact Nat.div_le_div_right hnum

end

end EthCLSpecs.Proofs.Heze
