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
  let Q : Array ValidatorIndex × Nat → Prop := fun r =>
    r.fst.size ≤ r.snd ∧ r.fst.size ≤ att.aggregationBits.val.size
  obtain ⟨r, hloop, hfin⟩ := except_bind_eq_ok h
  have hA : A = r.fst := by
    obtain ⟨out, o⟩ := r
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
  have hst' : st'.value = (out, b.snd + c.size) := by
    cases hrun
    rfl
  rw [hst']
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hinner
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hinner
  have := except_forIn_range'_inv
    (fun k out => out.size ≤ b.snd + k ∧ out.size ≤ att.aggregationBits.val.size) _
    (fun k k' o hk ho => ⟨by omega, ho.2⟩) _ 0 ?_ _ _ ⟨by have := hb.1; omega, hb.2⟩ hinner
  · simp only [Nat.zero_add] at this
    exact this
  intro k _ _ o st'' ho hbody
  obtain ⟨bit, hbit, hbody⟩ := except_bind_eq_ok hbody
  -- A push follows a read of the bit at `offset + k`, which lies inside the bitlist.
  split at hbody
  · cases hbody
    have hin : b.snd + k < att.aggregationBits.val.size := by
      unfold bitlistGetIdx sszGetIdx at hbit
      -- A read past the end returns `none`, and the run rejects.
      refine Nat.lt_of_not_le fun hge => ?_
      have hn : IdxRead.get? att.aggregationBits (b.snd + k) = none :=
        Array.getElem?_eq_none hge
      rw [hn] at hbit
      cases hbit
    simp only [ForInStep.value, Array.size_push]
    omega
  · cases hbody
    simp only [ForInStep.value]
    exact ⟨by have := ho.1; omega, ho.2⟩

omit [Preset] [HasherTag] in
/-- An `assert` in `Except` that passed: its test holds, and the rest ran. -/
theorem except_assert_bind_eq_ok {ε β : Type} {c : Prop} [Decidable c] {e : ε}
    {k : PUnit → Except ε β} {r : β}
    (h : ((if c then pure PUnit.unit else throw e : Except ε PUnit) >>= k) = .ok r) :
    c ∧ k PUnit.unit = .ok r := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact ⟨hc, h⟩
  · rw [ite_eq_right hc] at h
    cases h

omit [Preset] [HasherTag] in
/-- A loop in `Except` whose each step adds at most `m` to the measure `g` adds at most
`m` per element. -/
theorem except_forIn_list_measure_le {α β ε : Type} (g : β → Nat) (m : Nat)
    (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b r, f a b = .ok r → g r.value ≤ g b + m) :
    ∀ (l : List α) (init r : β), forIn l init f = .ok r → g r ≤ g init + l.length * m := by
  intro l
  induction l with
  | nil =>
    intro init r h
    rw [List.forIn_nil] at h
    cases h
    omega
  | cons a rest ih =>
    intro init r h
    rw [List.forIn_cons] at h
    cases hfa : f a init with
    | error e =>
      rw [hfa] at h
      cases h
    | ok st =>
      rw [hfa] at h
      have hst := hf a init st hfa
      cases st with
      | done b =>
        cases h
        simp only [ForInStep.value] at hst
        simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega
      | yield b =>
        have := ih b r h
        simp only [ForInStep.value] at hst
        simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega

omit [Preset] [HasherTag] in
/-- The set bit positions of a `Bitvector n` number at most `n`. -/
theorem trueIndices_size_le {n : Nat} (bv : Bitvector n) :
    (Bitvector.trueIndices bv).size ≤ n := by
  -- Each step pushes at most one position.
  have key : ∀ (l : List Nat) (init : Array Nat),
      (forIn (m := Id) l init (fun i r =>
        if bitGet bv i = true then pure (ForInStep.yield (r.push i))
        else pure (ForInStep.yield r))).run.size ≤ init.size + l.length := by
    intro l
    induction l with
    | nil =>
      intro init
      exact Nat.le_refl _
    | cons i rest ih =>
      intro init
      rw [List.forIn_cons]
      by_cases hb : bitGet bv i = true
      · rw [ite_eq_left hb]
        have := ih (init.push i)
        rw [Array.size_push] at this
        simp only [List.length_cons]
        exact Nat.le_trans this (by omega)
      · rw [ite_eq_right hb]
        have := ih init
        simp only [List.length_cons]
        exact Nat.le_trans this (by omega)
  unfold Bitvector.trueIndices
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using
    key (List.range' 0 n) #[]

/-- A committee that `compute_committee` returns is no larger than its index list. The run
asserts `stop ≤ len`, and the slice runs from `start` to `stop`. -/
theorem computeCommittee_size_le (indices : Array ValidatorIndex)
    (seed : EthCLSpecs.Heze.Bytes32) (k c : Nat) {out : Array ValidatorIndex}
    (h : (EthCLSpecs.Heze.computeCommittee indices seed k c :
      Except StateTransitionError (Array ValidatorIndex)) = .ok out) :
    out.size ≤ indices.size := by
  unfold EthCLSpecs.Heze.computeCommittee at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨lo, -, h⟩ := except_bind_eq_ok h
  split at h
  · cases h
  obtain ⟨next, -, h⟩ := except_bind_eq_ok h
  obtain ⟨hi, -, h⟩ := except_bind_eq_ok h
  split at h
  · cases h
    simp
  obtain ⟨-, h⟩ := except_assert_bind_eq_ok h
  obtain ⟨perm, -, h⟩ := except_bind_eq_ok h
  obtain ⟨hstop, h⟩ := except_assert_bind_eq_ok h
  cases h
  simp only [Array.size_map, Array.size_range]
  omega

/-- A committee that `get_beacon_committee` returns is no larger than the registry. -/
theorem getBeaconCommittee_size_le (st : BeaconState) (slot : EthCLSpecs.Heze.Slot) (idx : Nat)
    {c : Array ValidatorIndex} (h : getBeaconCommittee (pureState st) slot idx = .ok c) :
    c.size ≤ st.validators.val.size := by
  unfold getBeaconCommittee at h
  dsimp only at h
  -- The committee count, then the index check.
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  split at h
  · cases h
  -- The active set, the seed, then the committee number and the count.
  obtain ⟨active, hactive, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  refine Nat.le_trans (computeCommittee_size_le _ _ _ _ h) ?_
  rw [getActiveValidatorIndices_eq_of_ok hactive]
  unfold EthCLSpecs.Heze.activeValidatorIndicesOf
  exact EthCLLib.Proofs.indicesWhere_size_le _ _

/-- **`get_attesting_indices` collects at most `MAX_COMMITTEES_PER_SLOT` committees of
indices.** The committee bits name at most that many committees, and each committee is no
larger than the registry. At v1.7.0-beta.4 the aggregation bits are a progressive bitlist
(EIP-7688), so their length gives no bound of its own. -/
theorem getAttestingIndices_size_le_registry (st : BeaconState) (att : Attestation)
    (A : Array ValidatorIndex) (h : getAttestingIndices (pureState st) att = .ok A) :
    A.size ≤ EthCLSpecs.Heze.Const.maxCommitteesPerSlot * st.validators.val.size := by
  unfold getAttestingIndices at h
  dsimp only at h
  obtain ⟨r, hloop, hfin⟩ := except_bind_eq_ok h
  have hA : A = r.fst := by
    obtain ⟨out, o⟩ := r
    cases hfin
    rfl
  subst hA
  rw [← Array.forIn_toList] at hloop
  have hm := except_forIn_list_measure_le (fun r : Array ValidatorIndex × Nat => r.fst.size)
    st.validators.val.size _ ?_ _ _ _ hloop
  · have hL : (EthCLSpecs.Heze.getCommitteeIndices att.committeeBits).toList.length ≤
        EthCLSpecs.Heze.Const.maxCommitteesPerSlot := by
      rw [Array.length_toList]
      exact trueIndices_size_le _
    simp only [Array.size_empty, Nat.zero_add] at hm
    exact Nat.le_trans hm (Nat.mul_le_mul_right _ hL)
  -- One committee: the inner loop pushes at most one index per position.
  intro ci b st' hrun
  obtain ⟨c, hc, hrun⟩ := except_bind_eq_ok hrun
  obtain ⟨out, hinner, hrun⟩ := except_bind_eq_ok hrun
  have hst' : st'.value = (out, b.snd + c.size) := by
    cases hrun
    rfl
  rw [hst']
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hinner
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hinner
  have := except_forIn_range'_inv (fun k out => out.size ≤ b.fst.size + k) _
    (fun k k' o hk ho => by omega) _ 0 ?_ _ _ (by omega) hinner
  · simp only [Nat.zero_add] at this
    exact Nat.le_trans this (Nat.add_le_add_left (getBeaconCommittee_size_le st _ _ hc) _)
  intro k _ _ o st'' ho hbody
  obtain ⟨bit, -, hbody⟩ := except_bind_eq_ok hbody
  split at hbody
  · cases hbody
    simp only [ForInStep.value, Array.size_push]
    omega
  · cases hbody
    simp only [ForInStep.value]
    omega

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

/-- The bound of the move of one attestation on a registry of at most `n` validators: the
largest count of attesting indices, three flags each, at the largest base reward and flag
weight. An attestation names at most `MAX_COMMITTEES_PER_SLOT` committees, each no larger
than the registry (`getAttestingIndices_size_le_registry`). -/
def attBudget (s n : Nat) : Nat :=
  EthCLSpecs.Heze.Const.maxCommitteesPerSlot * n * (3 * (brMax s * wSum)) / attDenom

omit [HasherTag] in
/-- `attBudget` grows with the registry bound. -/
theorem attBudget_mono (s : Nat) {n n' : Nat} (h : n ≤ n') : attBudget s n ≤ attBudget s n' := by
  unfold attBudget
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h))

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

/-- **One attestation moves the capped balances by at most `attBudget s n`**, for the size `n`
of the registry, and it writes no other read of the invariant. -/
theorem processAttestation_move (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) (E : Nat) (C : DriftConsts) (att : Attestation) (a b : BeaconState)
    (hshape : ShapeOK a) {s : Nat} (hs0 : 0 < s) (hs : s * s ≤ (totBal a).toNat)
    {parentSlot : EthCLSpecs.Heze.Slot}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att parentSlot).run
      (pureState a) = .ok ((), pureState b)) :
    econView b = econView { a with balances := b.balances } ∧ b.slot = a.slot ∧
      b.balances.val.size = a.balances.val.size ∧
      moveN vals st₀ E a b ≤ attBudget s a.validators.val.size := by
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
  -- The flag list, the indices of the indexed attestation, and its validity read.
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨idx, _, hidx, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨r, _, hr, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  have hL := getAttestingIndices_size_le_registry _ att idx (liftErr_run_ok_spec hidx).1
  rw [← Array.forIn_toList] at hr
  -- The loop over the attesting indices: the box stays, and the numerator grows by at most
  -- three flags per index.
  have hloop := forIn_move_le
    (fun x y : State × Gwei × Gwei => y.2.1.toNat - x.2.1.toNat)
    (fun _ _ _ => by omega) (fun _ => Nat.sub_self _)
    (fun x : State × Gwei × Gwei => AccOK a x.1)
    (fun _ => 3 * (brMax s * wSum)) _ idx.toList ?step _ _ _ _ ⟨a, rfl, rfl, rfl⟩ hr
  case step =>
    intro vi _ rr _ _ stp hP hb
    -- The body splits on the target epoch first. Each branch reads the old flags, which
    -- writes nothing, then runs the flag loop and the weight step.
    rcases EthCLLib.Proofs.run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩ <;> (
    obtain ⟨_, _, -, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
    obtain ⟨r1, _, hin, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hin
    have hin2 := forIn_move_le
      (fun x y : State × Gwei × Bool => y.2.1.toNat - x.2.1.toNat)
      (fun _ _ _ => by omega) (fun _ => Nat.sub_self _)
      (fun x : State × Gwei × Bool => AccOK a x.1)
      (fun _ => brMax s * wSum) _ _ ?_ _ _ _ _ hP hin
    rotate_left
    · intro k _ q _ _ stq hq hbq
      -- A flag outside the list leaves the accumulator.
      rcases EthCLLib.Proofs.run_ite_eq_ok hbq with ⟨-, hbq⟩ | ⟨-, hbq⟩
      rotate_left
      · have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbq
        subst this
        exact ⟨hq, by simp only [ForInStep.value]; omega⟩
      -- A flag in the list reads the entry. A new flag adds a checked reward.
      rcases EthCLLib.Proofs.run_ite_eq_ok hbq with ⟨-, hbq⟩ | ⟨-, hbq⟩ <;>
      · obtain ⟨_, _, -, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
        rcases EthCLLib.Proofs.run_ite_eq_ok hbq with ⟨-, hbq⟩ | ⟨-, hbq⟩
        · obtain ⟨br, _, hbr, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
          obtain ⟨rw', _, hrw, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
          obtain ⟨pn', _, hpn, hbq⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hbq
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
        · have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbq
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
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
      subst this
      exact ⟨hP1, by simp only [ForInStep.value]; omega⟩
    · have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
      subst this
      exact ⟨hP1, by simp only [ForInStep.value]; omega⟩)
  obtain ⟨⟨t, ht, he, hsl⟩, hMr⟩ := hloop
  -- The proposer reward, then the payment write.
  rw [ht] at h
  obtain ⟨x, _, hinc, hset⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  have e9 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
  obtain ⟨-, hmx, hx, hsz⟩ := moveN_increaseBalance vals hnd st₀ E _ _ _ _ hinc
  -- The payment write changes the payment window only, which no part of the goal reads.
  obtain ⟨y, rfl⟩ : ∃ y, b = { x with builderPendingPayments := y } :=
    ⟨_, congrArg SizzLean.Cache.SSZ.Box.view e9⟩
  show econView x = econView { a with balances := x.balances } ∧ x.slot = a.slot ∧
    x.balances.val.size = a.balances.val.size ∧
    moveN vals st₀ E a x ≤ attBudget s a.validators.val.size
  simp only [econView, Prod.mk.injEq] at he
  obtain ⟨hv, hbal, he3⟩ := he
  refine ⟨?_, by rw [hx]; exact hsl, by rw [hsz]; exact congrArg (·.val.size) hbal, ?_⟩
  · rw [congrArg econView hx]
    simp only [econView, Prod.mk.injEq, true_and]
    exact ⟨hv, he3⟩
  · -- The loop kept the capped balances of `a`.
    refine Nat.le_trans (Nat.le_trans (Nat.le_of_eq ?_) hmx) ?_
    · exact (moveN_congr_left vals st₀ E x fun i => by
        unfold capN balN maxN
        rw [hv, hbal]).symm
    -- The numerator: at most three flags per attesting index, and at most
    -- `MAX_COMMITTEES_PER_SLOT` committees of indices.
    dsimp only at hMr
    simp only [List.map_const', List.sum_replicate_nat, Array.length_toList] at hMr
    have hnum := Nat.le_trans hMr (Nat.mul_le_mul_right (3 * (brMax s * wSum)) hL)
    -- The reward is a `Gwei` quotient by the proposer denominator, a small constant.
    rw [UInt64.toNat_div, EthCLLib.Proofs.toNat_ofNat_lt64 (by decide)]
    exact Nat.div_le_div_right hnum

end

end EthCLSpecs.Proofs.Heze
