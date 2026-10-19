import EthCLSpecs.Proofs.Heze.DriftEpochStep
import EthCLSpecs.Proofs.Heze.RunWeighs

/-!
# `EthCLSpecs.Proofs.Heze.DriftRun`: the steps of a run keep the invariant

A run is a list of slot steps and block steps. `StatePre` collects the bounds that a state of
the run must meet for the writers of a step from it. A slot step keeps `RunInv` at no cost,
or at the cost of an epoch when it ends one (`RunInv.slotStep`). A block step keeps it at the
cost `blockBudget` (`RunInv.blockStep`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The bounds at a state `t` of a run from `st₀` that the writers of a step from `t` need.
`NX` bounds the registry size plus one, `ΓX` the count of churn reservations of partial
withdrawals, `sq * sq` and `U` the total active balance, `U` the sum of the effective
balances, and `S` the inactivity scores. -/
structure StatePre (vals : List ValidatorIndex) (st₀ t : BeaconState)
    (E CX CC NX ΓX sq U S : Nat) : Prop where
  step : StepPre st₀ t E CX NX ΓX
  cons : ConsCtx st₀ t E CC
  nx : sizeOf t + 1 ≤ NX
  sqT : sq * sq ≤ (totBal t).toNat
  totU : (totBal t).toNat ≤ U
  ebU : ebSum t ≤ U
  sc : ∀ i, scoreN t i ≤ S
  bal : ∀ i, i < sizeOf t → balN t i + downN < 2 ^ 64
  dbc : t.depositBalanceToConsume.toNat + churnA < 2 ^ 63
  pd : ∀ i : Nat,
    (t.pendingDeposits.toArray[i]! : EthCLSpecs.Heze.PendingDeposit).amount.toNat < 2 ^ 63
  sz : sizeOf t + EthCLSpecs.Heze.Const.pendingDepositsLimit < 2 ^ 64
  s40 : sizeOf t < 2 ^ 40
  ep62 : epochN t + EthCLSpecs.Heze.Const.epochsPerSlashingsVector < 2 ^ 62
  cov : ∀ i, i < sizeOf t → UInt64.ofNat i ∈ vals

/-- The epoch test of a slot step from `t`. -/
def boundaryB (t : BeaconState) : Bool :=
  (t.slot + 1) % UInt64.ofNat EthCLSpecs.Heze.Const.slotsPerEpoch == 0

/-- **A slot step keeps the invariant**, at the cost of an epoch when it ends one. -/
theorem RunInv.slotStep {vals : List ValidatorIndex} {st₀ t t' : BeaconState}
    {E CX CC NX ΓX sq U S : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (C : DriftConsts) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀) (h0 : 0 < sq) (hinc : incN ≤ U)
    (hk2 : E < epochN st₀ + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2)
    (hEf : E + 1 < farN)
    (Pt : StatePre vals st₀ t E CX CC NX ΓX sq U S) (Pt' : StatePre vals st₀ t' E CX CC NX ΓX sq U S)
    (I : RunInv vals st₀ E CX CC t V W tag Γp B) (hΓX : Γp ≤ ΓX) (h : SlotStep t t') :
    ∃ V' W' tag', RunInv vals st₀ E CX CC t' V' W' tag' Γp
      (B + if boundaryB t then epochBudget sq U S + slEpoch st₀ (epochN t) else 0) := by
  obtain ⟨st1, st2, h1, h2, h3⟩ := h
  have e1 := processSlot_run_eq h1
  subst e1
  have I1 := I.of_econ (b := slotWrite t) rfl
  have K1 : AcKeep t (slotWrite t) := AcKeep.of_validators rfl rfl
  have e3 : t' = { st2 with slot := st2.slot + 1 } := (pureState_inj h3.symm).symm
  have ec3 : econView t' = econView st2 := by rw [e3]; rfl
  have hv3 : t'.validators = st2.validators := validators_of_econ ec3
  split at h2
  · rename_i hb
    have hbt : boundaryB t = true := hb
    rw [if_pos hbt]
    obtain ⟨-, V2, W2, tag2, I2⟩ := RunInv.processEpoch (e := slotWrite t) C hnd hshape₀
      (fun i hi => Pt.cov i hi) (Pt.step.keep K1) Pt.nx hΓX I1 h0
      (by rw [totBal_congr K1 Pt.step.h64]; exact Pt.sqT) Pt.ebU hinc Pt.sc hk2 Pt.ep62 hEf
      Pt.dbc Pt.pd Pt.sz h2
      (fun i hi => by
        have := Pt'.bal i (by unfold sizeOf at hi ⊢; rw [hv3]; exact hi)
        unfold balN at this ⊢
        rw [e3] at this
        exact this)
      (by have := Pt'.step.h64; unfold sizeOf; rw [← hv3]; exact this)
    exact ⟨V2, W2, tag2, (I2.of_econ ec3).mono_B (by rw [Nat.add_assoc]; exact Nat.le_refl _)⟩
  · rename_i hb
    have hbt : boundaryB t = false := by simpa [boundaryB] using hb
    rw [if_neg (by rw [hbt]; decide)]
    subst h2
    exact ⟨V, W, tag, (I1.of_econ ec3).mono_B (Nat.le_add_right _ _)⟩

/-- The largest count of withdrawal requests of one block. -/
def maxWR : Nat := EthCLSpecs.Heze.Const.maxWithdrawalRequestsPerPayload

/-- The bound of the move of one block. -/
def blockBudget (sq U : Nat) : Nat :=
  EthCLSpecs.Heze.Const.maxConsolidationRequestsPerPayload * slashCost maxEBN +
    EthCLSpecs.Heze.Const.maxAttestationsElectra * attBudget sq + syncBudget sq U

/-- The withdrawal requests of a block have amounts below `2 ^ 62`. -/
def BlockAmountsOK (sb : EthCLSpecs.Heze.SignedBeaconBlock) : Prop :=
  ∀ wr ∈ sb.message.body.parentExecutionRequests.withdrawals.val, wr.amount.toNat < 2 ^ 62

/-- **A block step keeps the invariant**, at the cost `blockBudget sq U`, with at most `maxWR`
more churn reservations. -/
theorem RunInv.blockStep {vals : List ValidatorIndex} {st₀ t t' : BeaconState}
    {E CX CC NX ΓX sq U S : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (C : DriftConsts) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀) (h0 : 0 < sq)
    (Pt : StatePre vals st₀ t E CX CC NX ΓX sq U S)
    (I : RunInv vals st₀ E CX CC t V W tag Γp B) (hΓX : Γp + maxWR ≤ ΓX)
    {sb : EthCLSpecs.Heze.SignedBeaconBlock} {vr : Bool} (hamt : BlockAmountsOK sb)
    (h : BlockStep sb vr t t') :
    ∃ Γ' V' W' tag', Γ' ≤ Γp + maxWR ∧ RunInv vals st₀ E CX CC t' V' W' tag' Γ' (B + blockBudget sq U) := by
  have hb := h.2.1
  have hW := sb.message.body.parentExecutionRequests.withdrawals.property
  have hC := sb.message.body.parentExecutionRequests.consolidations.property
  have hA := sb.message.body.attestations.property
  have X : OpsCtx vals st₀ t E CX (Γp + maxWR) :=
    ⟨C, hnd, hshape₀, ⟨NX, ΓX, Pt.step, Pt.nx, hΓX⟩, Pt.cov⟩
  obtain ⟨⟨V', W', tag', I'⟩, -⟩ := processBlock_ops X Pt.cons ⟨⟨V, W, tag, I⟩, AcKeep.refl t⟩
    Pt.s40 h0 Pt.sqT Pt.totU sb.message hamt (by unfold maxWR; omega) hb
  refine ⟨_, V', W', tag', by unfold maxWR; omega, I'.mono_B ?_⟩
  unfold blockBudget
  have := Nat.mul_le_mul_right (slashCost maxEBN) hC
  have := Nat.mul_le_mul_right (attBudget sq) hA
  omega

/-! ## The run -/

/-- The budget after `nb` blocks and `ne` epochs: the potentials of `st₀`, the cost of each
block, and the cost of each epoch from the epoch of `st₀` on. -/
def runB (vals : List ValidatorIndex) (st₀ : BeaconState) (E sq U S nb ne : Nat) : Nat :=
  phi vals E st₀ + nb * blockBudget sq U +
    ((List.range ne).map fun j => epochBudget sq U S + slEpoch st₀ (epochN st₀ + j)).sum

/-- The invariant of a run state `t`: some ghosts make `RunInv` hold at the budget of `nb`
blocks and of the epochs since `st₀`, the reservations are at most `maxWR` per block, and the
blocks are at most the slots since `st₀` plus one. -/
def RunAcc (vals : List ValidatorIndex) (st₀ : BeaconState) (E CX CC sq U S : Nat)
    (t : BeaconState) : Prop :=
  ∃ V W tag Γp nb, RunInv vals st₀ E CX CC t V W tag Γp
      (runB vals st₀ E sq U S nb (epochN t - epochN st₀)) ∧ Γp ≤ nb * maxWR ∧
    nb + (if t.latestBlockHeader.slot < t.slot then 1 else 0) ≤ t.slot.toNat - st₀.slot.toNat + 1

omit [Config] [CryptoBackend] in
theorem epochN_eq (t : BeaconState) : epochN t = t.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch :=
  computeEpochAtSlot_toNat t.slot

omit [Config] [CryptoBackend] in
theorem filledHeader_slot (t : BeaconState) : (filledHeader t).slot = t.latestBlockHeader.slot := by
  unfold filledHeader; split <;> rfl

/-- **The run keeps `RunAcc`.** Each state of the run meets `StatePre`, and each block meets
`BlockAmountsOK`. `ΓX` bounds the reservations of one more block than the slots of the run. -/
theorem runAcc_run {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {vals : List ValidatorIndex} {st₀ u : BeaconState} {E CX CC NX ΓX sq U S : Nat}
    (C : DriftConsts) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀) (h0 : 0 < sq) (hinc : incN ≤ U)
    (hk2 : E < epochN st₀ + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2)
    (hEf : E + 1 < farN)
    (hpre : ∀ s₁ s₂ t, steps = s₁ ++ s₂ → ChainRun hi s₁ st₀ t →
      StatePre vals st₀ t E CX CC NX ΓX sq U S)
    (hblk : ∀ sb vr, ChainStep.block sb vr ∈ steps → BlockAmountsOK sb)
    (hΓ : (u.slot.toNat - st₀.slot.toNat + 1) * maxWR ≤ ΓX) :
    ∀ (q : List ChainStep) (t : BeaconState), ChainRun hi q t u → ∀ p, steps = p ++ q →
      ChainRun hi p st₀ t → RunAcc vals st₀ E CX CC sq U S t → RunAcc vals st₀ E CX CC sq U S u := by
  intro q t hq
  induction hq with
  | nil => intro _ _ _ h; exact h
  | @slot q' t t1 w hlt hstep hrest ih =>
    intro p hp hpr ⟨V, W, tag, Γp, nb, I, hΓp, hnb⟩
    have hpr1 : ChainRun hi (p ++ [.slot]) st₀ t1 := hpr.append (.slot hlt hstep (.nil _))
    have hp1 : steps = (p ++ [.slot]) ++ q' := by rw [hp]; simp
    have Pt := hpre p (.slot :: q') t hp hpr
    have Pt1 := hpre (p ++ [.slot]) q' t1 hp1 hpr1
    have hlt' : t.slot.toNat < hi := hlt
    have hs1 := hstep.slot (by omega)
    have hs0 := (hpr.slot_le hhi).1
    have hsu := (hrest.slot_le hhi).1
    have hΓX : Γp ≤ ΓX := by
      have := Nat.mul_le_mul_right maxWR (show nb ≤ w.slot.toNat - st₀.slot.toNat + 1 by omega)
      omega
    obtain ⟨V1, W1, tag1, I1⟩ := I.slotStep C hnd hshape₀ h0 hinc hk2 hEf Pt Pt1 hΓX hstep
    refine ih hΓ (p ++ [.slot]) hp1 hpr1 ⟨V1, W1, tag1, Γp, nb, I1.mono_B ?_, hΓp, ?_⟩
    · -- The epoch count moves on at a boundary.
      have he0 : epochN st₀ ≤ epochN t := by
        rw [epochN_eq, epochN_eq]; exact Nat.div_le_div_right hs0
      have hspe := EthCLSpecs.Heze.Const.slotsPerEpochPos
      unfold runB
      split
      · rename_i hb
        have hb' : (t.slot.toNat + 1) % EthCLSpecs.Heze.Const.slotsPerEpoch = 0 :=
          (epochTest_iff t.slot (by omega)).mp hb
        have he1 : epochN t1 = epochN t + 1 := by
          rw [epochN_eq, epochN_eq, hs1]
          exact succ_div_of_mod_eq hb'
        rw [he1, show epochN t + 1 - epochN st₀ = (epochN t - epochN st₀) + 1 by omega,
          List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [show epochN st₀ + (epochN t - epochN st₀) = epochN t by omega]
        omega
      · rename_i hb
        have hb' : (t.slot.toNat + 1) % EthCLSpecs.Heze.Const.slotsPerEpoch ≠ 0 := fun h =>
          hb ((epochTest_iff t.slot (by omega)).mpr h)
        have he1 : epochN t1 = epochN t := by
          rw [epochN_eq, epochN_eq, hs1]
          exact epoch_succ_of_not_boundary hb'
        rw [he1]
        omega
    · -- The header keeps its slot, and the slot moves on.
      have hh : t1.latestBlockHeader.slot = t.latestBlockHeader.slot := by
        rw [hstep.hdr.1, filledHeader_slot]
      rw [hh]
      have : (if t.latestBlockHeader.slot < t1.slot then 1 else 0) ≤ 1 := by split <;> omega
      have : nb ≤ t.slot.toNat - st₀.slot.toNat + 1 := by
        have : 0 ≤ (if t.latestBlockHeader.slot < t.slot then 1 else 0) := Nat.zero_le _
        omega
      omega
  | @block q' t t1 w sb vr hstep hrest ih =>
    intro p hp hpr ⟨V, W, tag, Γp, nb, I, hΓp, hnb⟩
    have hpr1 : ChainRun hi (p ++ [.block sb vr]) st₀ t1 := hpr.append (.block sb vr hstep (.nil _))
    have hp1 : steps = (p ++ [.block sb vr]) ++ q' := by rw [hp]; simp
    have Pt := hpre p (.block sb vr :: q') t hp hpr
    obtain ⟨hbs, hlb, hlh, -, hsl⟩ := hstep.hdr
    have hs0 := (hpr.slot_le hhi).1
    have hsu := (hrest.slot_le hhi).1
    have hlt : t.latestBlockHeader.slot < t.slot := by rw [← hbs]; exact hlb
    rw [if_pos hlt] at hnb
    have hΓX : Γp + maxWR ≤ ΓX := by
      have := Nat.mul_le_mul_right maxWR (show nb + 1 ≤ w.slot.toNat - st₀.slot.toNat + 1 by
        rw [hsl] at hsu; omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    obtain ⟨Γ', V1, W1, tag1, hΓ', I1⟩ := I.blockStep C hnd hshape₀ h0 Pt hΓX
      (hblk sb vr (by rw [hp]; simp)) hstep
    have he1 : epochN t1 = epochN t := by rw [epochN_eq, epochN_eq, hsl]
    refine ih hΓ (p ++ [.block sb vr]) hp1 hpr1 ⟨V1, W1, tag1, Γ', nb + 1, I1.mono_B ?_, ?_, ?_⟩
    · unfold runB; rw [he1, Nat.add_mul, Nat.one_mul]; omega
    · rw [Nat.add_mul, Nat.one_mul]; omega
    · have hh : t1.latestBlockHeader.slot = t1.slot := by rw [hlh, hsl, ← hbs]; rfl
      rw [hh, if_neg (UInt64.lt_irrefl _), hsl]
      omega

end

end EthCLSpecs.Proofs.Heze
