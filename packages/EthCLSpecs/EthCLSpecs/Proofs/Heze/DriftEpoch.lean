import EthCLSpecs.Proofs.Heze.DriftBlockStep

/-!
# `EthCLSpecs.Proofs.Heze.DriftEpoch`: the epoch writers that the potentials pay for

`RunInv.payStep`: a step that keeps the registry and the churn fields keeps the invariant at no
new cost, when the potentials drop by at least the move. `process_pending_consolidations`
is such a step: each consolidation it applies moves at most `MAX_EFFECTIVE_BALANCE_ELECTRA` to
its target, and `gCons` drops by that much, since the queue drops the entry. The source is
withdrawable by the next epoch, so `moveN` does not count it.

`process_slashings` takes the correlation penalty of each validator that is withdrawable half
a slashings vector after the epoch. A validator that the run slashed is withdrawable later
than the run, so only a validator that `st₀` slashed pays, at one epoch (`slBud`).

`process_registry_updates` writes eligibility epochs and activation epochs, and ejects
validators through exits (`OpsInv.processRegistryUpdates`). An activation sets the epoch of a
validator that `st₀` did not activate, after the current epoch, so the active set of the
current epoch stays (`RunInv.actWrite`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

/-- A `fuelLoop` keeps a predicate `Q` of its value and its state, when each step keeps it and
keeps the uncached box. -/
theorem fuelLoop_state_inv [Preset] [HasherTag] {β α : Type} (Q : β → BeaconState → Prop)
    (R : α → BeaconState → Prop) (exhausted : α) (step : β → HezeRun (EthCLLib.Spec.Step β α))
    (hk : ∀ b, KeepsUncached (step b))
    (hstep : ∀ (b : β) (t : BeaconState) (r : EthCLLib.Spec.Step β α) (t' : BeaconState),
      Q b t → (step b).run (pureState t) = .ok (r, pureState t') →
      (∀ b', r = .next b' → Q b' t') ∧ (∀ x, r = .done x → R x t'))
    (hex : ∀ b t, Q b t → R exhausted t) :
    ∀ (fuel : Nat) (init : β) (t : BeaconState) (x : α) (t' : BeaconState), Q init t →
      (EthCLLib.Spec.fuelLoop fuel init exhausted step).run (pureState t)
        = .ok (x, pureState t') → R x t' := by
  intro fuel
  induction fuel with
  | zero =>
    intro init t x t' hq h
    unfold EthCLLib.Spec.fuelLoop at h
    have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h)
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
    subst this e
    exact hex init _ hq
  | succ fuel ih =>
    intro init t x t' hq h
    unfold EthCLLib.Spec.fuelLoop at h
    obtain ⟨r, t1, h1, h2⟩ := run_bind_eq_ok_pure (hk init) h
    obtain ⟨hn, hd⟩ := hstep init t r t1 hq h1
    cases r with
    | done a =>
      have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h2)
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h2
      subst this e
      exact hd _ rfl
    | next b =>
      exact ih b t1 x t' (hn b rfl) h2

section
variable [Preset] [HasherTag]

/-- **A step paid by the potentials keeps the invariant.** It keeps the registry and the churn
fields, and the potentials drop by at least the move. -/
theorem RunInv.payStep {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (hv : b.validators = a.validators) (hbsz : b.balances.val.size = a.balances.val.size)
    (hx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch)
    (hpay : phi vals E b + moveN vals st₀ E a b ≤ phi vals E a) :
    RunInv vals st₀ E CX CC b (stepV V a b) W tag Γp B := by
  have e2 : ∀ i, ebN b i = ebN a i := fun i => by simp [ebN, hv]
  have e4 : ∀ i, actOf b i = actOf a i := fun i => by simp [actOf, hv]
  have e5 : ∀ i, exitOf b i = exitOf a i := fun i => by simp [exitOf, hv]
  have e6 : ∀ i, wdrOf b i = wdrOf a i := fun i => by simp [wdrOf, hv]
  have e7 : sizeOf b = sizeOf a := by simp [sizeOf, hv]
  have e9 : ∀ i, maxN b i = maxN a i := fun i => by simp [maxN, hv]
  have e10 := exitedCount_eq e7 e5
  have e11 : ∀ i, slashedOf b i = slashedOf a i := fun i => by simp [slashedOf, hv]
  have hV : ∀ i, V i ≤ stepV V a b i := fun i => Nat.le_add_right _ _
  refine ⟨fun i hi hl => ?_, ?_, fun i hi hl => ?_, fun i h1 h2 => by rw [e4]; exact I.actOnce i h1 h2,
    fun i h1 h2 => by rw [e5]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => ?_, by rw [hx1, hx2]; exact I.churnX.of_exit_eq e5,
    by rw [hc1, hc2]; exact I.churnC.of_exit_eq e5, ?_,
    fun i hi hl hs => by rw [e6]; exact I.live i hi hl (by rw [← e7]; exact hs),
    by rw [e7]; exact I.sizeLe, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [e6]; exact I.slashInv i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)⟩
  · have := absDiff_triangle (capN b i.toNat) (capN a i.toNat) (capN st₀ i.toNat)
    have := I.cap i hi hl
    unfold stepV
    omega
  · rw [sum_stepV]
    have := I.bud
    omega
  · rw [e2]; exact (I.track i hi hl).mono (hV _)
  · exact Nat.le_trans (I.newExit i hi h1 h2 (by rw [← e5]; exact h3))
      (Nat.add_le_add_left (abound_mono (Nat.add_le_add_left (hV _) _)) _)
  · obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    constructor
    · rw [hv, hbsz]; exact s1
    · intro i hi; rw [e2, e9]; exact s2 i (by rw [← e7]; exact hi)
    · intro i hi; rw [e2]; exact s3 i (by rw [← e7]; exact hi)
    · intro i hi hx; rw [e6]; exact s4 i (by rw [← e7]; exact hi) (by rw [← e5]; exact hx)
    · intro i hi hs; rw [e5]; exact s5 i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)

/-- An index withdrawable by `E + 1` is not counted. -/
theorem countedB_false_of_wdr {vals : List ValidatorIndex} {st₀ a : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (i : Nat) (hi : i < sizeOf a)
    (hw : wdrOf a i ≤ E + 1) : countedB vals st₀ E i = false := by
  unfold countedB
  rw [List.any_eq_false]
  intro j hj hjc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hjc
  obtain ⟨hjv, hjl⟩ := hjc
  have := I.live j hj (by rw [hjv]; exact hjl) (by rw [hjv]; exact hi)
  rw [hjv] at this
  omega

/-- The consolidation potential of the entries of a queue from position `n` on. -/
def gConsFrom (E : Nat) (a : BeaconState) (l : List EthCLSpecs.Heze.PendingConsolidation) (n : Nat) :
    Nat :=
  maxEBN * ((l.drop n).filter fun q => decide (wdrOf a q.sourceIndex.toNat ≤ E + 1)).length

omit [HasherTag] in
theorem gConsFrom_succ (E : Nat) (a : BeaconState) (l : List EthCLSpecs.Heze.PendingConsolidation)
    (n : Nat) (hn : n < l.length) :
    gConsFrom E a l n = gConsFrom E a l (n + 1) +
      (if wdrOf a (l[n]).sourceIndex.toNat ≤ E + 1 then maxEBN else 0) := by
  unfold gConsFrom
  rw [List.drop_eq_getElem_cons hn, List.filter_cons]
  split
  · rename_i h
    simp only [decide_eq_true_eq] at h
    rw [if_pos h, List.length_cons, Nat.mul_succ]
  · rename_i h
    simp only [decide_eq_true_eq] at h
    simp only [if_neg h, Nat.add_zero]

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **The pending consolidations keep the invariant**, paid by `gCons`. -/
theorem RunInv.processPendingConsolidations (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    {a b : BeaconState} (C : DriftConsts) (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (hE : epochN a ≤ E)
    (h : (EthCLSpecs.Heze.processPendingConsolidations (StateTransition := HezeRun)).run
      (pureState a) = .ok ((), pureState b)) :
    AcKeep a b ∧ ∃ V', RunInv vals st₀ E CX CC b V' W tag Γp B := by
  unfold EthCLSpecs.Heze.processPendingConsolidations at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨npc, t, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_pcLoop _ _) h
  generalize hl : a.pendingConsolidations.val.toList = l
  -- The invariant of the scan: the reads but the balances stay, and the move plus the
  -- potential of the rest of the queue stays within the potential of the queue.
  let Q : Nat → BeaconState → Prop := fun n t =>
    t.validators = a.validators ∧ t.slot = a.slot ∧
    t.balances.val.size = a.balances.val.size ∧
    econView t = econView { a with balances := t.balances } ∧
    moveN vals st₀ E a t + gConsFrom E a l n ≤ gConsFrom E a l 0
  unfold EthCLSpecs.Heze.pcLoop at h1
  have hlv : (pureState a).view.pendingConsolidations.toArray.toList = l := hl
  have key : Q npc t := by
    -- The step keeps the uncached box, as in `keepsUncached_pcLoop`.
    refine fuelLoop_state_inv Q Q _ _ (fun _ => by
      open EthCLLib.Proofs in
      refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
      refine keepsUncached_get_bind (fun v => ?_)
      refine keepsUncachedFrom_bind (keepsUncachedFrom_liftErr _ _) (fun src w₁ => ?_)
      refine keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => ?_)
      refine keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => ?_)
      refine keepsUncachedFrom_bind (keepsUncachedFrom_liftErr _ _) (fun srcBal w₂ => ?_)
      refine returnsUncachedFrom_bind (returnsUncached_decreaseBalance _ _ _) (fun s₁ w₃ => ?_)
      refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _) (fun s₂ w₄ => ?_)
      exact keepsUncachedFrom_bind (keepsUncachedFrom_set w₄ s₂)
        (fun _ w₅ => keepsUncachedFrom_pure w₅ _)) ?_ (fun b t hq =>
      ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, by
        have h0 : gConsFrom E a l (pureState a).view.pendingConsolidations.toArray.size = 0 := by
          unfold gConsFrom
          rw [show (pureState a).view.pendingConsolidations.toArray.size = l.length by
            rw [← hlv, Array.length_toList], List.drop_length]
          rfl
        have := hq.2.2.2.2
        omega⟩) _ 0 a npc t
      ⟨rfl, rfl, rfl, rfl, by rw [moveN_self]; omega⟩ h1
    intro n t r t' ⟨hv, hsl, hsz, he, hm⟩ hrun
    rcases run_ite_eq_ok hrun with ⟨-, hrun⟩ | ⟨hlt, hrun⟩
    · have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ hrun)
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
      subst this e
      exact ⟨fun b' hb' => (by cases hb'), fun x hx => by cases hx; exact ⟨hv, hsl, hsz, he, hm⟩⟩
    have hn : n < l.length := by rw [← hlv]; simp at hlt ⊢; omega
    have hlv' : a.pendingConsolidations.toArray.toList = l := hl
    have hget : a.pendingConsolidations.toArray[n]! = l[n] := by
      rw [getElem!_pos _ n (by rw [← Array.length_toList, hlv']; exact hn)]
      simp only [← hlv', Array.getElem_toList]
    obtain ⟨src, s2, hsrc, hrun⟩ := run_bind_eq_ok _ _ _ _ (run_get_bind_eq_ok _ _ _ hrun)
    obtain ⟨hsrc', rfl⟩ := sszGetIdx_run_ok hsrc
    simp only [SizzLean.Proofs.view_uncachedBox] at hsrc' hrun
    rw [hget] at hsrc' hrun
    have hjs : (l[n]).sourceIndex.toNat < t.validators.val.size :=
      (Array.getElem?_eq_some_iff.mp hsrc').1
    have hwdr : wdrOf a (l[n]).sourceIndex.toNat = src.withdrawableEpoch.toNat := by
      unfold wdrOf; rw [← hv, hsrc']
    have hsucc := gConsFrom_succ E a l n hn
    rcases run_ite_eq_ok hrun with ⟨-, hrun⟩ | ⟨-, hrun⟩
    · -- A slashed source: the entry drops with no move.
      have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ hrun)
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
      subst this e
      refine ⟨fun b' hb' => ?_, fun x hx => by cases hx⟩
      cases hb'
      refine ⟨hv, hsl, hsz, he, ?_⟩
      split at hsucc <;> omega
    rcases run_ite_eq_ok hrun with ⟨-, hrun⟩ | ⟨hle, hrun⟩
    · have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ hrun)
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
      subst this e
      exact ⟨fun b' hb' => (by cases hb'), fun x hx => by cases hx; exact ⟨hv, hsl, hsz, he, hm⟩⟩
    -- A withdrawable source: its balance moves to the target.
    have hwe : src.withdrawableEpoch.toNat ≤ E + 1 := by
      have := Nat.le_of_not_lt fun hc => hle (UInt64.lt_iff_toNat_lt.mpr hc)
      have hne : (EthCLSpecs.Heze.currentEpochOf (pureState a) + 1).toNat ≤ epochN a + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_le _ _
      omega
    obtain ⟨sb, s3, hsb, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
    obtain ⟨-, rfl⟩ := sszGetIdx_run_ok hsb
    obtain ⟨st1, s4, hd, hrun⟩ := run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) hrun
    obtain ⟨-, x1, rfl, -, -⟩ := decreaseBalance_exact t _ _ _ hd
    obtain ⟨x2, s5, hi, hrun⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) hrun
    obtain ⟨-, hm2, hx2, hs2⟩ := moveN_increaseBalance vals hnd st₀ E _ _ _ _ hi
    obtain ⟨⟨⟩, s6, hset, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
    have e6 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
    subst e6
    have e7 := (EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ hrun)).symm
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
    subst this e7
    refine ⟨fun b' hb' => ?_, fun x hx => by cases hx⟩
    cases hb'
    have hunc : countedB vals st₀ E (l[n]).sourceIndex.toNat = false :=
      countedB_false_of_wdr I _ (by unfold sizeOf; rw [← hv]; exact hjs) (by rw [hwdr]; exact hwe)
    have hm1 := moveN_set_uncounted vals st₀ E t _ x1 hunc
    have htri := moveN_triangle vals st₀ E a t
      { t with balances := t.balances.set! (l[n]).sourceIndex.toNat x1 }
    have htri2 := moveN_triangle vals st₀ E a
      { t with balances := t.balances.set! (l[n]).sourceIndex.toNat x1 } x2
    have hamt : (umin sb src.effectiveBalance).toNat ≤ maxEBN := by
      rw [umin_toNat]
      have := I.shape.ebLe _ (by unfold sizeOf; rw [← hv]; exact hjs)
      have hmx := C.maxLe src
      unfold ebN maxN at this
      rw [← hv, hsrc'] at this
      simp only at this
      omega
    refine ⟨by rw [hx2]; exact hv, by rw [hx2]; exact hsl,
      by rw [hs2]; exact (SizzLean.Proofs.sszListSet!_size _ _ _).trans hsz, ?_, ?_⟩
    · rw [hx2]
      simp only [econView, Prod.mk.injEq, true_and] at he ⊢
      exact he
    · rw [if_pos (by rw [hwdr]; exact hwe)] at hsucc
      omega
  obtain ⟨hv, hsl, hsz, he, hm⟩ := key
  -- The drop of the passed entries.
  have hb := congrArg SizzLean.Cache.SSZ.Box.view (EthCLLib.Proofs.run_modifyThe_eq_ok h)
  simp only [econView, Prod.mk.injEq, true_and] at he
  obtain ⟨-, -, hppw, hdbc, hx1, hx2, hc1, hc2⟩ := he
  have hbt : b.validators = t.validators ∧ b.balances = t.balances ∧ b.slot = t.slot ∧
      b.pendingPartialWithdrawals = t.pendingPartialWithdrawals ∧
      b.depositBalanceToConsume = t.depositBalanceToConsume ∧
      b.exitBalanceToConsume = t.exitBalanceToConsume ∧ b.earliestExitEpoch = t.earliestExitEpoch ∧
      b.consolidationBalanceToConsume = t.consolidationBalanceToConsume ∧
      b.earliestConsolidationEpoch = t.earliestConsolidationEpoch ∧
      b.pendingConsolidations = sszDrop a.pendingConsolidations npc := by
    subst hb
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨bv, bbal, bsl, bppw, bdbc, bx1, bx2, bc1, bc2, bpc⟩ := hbt
  have hbv : b.validators = a.validators := bv.trans hv
  have hcap : ∀ i, capN b i = capN t i := fun i => by unfold capN balN maxN; rw [bbal, bv]
  have hmb : moveN vals st₀ E a b = moveN vals st₀ E a t := by unfold moveN; simp only [hcap]
  have hpay : phi vals E b + moveN vals st₀ E a b ≤ phi vals E a := by
    have hgb : gCons E b = gConsFrom E a l npc := by
      unfold gCons gConsFrom
      rw [bpc, sszDrop_toList, hl]
      congr 3
      funext q
      unfold wdrOf
      rw [hbv]
    have hga : gCons E a = gConsFrom E a l 0 := by
      unfold gCons gConsFrom; rw [hl, List.drop_zero]
    have hsl' : gSl vals b = gSl vals a := by unfold gSl sizeOf slashedOf maxN; rw [hbv]
    unfold phi gPart
    rw [hgb, hsl', hmb, bppw, hppw, bdbc, hdbc, hga]
    omega
  refine ⟨AcKeep.of_validators (bsl.trans hsl) hbv, _, I.payStep hbv (by rw [bbal]; exact hsz)
    (bx1.trans hx1) (bx2.trans hx2) (bc1.trans hc1) (bc2.trans hc2) hpay⟩

/-- The cost of the correlation penalty of index `i` at epoch `ep`: a validator that `st₀`
slashed, withdrawable `EPOCHS_PER_SLASHINGS_VECTOR / 2` epochs after `ep`. -/
def slBud (st₀ : BeaconState) (ep i : Nat) : Nat :=
  if i < sizeOf st₀ ∧ slashedOf st₀ i = true ∧
      wdrOf st₀ i = ep + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2 then 2 * maxEBN
  else 0

omit [Preset] [HasherTag] [Config] [CryptoBackend] in
/-- A balance divided by its own increment count is at most two increments. -/
theorem div_div_le_two {x c : Nat} (hc : 0 < c) (hx : c ≤ x) : x / (x / c) ≤ 2 * c := by
  have hq : 1 ≤ x / c := (Nat.le_div_iff_mul_le hc).mpr (by omega)
  have hlt : x < x / c * c + c := Nat.lt_div_mul_add hc
  have h1 : c ≤ x / c * c := Nat.le_mul_of_pos_left c hq
  have h2 : x / c * (2 * c) = x / c * c + x / c * c := by
    rw [Nat.two_mul, Nat.mul_add]
  exact Nat.div_le_of_le_mul (by rw [h2]; omega)

/-- **The correlation penalties keep the invariant**, at the cost `slBud` of each index. A
validator that the run slashed is withdrawable too late to pay a penalty within the run. -/
theorem RunInv.processSlashings (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    {a b : BeaconState} (C : DriftConsts) (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (hE : epochN a ≤ E)
    (hk2 : E < epochN st₀ + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2)
    (hep62 : epochN a + EthCLSpecs.Heze.Const.epochsPerSlashingsVector < 2 ^ 62)
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run
      (pureState a) = .ok ((), pureState b)) :
    AcKeep a b ∧ ∃ V', RunInv vals st₀ E CX CC b V' W tag Γp
      (B + ((List.range (sizeOf a)).map (slBud st₀ (epochN a))).sum) := by
  unfold EthCLSpecs.Heze.processSlashings at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  -- The total read succeeds and keeps the state.
  cases htot : EthCLSpecs.Heze.getTotalActiveBalance (pureState a) with
  | error e =>
    rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_error _ _ (by rw [htot]; rfl),
      EthCLLib.Proofs.except_bind_error] at h
    cases h
  | ok T =>
  rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_ok _ _ (by rw [htot]; rfl),
    EthCLLib.Proofs.except_bind_ok] at h
  -- The checked sum of the slashings and its checked product read the state only.
  obtain ⟨_, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
  rw [← Array.foldlM_toList] at h2
  have e2 := listFoldlM_run_state_eq (fun _ _ _ _ _ hb => (checkedAdd_run_ok hb).1) _ _ _ _ _ h2
  subst e2
  obtain ⟨_, s3, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, -⟩ := checkedMul_run_ok h3
  obtain ⟨r, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e1 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
  -- The penalty of one index: at most two caps. The total is at least one increment.
  have hT : EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat ≤ T.toNat := by
    rw [getTotalBalance_ok_toNat (u := a) (idx := EthCLSpecs.Heze.getActiveValidatorIndices
      (pureState a) (EthCLSpecs.Heze.currentEpochOf (pureState a))) htot]
    exact Nat.le_max_right _ _
  have hpen : ∀ (S : UInt64) (v : Validator), v.effectiveBalance.toNat ≤ maxEBN →
      (umin S T / (T / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG) *
        (v.effectiveBalance / EthCLSpecs.Heze.Const.effectiveBalanceIncrementG)).toNat ≤
        2 * maxEBN := by
    intro S v hv
    have hinc : 0 < EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat := C.incPos
    revert hT hinc
    generalize EthCLSpecs.Heze.Const.effectiveBalanceIncrementG = I0
    intro hT hinc
    have hp : (umin S T / (T / I0)).toNat ≤ 2 * I0.toNat := by
      rw [UInt64.toNat_div, umin_toNat, UInt64.toNat_div]
      exact Nat.le_trans (Nat.div_le_div_right (Nat.min_le_right _ _)) (div_div_le_two hinc hT)
    have hq : (v.effectiveBalance / I0).toNat * I0.toNat ≤ v.effectiveBalance.toNat := by
      rw [UInt64.toNat_div]; exact Nat.div_mul_le_self _ _
    have hprod : (umin S T / (T / I0)).toNat * (v.effectiveBalance / I0).toNat ≤ 2 * maxEBN := by
      have := Nat.mul_le_mul_right (v.effectiveBalance / I0).toNat hp
      rw [Nat.mul_assoc, Nat.mul_comm I0.toNat] at this
      have := C.maxEB62
      omega
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by have := C.maxEB62; omega)]
    exact hprod
  -- The loop: each index moves at most its `slBud`.
  -- The loop threads plain states, and its accumulator is a plain state.
  have hloop := forIn_move_le_inv (fun x y : State => moveN vals st₀ E x.view y.view)
    (fun x y z => moveN_triangle vals st₀ E _ _ _) (fun x => moveN_self vals st₀ E _)
    (fun x : State => ∃ y : BeaconState, x = pureState y ∧ y = { a with balances := y.balances } ∧
      y.balances.val.size = a.balances.val.size)
    (fun s : State => ∃ u : BeaconState, s = pureState u)
    (slBud st₀ (epochN a)) _ _ ?step _ _ _ _ ⟨a, rfl, rfl, rfl⟩ ⟨a, rfl⟩ h1
  case step =>
    intro i hi acc s s' st ⟨y, hy, hya, hysz⟩ ⟨u, hu⟩ hbody
    subst hy hu
    simp only [SizzLean.Proofs.view_uncachedBox] at hbody
    have hyv : y.validators = a.validators := by rw [hya]
    -- An index that skips keeps the accumulator.
    have skip : ∀ {st : ForInStep State} {s' : State},
        (do pure PUnit.unit; pure (ForInStep.yield (pureState y)) : HezeRun _).run (pureState u)
          = .ok (st, s') →
        (∃ y', st.value = pureState y' ∧ y' = { a with balances := y'.balances } ∧
          y'.balances.val.size = a.balances.val.size) ∧ (∃ u', s' = pureState u') ∧
        moveN vals st₀ E (pureState y).view st.value.view ≤ slBud st₀ (epochN a) i := by
      intro st s' hbody
      obtain ⟨_, s5, h5, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
      have e5 := run_pure_state_eq _ _ _ _ h5
      have e6 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbody
      have e7 := run_pure_state_eq _ _ _ _ hbody
      subst e5 e6 e7
      refine ⟨⟨y, rfl, hya, hysz⟩, ⟨_, rfl⟩, ?_⟩
      show moveN vals st₀ E y y ≤ _
      rw [moveN_self]
      exact Nat.zero_le _
    rcases run_ite_eq_ok hbody with ⟨hsl, hbody⟩ | ⟨-, hbody⟩
    rotate_left
    · exact skip hbody
    -- The checked target epoch did not overflow.
    obtain ⟨tg, s4, htg, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
    obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok htg
    rcases run_ite_eq_ok hbody with ⟨hwe, hbody⟩ | ⟨-, hbody⟩
    rotate_left
    · exact skip hbody
    -- The checked penalty did not overflow.
    obtain ⟨pen, s6, hpe, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
    obtain ⟨rfl, rfl, -⟩ := checkedMul_run_ok hpe
    · obtain ⟨x1, s3, h1, hbody⟩ :=
        run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) hbody
      obtain ⟨-, hm1, hx1, hs1⟩ := moveN_decreaseBalance vals hnd st₀ E y _ _ _ h1
      obtain ⟨_, s5, h5, hbody⟩ := run_bind_eq_ok _ _ _ _ hbody
      have e5 := run_pure_state_eq _ _ _ _ h5
      have e6 := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hbody
      have e7 := run_pure_state_eq _ _ _ _ hbody
      subst e5 e6 e7
      refine ⟨⟨x1, rfl, by rw [hx1, hya], by rw [hs1, hysz]⟩, ⟨_, rfl⟩, ?_⟩
      show moveN vals st₀ E y x1 ≤ _
      -- The penalized index is a validator that `st₀` slashed.
      rw [hyv] at hsl hwe hm1
      simp only [beq_iff_eq] at hwe
      have hia : i < a.validators.val.size := by
        refine Classical.byContradiction fun hge => ?_
        rw [sszList_getElem!_eq, getElem!_neg a.validators.val i (by omega)] at hsl
        cases hsl
      rw [sszList_getElem!_eq, getElem!_pos a.validators.val i hia] at hsl hwe
      rw [sszList_getElem!_eq, getElem!_pos a.validators.val i hia] at hm1
      have hsa : slashedOf a i = true := by
        unfold slashedOf; rw [getElem?_pos a.validators.val i hia]; exact hsl
      have hwN : wdrOf a i = epochN a + EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2 := by
        unfold wdrOf; rw [getElem?_pos a.validators.val i hia]
        show (a.validators.val[i]).withdrawableEpoch.toNat = _
        have hy : (UInt64.ofNat EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2 : UInt64).toNat =
            EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2 := by
          rw [UInt64.toNat_div, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          rfl
        have hc : (EthCLSpecs.Heze.currentEpochOf (pureState a)).toNat = epochN a := rfl
        rw [← hwe, UInt64.toNat_add, hy, hc, Nat.mod_eq_of_lt (by omega)]
      have hcase := I.slashInv i hia hsa
      rcases hcase with ⟨hi0, hs0, hw0⟩ | hlate
      · unfold slBud
        rw [if_pos ⟨hi0, hs0, by rw [← hw0, hwN]⟩]
        refine Nat.le_trans hm1 (hpen _ _ ?_)
        have := I.shape.ebLe i hia
        unfold ebN maxN at this
        rw [getElem?_pos a.validators.val i hia] at this
        exact Nat.le_trans this (C.maxLe _)
      · exfalso
        have : EthCLSpecs.Heze.Const.epochsPerSlashingsVector / 2 * 2 ≤
            EthCLSpecs.Heze.Const.epochsPerSlashingsVector := Nat.div_mul_le_self _ _
        omega
  obtain ⟨⟨y, hy, hya, hysz⟩, -, hm⟩ := hloop
  subst hy
  have hb : b = y := congrArg SizzLean.Cache.SSZ.Box.view e1
  subst hb
  have hm' : moveN vals st₀ E a b ≤ ((List.range (sizeOf a)).map (slBud st₀ (epochN a))).sum := by
    have := hm
    simp only [SizzLean.Proofs.view_uncachedBox] at this
    rw [List.range_eq_range'] at *
    simpa [Std.Legacy.Range.size, sizeOf] using this
  have hv : b.validators = a.validators := by rw [hya]
  have hsl : b.slot = a.slot := by rw [hya]
  exact ⟨AcKeep.of_validators hsl hv, _, I.balanceStep (by rw [hya]) hysz hm'⟩

end

/-! ## Registry updates -/

section
variable [Preset] [HasherTag]

/-- **A write of one validator that keeps every read but its activation epoch keeps the
invariant**, when `st₀` sets no activation epoch for it. -/
theorem RunInv.actWrite {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat} {j : Nat} {v v' : Validator}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (w : OneWrite a b j v v')
    (heb : v'.effectiveBalance = v.effectiveBalance)
    (hmx : EthCLSpecs.Heze.getMaxEffectiveBalance v' = EthCLSpecs.Heze.getMaxEffectiveBalance v)
    (hex : v'.exitEpoch = v.exitEpoch) (hwd : v'.withdrawableEpoch = v.withdrawableEpoch)
    (hsl : v'.slashed = v.slashed)
    (hfar : ¬ (j < sizeOf st₀ ∧ actOf st₀ j ≠ farN))
    (hq1 : b.pendingConsolidations = a.pendingConsolidations)
    (hq2 : b.pendingPartialWithdrawals = a.pendingPartialWithdrawals)
    (hd : b.depositBalanceToConsume = a.depositBalanceToConsume)
    (hx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch) :
    RunInv vals st₀ E CX CC b V W tag Γp B := by
  have emx : ∀ k, maxN b k = maxN a k := fun k =>
    w.read (fun u => (EthCLSpecs.Heze.getMaxEffectiveBalance u).toNat) 0
      (by dsimp only; rw [hmx]) k
  have eeb : ∀ k, ebN b k = ebN a k := fun k =>
    w.read (fun u => u.effectiveBalance.toNat) 0 (by dsimp only; rw [heb]) k
  have eact : ∀ k, k ≠ j → actOf b k = actOf a k := fun k hk =>
    w.read_ne (fun u => u.activationEpoch.toNat) 0 k hk
  have eex : ∀ k, exitOf b k = exitOf a k := fun k =>
    w.read (fun u => u.exitEpoch.toNat) _ (by dsimp only; rw [hex]) k
  have ewd : ∀ k, wdrOf b k = wdrOf a k := fun k =>
    w.read (fun u => u.withdrawableEpoch.toNat) _ (by dsimp only; rw [hwd]) k
  have esl : ∀ k, slashedOf b k = slashedOf a k := fun k => by
    unfold slashedOf
    rw [w.get k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, w.old]; exact hsl
    · rw [if_neg hk]
  have ecap : ∀ k, capN b k = capN a k := fun k => by unfold capN balN; rw [w.bal, emx]
  have ephi : phi vals E b = phi vals E a := by
    have hg : gSl vals b = gSl vals a := by
      unfold gSl
      rw [w.size]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      rw [esl, emx]
    have hc : gCons E b = gCons E a := by
      unfold gCons
      rw [hq1]
      simp only [ewd]
    unfold phi gPart
    rw [hg, hc, hq2, hd]
  have e10 := exitedCount_eq w.size eex
  refine ⟨fun i hi hl => by rw [ecap]; exact I.cap i hi hl, by rw [ephi]; exact I.bud,
    fun i hi hl => by rw [eeb]; exact I.track i hi hl, fun i h1 h2 => ?_,
    fun i h1 h2 => by rw [eex]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => I.newExit i hi h1 h2 (by rw [← eex]; exact h3),
    by rw [hx1, hx2]; exact I.churnX.of_exit_eq eex,
    by rw [hc1, hc2]; exact I.churnC.of_exit_eq eex, ?_,
    fun i hi hl hs => by rw [ewd]; exact I.live i hi hl (by rw [← w.size]; exact hs),
    by rw [w.size]; exact I.sizeLe, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [ewd]; exact I.slashInv i (by rw [← w.size]; exact hi) (by rw [← esl]; exact hs)⟩
  · by_cases hij : i = j
    · subst hij; exact absurd ⟨h1, h2⟩ hfar
    · rw [eact i hij]; exact I.actOnce i h1 h2
  · obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    refine ⟨by rw [w.bal, s1]; exact w.size.symm, fun i hi => ?_, fun i hi => ?_,
      fun i hi hx => ?_, fun i hi hs => ?_⟩
    · rw [eeb, emx]; exact s2 i (by rw [← w.size]; exact hi)
    · rw [eeb]; exact s3 i (by rw [← w.size]; exact hi)
    · rw [ewd]; exact s4 i (by rw [← w.size]; exact hi) (by rw [← eex]; exact hx)
    · rw [eex]; exact s5 i (by rw [← w.size]; exact hi) (by rw [← esl]; exact hs)

omit [HasherTag] in
/-- The write of one validator of the registry. -/
theorem oneWrite_set (s : BeaconState) (j : Nat) (hj : j < sizeOf s) (f : Validator → Validator) :
    OneWrite s (withValidators s (s.validators.set! j (f s.validators[j]!))) j s.validators[j]!
      (f s.validators[j]!) := by
  have hv : s.validators.val[j]? = some s.validators[j]! := by
    rw [sszList_getElem!_eq, getElem!_pos s.validators.val _ hj]
    exact getElem?_pos s.validators.val _ hj
  refine ⟨hj, fun k => getElem?_validators_set s _ k _ hj, hv, rfl, ?_⟩
  show (s.validators.set! _ _).val.size = s.validators.val.size
  exact SizzLean.Proofs.sszListSet!_size _ _ _

/-- **A write of the activation eligibility epoch keeps `OpsInv`.** -/
theorem OpsInv.eligWrite {vals : List ValidatorIndex} {st₀ a₀ s : BeaconState}
    {E CX CC Γp B : Nat} (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (j : Nat) (hj : j < sizeOf s)
    (x : EthCLSpecs.Heze.Epoch) :
    OpsInv vals st₀ a₀ E CX CC Γp B (withValidators s (s.validators.set! j
      { s.validators[j]! with activationEligibilityEpoch := x })) := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  have w := oneWrite_set s j hj (fun v => { v with activationEligibilityEpoch := x })
  exact ⟨⟨V, W, tag, I.sameReads w rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
    hk.trans (w.acKeep rfl rfl rfl)⟩

/-- **A write of the activation epoch keeps `OpsInv`**, when `st₀` sets no activation epoch
for the validator, the validator is not active, and the new epoch is after the current
epoch. -/
theorem OpsInv.actWrite {vals : List ValidatorIndex} {st₀ a₀ s : BeaconState}
    {E CX CC Γp B : Nat} (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (j : Nat) (hj : j < sizeOf s)
    (hfar : ¬ (j < sizeOf st₀ ∧ actOf st₀ j ≠ farN)) (hna : acB s j = false)
    (x : EthCLSpecs.Heze.Epoch) (hx : EthCLSpecs.Heze.currentEpochOf (pureState s) < x) :
    OpsInv vals st₀ a₀ E CX CC Γp B (withValidators s (s.validators.set! j
      { s.validators[j]! with activationEpoch := x })) := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  have w := oneWrite_set s j hj (fun v => { v with activationEpoch := x })
  have hact : EthCLSpecs.Heze.isActiveValidator { s.validators[j]! with activationEpoch := x }
      (EthCLSpecs.Heze.currentEpochOf (pureState s)) =
      EthCLSpecs.Heze.isActiveValidator s.validators[j]!
        (EthCLSpecs.Heze.currentEpochOf (pureState s)) := by
    have h1 : acB s j = EthCLSpecs.Heze.isActiveValidator s.validators[j]!
        (EthCLSpecs.Heze.currentEpochOf (pureState s)) := by
      unfold acB; rw [w.old]
    rw [← h1, hna]
    unfold EthCLSpecs.Heze.isActiveValidator
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (UInt64.not_le.mpr hx)
  exact ⟨⟨V, W, tag, I.actWrite w rfl rfl rfl rfl rfl hfar rfl rfl rfl rfl rfl rfl rfl⟩,
    hk.trans (w.acKeep rfl rfl hact)⟩

/-- A program `x` keeps a predicate `Q` of the plain state: each run from a plain state that
holds `Q` to a plain state ends in a state that holds `Q`. -/
def RunKeeps {α : Type} (Q : BeaconState → Prop) (x : HezeRun α) : Prop :=
  ∀ (t : BeaconState) (r : α) (t' : BeaconState), Q t →
    x.run (pureState t) = .ok (r, pureState t') → Q t'

theorem RunKeeps.bind {α β : Type} {Q : BeaconState → Prop} {x : HezeRun α}
    {k : α → HezeRun β} (hkx : KeepsUncached x) (hx : RunKeeps Q x)
    (hk : ∀ a, RunKeeps Q (k a)) : RunKeeps Q (x >>= k) := by
  intro t r t' hq h
  obtain ⟨a, t1, h1, h2⟩ := run_bind_eq_ok_pure hkx h
  exact hk a t1 r t' (hx t a t1 hq h1) h2

theorem RunKeeps.ite {α : Type} {Q : BeaconState → Prop} {p : Prop} [Decidable p]
    {x y : HezeRun α} (hx : p → RunKeeps Q x) (hy : ¬ p → RunKeeps Q y) :
    RunKeeps Q (if p then x else y) := by
  by_cases hp : p
  · rw [if_pos hp]; exact hx hp
  · rw [if_neg hp]; exact hy hp

theorem RunKeeps.pure {α : Type} {Q : BeaconState → Prop} (a : α) :
    RunKeeps Q (Pure.pure a : HezeRun α) := by
  intro t r t' hq h
  have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h)
  subst e
  exact hq

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

set_option maxHeartbeats 800000 in
/-- **The registry updates keep `OpsInv`.** A write of an activation eligibility epoch keeps
every read. An ejection is an exit. An activation sets the epoch of a validator that `st₀`
did not activate, and the new epoch is after the current epoch, so the active set of the
current epoch stays. The checked activation epoch and the checked churn reservation of the
exit make the body larger. It needs more than the default heartbeat limit. -/
theorem OpsInv.processRegistryUpdates {vals : List ValidatorIndex} {st₀ a₀ b : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (hΓ : Γp ≤ Γc)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B a₀)
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState a₀) = .ok ((), pureState b)) : OpsInv vals st₀ a₀ E CX CC Γp B b := by
  obtain ⟨NX, ΓX, P, -, -⟩ := X.pre
  have hc62 : epochN a₀ + lagN < 2 ^ 62 := by
    have := P.small
    have := P.curE
    have := Nat.le_max_right st₀.earliestExitEpoch.toNat (E + lagN)
    omega
  have hfar64 : EthCLSpecs.Heze.Const.farFutureEpoch.toNat = farN := rfl
  unfold EthCLSpecs.Heze.processRegistryUpdates at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  -- The checked activation epoch keeps the state.
  obtain ⟨act, s0, hae, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hactE, rfl⟩ := liftErr_run_ok_spec hae
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨r, s1, h1, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
  let Q : BeaconState → Prop := OpsInv vals st₀ a₀ E CX CC Γp B
  have hloop := forIn_list_state_inv (fun _ t => Q t) _ (fun _ _ => by frame_keeps) _
    (fun d hd acc y r' s' hq hb => by
      have hb := run_get_bind_eq_ok _ _ _ hb
      have hdl : d < sizeOf a₀ := by
        simp only [List.mem_range'_1] at hd
        have h2 := hd.2
        simp only [Std.Legacy.Range.size] at h2
        exact (by omega : d < (pureState a₀).view.validators.size)
      have hd64 : (UInt64.ofNat d).toNat = d := by
        rw [UInt64.toNat_ofNat']
        exact Nat.mod_eq_of_lt (by have := P.h64; unfold sizeOf at hdl; omega)
      have hdy : d < sizeOf y := by rw [hq.2.size]; exact hdl
      have hv0 : y.validators.val[d]? = some y.validators[d]! := (oneWrite_set y d hdy id).old
      -- The leaves of the body.
      have hEl : ∀ x : EthCLSpecs.Heze.Epoch, RunKeeps Q
          (EthCLSpecs.Heze.modifyState fun st =>
            EthCLSpecs.Heze.modValidator st (UInt64.ofNat d) fun v =>
              { v with activationEligibilityEpoch := x }) := by
        intro x t r t' hq' h
        have e := EthCLLib.Proofs.run_modifyThe_eq_ok h
        rw [modValidator_pureState, hd64] at e
        rw [EthCLLib.Proofs.pureState_inj e]
        exact hq'.eligWrite d (by rw [hq'.2.size]; exact hdl) x
      have hEx : ∀ i, RunKeeps Q
          (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i) := by
        intro i t r t' hq' h
        cases r
        exact hq'.exit X hΓ i h
      have hAc : EthCLSpecs.Heze.isEligibleForActivation (pureState y)
            (pureState y).view.validators[d]! = true → RunKeeps Q
          (EthCLSpecs.Heze.modifyState fun st =>
            EthCLSpecs.Heze.modValidator st (UInt64.ofNat d) fun v =>
              { v with activationEpoch := act }) := by
        intro hc t r t' hq' h
        simp only [EthCLSpecs.Heze.isEligibleForActivation, SizzLean.Proofs.view_uncachedBox,
          Bool.and_eq_true, beq_iff_eq] at hc
        have hay : actOf y d = farN := by
          unfold actOf; rw [hv0]; dsimp only; rw [hc.2]; exact hfar64
        have hfar : ¬ (d < sizeOf st₀ ∧ actOf st₀ d ≠ farN) := fun ⟨h1, h2⟩ => by
          obtain ⟨⟨V, W, tag, I⟩, -⟩ := hq
          have := I.actOnce d h1 h2
          rw [hay] at this
          exact h2 this.symm
        have ecur : ∀ u : BeaconState, AcKeep a₀ u →
            EthCLSpecs.Heze.currentEpochOf (pureState u) =
              EthCLSpecs.Heze.currentEpochOf (pureState a₀) := fun u hk => by
          show EthCLSpecs.Heze.computeEpochAtSlot u.slot = EthCLSpecs.Heze.computeEpochAtSlot a₀.slot
          rw [hk.slot]
        have hcur : (EthCLSpecs.Heze.currentEpochOf (pureState a₀)).toNat = epochN a₀ := rfl
        have hny : acB y d = false := by
          unfold acB
          rw [hv0]
          dsimp only
          unfold EthCLSpecs.Heze.isActiveValidator
          rw [hc.2, ecur y hq.2]
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          refine Or.inl fun hle => ?_
          rw [UInt64.le_iff_toNat_le, hfar64, hcur] at hle
          have h62 : epochN a₀ < farN := by unfold farN; omega
          exact absurd hle (Nat.not_le.mpr h62)
        have hnt : acB t d = false := by rw [hq'.2.gate d, ← hq.2.gate d]; exact hny
        have hx : EthCLSpecs.Heze.currentEpochOf (pureState t) < act := by
          rw [ecur t hq'.2]
          -- A successful activation epoch is the sum `epoch + 1 + MAX_SEED_LOOKAHEAD`.
          rw [computeActivationExitEpoch_eq] at hactE
          split at hactE
          · cases hactE
          split at hactE
          · cases hactE
          injection hactE with hactE
          subst hactE
          unfold lagN at hc62
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_one, hcur]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have e := EthCLLib.Proofs.run_modifyThe_eq_ok h
        rw [modValidator_pureState, hd64] at e
        rw [EthCLLib.Proofs.pureState_inj e]
        exact hq'.actWrite d (by rw [hq'.2.size]; exact hdl) hfar hnt _ hx
      -- The three branches of the `if` chain: a queue write, an exit, or an activation write.
      refine (?_ : RunKeeps Q _) y r' s' hq hb
      repeat' first
        | exact RunKeeps.pure _
        | refine RunKeeps.ite (fun _ => ?_) (fun _ => ?_)
        | refine RunKeeps.bind (by frame_keeps) (hEl _) (fun _ => ?_)
        | refine RunKeeps.bind (keepsUncached_initiateValidatorExit _) (hEx _) (fun _ => ?_)
        | refine RunKeeps.bind (by frame_keeps) (hAc ‹_›) (fun _ => ?_)
        | refine RunKeeps.bind (by frame_keeps) (RunKeeps.pure _) (fun _ => ?_))
    PUnit.unit a₀ r s1 hs h1
  have e := run_pure_state_eq _ _ _ _ h
  rw [pureState_inj e]
  exact hloop

end

end EthCLSpecs.Proofs.Heze
