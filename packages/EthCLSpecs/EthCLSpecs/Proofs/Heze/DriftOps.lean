import EthCLSpecs.Proofs.Heze.DriftSlash
import EthCLSpecs.Proofs.Heze.PaymentCarried

/-!
# `EthCLSpecs.Proofs.Heze.DriftOps`: the exits and slashings of a block keep the invariant

The operations of a block exit and slash validators in three loops: the proposer slashings,
the attester slashings, and the voluntary exits. Each exit and each slashing keeps `RunInv`
with new ghosts (`RunInv.exitStep`, `RunInv.slashStep`), and keeps the reads of the total
active balance (`AcKeep`). So `StepPre` at the start of the block holds before each of them.

`OpsInv` is the predicate that these loops keep: some ghosts make `RunInv` hold, and the
state keeps `AcKeep` from the start of the block. `forIn_list_state_inv` carries a state
predicate through a loop with an accumulator, as the loop of an attester slashing has one.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok keepsUncached_bind
  keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei
  builderPaymentIndex)

section
variable [Preset] [HasherTag]

/-- A loop with an accumulator keeps a predicate `Q` on the accumulator and the state, when
each run of the body keeps it and keeps the uncached box. -/
theorem forIn_list_state_inv {δ β : Type} (Q : β → BeaconState → Prop)
    (f : δ → β → HezeRun (ForInStep β)) (hk : ∀ d b, KeepsUncached (f d b)) :
    ∀ (l : List δ), (∀ d ∈ l, ∀ (b : β) (s : BeaconState) (r : ForInStep β) (s' : BeaconState),
        Q b s → (f d b).run (pureState s) = .ok (r, pureState s') → Q r.value s') →
      ∀ (init : β) (s : BeaconState) (r : β) (s' : BeaconState), Q init s →
        (forIn l init f).run (pureState s) = .ok (r, pureState s') → Q r s' := by
  intro l
  induction l with
  | nil =>
    intro _ init s r s' hq h
    rw [List.forIn_nil] at h
    injection h with h
    injection h with h1 h2
    subst h1
    rw [← EthCLLib.Proofs.pureState_inj h2]
    exact hq
  | cons d rest ih =>
    intro hf init s r s' hq h
    rw [List.forIn_cons] at h
    obtain ⟨step, s1, h1, h2⟩ := run_bind_eq_ok_pure (hk d init) h
    have hq1 := hf d List.mem_cons_self init s step s1 hq h1
    cases step with
    | done b =>
      injection h2 with h2
      injection h2 with e1 e2
      subst e1
      rw [← EthCLLib.Proofs.pureState_inj e2]
      exact hq1
    | yield b =>
      exact ih (fun d' hd' => hf d' (List.mem_cons_of_mem _ hd')) b s1 r s' hq1 h2

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- A voluntary exit runs `initiate_validator_exit` once its checks pass. -/
theorem processVoluntaryExit_run (sve : EthCLSpecs.Heze.SignedVoluntaryExit) (a b : BeaconState)
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState a) = .ok ((), pureState b)) :
    (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun)
      sve.message.validatorIndex).run (pureState a) = .ok ((), pureState b) := by
  unfold EthCLSpecs.Heze.processVoluntaryExit at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨_, -, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The pending-withdrawal read keeps the state.
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact h

/-- A proposer slashing clears at most one entry of the builder payments, which no read of
the invariant sees, then runs `slash_validator` on an unslashed validator. -/
theorem processProposerSlashing_run (ps : EthCLSpecs.Heze.ProposerSlashing) (a b : BeaconState)
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState a) = .ok ((), pureState b)) :
    ps.signedHeader1.message.proposerIndex.toNat < sizeOf a ∧
    slashedOf a ps.signedHeader1.message.proposerIndex.toNat = false ∧
    ∃ a', econView a' = econView a ∧ a'.slot = a.slot ∧
      (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun)
        ps.signedHeader1.message.proposerIndex).run (pureState a') = .ok ((), pureState b) := by
  unfold EthCLSpecs.Heze.processProposerSlashing at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The proposer read is in range and keeps the state.
  obtain ⟨prop, s1, hp, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hp', rfl⟩ := sszGetIdx_run_ok hp
  have hb := (Array.getElem?_eq_some_iff.mp hp').1
  obtain ⟨hsl, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  refine ⟨hb, ?_, ?_⟩
  · unfold slashedOf
    rw [show a.validators.val[ps.signedHeader1.message.proposerIndex.toNat]? = some prop
      from hp']
    simp only [EthCLSpecs.Heze.isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at hsl
    exact hsl.1.1
  -- The clear of one entry, at either half, keeps every read of the invariant.
  have clear : ∀ (j : Nat), ∃ t, (sszUpdate (pureState a) with builderPendingPayments[j]! := default)
      = pureState t ∧ econView t = econView a ∧ t.slot = a.slot := fun _ => ⟨_, rfl, rfl, rfl⟩
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨_, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
      have hs2 := EthCLLib.Proofs.run_modifyThe_eq_ok h2
      subst hs2
      obtain ⟨t, ht, he, hs⟩ := clear (builderPaymentIndex ps.signedHeader1.message.slot true)
      exact ⟨t, he, hs, by rw [← ht]; exact h⟩
    · exact ⟨a, rfl, rfl, h⟩
  · rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
      · obtain ⟨_, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
        have hs2 := EthCLLib.Proofs.run_modifyThe_eq_ok h2
        subst hs2
        obtain ⟨t, ht, he, hs⟩ := clear (builderPaymentIndex ps.signedHeader1.message.slot false)
        exact ⟨t, he, hs, by rw [← ht]; exact h⟩
      · exact ⟨a, rfl, rfl, h⟩
    · exact ⟨a, rfl, rfl, h⟩

/-- An attester slashing keeps a predicate `Q` that each slashing of an unslashed validator
of the registry keeps. -/
theorem processAttesterSlashing_inv (Q : BeaconState → Prop)
    (hQ : ∀ (s s' : BeaconState) (i : ValidatorIndex), Q s → i.toNat < sizeOf s →
      slashedOf s i.toNat = false →
      (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState s)
        = .ok ((), pureState s') → Q s')
    (asl : EthCLSpecs.Heze.AttesterSlashing) (a b : BeaconState) (ha : Q a)
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState a) = .ok ((), pureState b)) : Q b := by
  unfold EthCLSpecs.Heze.processAttesterSlashing at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The two validity reads keep the state.
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The loop body slashes or does nothing, and keeps the uncached box. The proof is the
  -- loop step of `keepsUncached_processAttesterSlashing`.
  have hbody : ∀ d b, KeepsUncached ((fun (x : ValidatorIndex) (r : Bool) => (do
      let state ← get
      if (decide (x.toNat < (sszGet state validators).size) &&
          EthCLSpecs.Heze.isSlashableValidator (sszGet state validators[x.toNat]!)
            (EthCLSpecs.Heze.currentEpochOf state)) = true then do
        EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) x
        pure (ForInStep.yield true)
      else pure (ForInStep.yield r) : HezeRun (ForInStep Bool))) d b) := by
    intro d b
    refine EthCLLib.Proofs.keepsUncached_iff_forall_from.mpr fun m => ?_
    refine EthCLLib.Proofs.keepsUncachedFrom_bind (EthCLLib.Proofs.keepsUncachedFrom_get m)
      (fun _ _ => ?_)
    refine EthCLLib.Proofs.keepsUncachedFrom_ite (fun _ => ?_)
      (fun _ => EthCLLib.Proofs.keepsUncachedFrom_pure _ _)
    exact EthCLLib.Proofs.keepsUncachedFrom_bind
      (EthCLLib.Proofs.keepsUncached_iff_forall_from.mp (keepsUncached_slashValidator _) _)
      (fun _ _ => EthCLLib.Proofs.keepsUncachedFrom_pure _ _)
  obtain ⟨r, t, h1, h2⟩ := run_bind_eq_ok_pure
    (EthCLLib.Proofs.keepsUncached_forIn_array _ hbody _ _) h
  rw [← Array.forIn_toList] at h1
  -- One pass of the loop body: a slashing of a slashable validator, or nothing.
  have ht := forIn_list_state_inv (fun _ s => Q s) _ hbody _
    (fun d _ acc s r' s' hq hb => by
    have hb := run_get_bind_eq_ok _ _ _ hb
    rcases run_ite_eq_ok hb with ⟨hc, hb⟩ | ⟨-, hb⟩
    · obtain ⟨⟨⟩, t1, h1, hb⟩ := run_bind_eq_ok_pure (keepsUncached_slashValidator d) hb
      have e2 := pureState_inj (run_pure_state_eq _ _ _ _ hb)
      subst e2
      simp only [Bool.and_eq_true, decide_eq_true_eq, SizzLean.Proofs.view_uncachedBox] at hc
      obtain ⟨hlt, hsl⟩ := hc
      refine hQ s _ d hq hlt ?_ h1
      unfold slashedOf
      rw [getElem?_pos s.validators.val _ hlt]
      rw [sszList_getElem!_eq, getElem!_pos s.validators.val _ hlt] at hsl
      simp only [EthCLSpecs.Heze.isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at hsl
      exact hsl.1.1
    · have e2 := pureState_inj (run_pure_state_eq _ _ _ _ hb)
      subst e2
      exact hq) false a r t ha h1
  -- The last assert keeps the state.
  have hbt : pureState b = pureState t := by
    rcases run_ite_eq_ok h2 with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact run_pure_state_eq _ _ _ _ h2
    · cases h2
  rw [pureState_inj hbt]
  exact ht

/-- The predicate of the exit loops of a block from `a₀`: some ghosts make the invariant hold,
and the state keeps the reads of the total active balance from `a₀`. -/
def OpsInv (vals : List ValidatorIndex) (st₀ a₀ : BeaconState) (E CX CC Γp B : Nat)
    (s : BeaconState) : Prop :=
  (∃ V W tag, RunInv vals st₀ E CX CC s V W tag Γp B) ∧ AcKeep a₀ s

/-- The facts at the start of a block that the exit loops need. `vals` holds every index of
the registry, and `Γc` bounds the count `Γp` along the block. -/
structure OpsCtx (vals : List ValidatorIndex) (st₀ a₀ : BeaconState) (E CX Γc : Nat) : Prop where
  consts : DriftConsts
  nodup : vals.Nodup
  shape₀ : ShapeOK st₀
  pre : ∃ NX ΓX, StepPre st₀ a₀ E CX NX ΓX ∧ sizeOf a₀ + 1 ≤ NX ∧ Γc ≤ ΓX
  cov : ∀ i, i < sizeOf a₀ → UInt64.ofNat i ∈ vals

/-- **A slashing keeps `OpsInv`.** -/
theorem OpsInv.slash {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (hΓ : Γp ≤ Γc)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (i : ValidatorIndex)
    (hi : i.toNat < sizeOf s) (hu : slashedOf s i.toNat = false)
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState s)
      = .ok ((), pureState s')) : OpsInv vals st₀ a₀ E CX CC Γp B s' := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  obtain ⟨NX, ΓX, P, hn, hg⟩ := X.pre
  replace hg := Nat.le_trans hΓ hg
  have hn' : exitedCount s + 1 ≤ NX := by
    have := exitedCount_le s
    have := hk.size
    omega
  have hiv : i ∈ vals := by
    have := X.cov i.toNat (by rw [← hk.size]; exact hi)
    rwa [UInt64.ofNat_toNat] at this
  obtain ⟨hk', V', W', tag', I'⟩ := I.slashStep X.consts i X.nodup X.shape₀ (P.keep hk) hn' hg h hu hiv
  exact ⟨⟨V', W', tag', I'⟩, hk.trans hk'⟩

/-- **An exit keeps `OpsInv`.** -/
theorem OpsInv.exit {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (hΓ : Γp ≤ Γc)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (i : ValidatorIndex)
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState s) = .ok ((), pureState s')) : OpsInv vals st₀ a₀ E CX CC Γp B s' := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  obtain ⟨NX, ΓX, P, hn, hg⟩ := X.pre
  replace hg := Nat.le_trans hΓ hg
  have hn' : exitedCount s + 1 ≤ NX := by
    have := exitedCount_le s
    have := hk.size
    omega
  obtain ⟨hk', W', tag', I'⟩ := I.exitStep X.consts i X.nodup X.shape₀ (P.keep hk) hn' hg h
  exact ⟨⟨V, W', tag', I'⟩, hk.trans hk'⟩

omit [Config] [CryptoBackend] in
/-- A step that keeps `econView` and the slot keeps `OpsInv`. -/
theorem OpsInv.of_econ {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γp B : Nat} (hs : OpsInv vals st₀ a₀ E CX CC Γp B s)
    (he : econView s' = econView s) (hsl : s'.slot = s.slot) :
    OpsInv vals st₀ a₀ E CX CC Γp B s' := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  have hv : s'.validators = s.validators := by
    simp only [econView, Prod.mk.injEq] at he
    exact he.1
  exact ⟨⟨V, W, tag, I.of_econ he⟩, hk.trans (AcKeep.of_validators hsl hv)⟩

/-- **A proposer slashing keeps `OpsInv`.** -/
theorem OpsInv.proposerSlashing {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (hΓ : Γp ≤ Γc)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (ps : EthCLSpecs.Heze.ProposerSlashing)
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState s) = .ok ((), pureState s')) : OpsInv vals st₀ a₀ E CX CC Γp B s' := by
  obtain ⟨hi, hu, a', he, hsl, h⟩ := processProposerSlashing_run ps s s' h
  have hv : a'.validators = s.validators := by
    simp only [econView, Prod.mk.injEq] at he
    exact he.1
  have hs' := hs.of_econ he hsl
  refine hs'.slash X hΓ _ (by unfold sizeOf; rw [hv]; exact hi) (by unfold slashedOf; rw [hv]; exact hu) h

end

end EthCLSpecs.Proofs.Heze
