import EthCLSpecs.Proofs.Heze.ViableNext
import EthCLSpecs.Proofs.Heze.FinalEmpty
import EthCLSpecs.Proofs.Heze.StakeRun

/-!
# `EthCLSpecs.Proofs.Heze.ViableWindow`: EMPTY `r` stays viable through the window

`filter_node_tree` keeps a node only through a leaf below it that passes the leaf check
(`go_kept_leaf`). So when FULL `r` is in the filtered tree, a leaf below FULL `r` passes the
check, and its two reads constrain the store: the voting source of its block, and the
checkpoint block of its branch at the finalized epoch.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_pure_eq_ok pureState pureState_inj runPure)
open EthCLLib.Spec (HasherTag MapKind FcMap htr)
open EthCLSpecs.Heze (Preset Config Store ForkChoiceNode getNodeChildren isPayloadVerified)

variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
  [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root]

/-- **A kept node has a passing leaf below it.** The walk keeps a node with children only when
a child's walk keeps a node, and a node without children only when it passes `leafOk`. -/
theorem go_kept_leaf (store : Store map) :
    ∀ (K : Nat) (n : ForkChoiceNode) (t : Store map) (xs : Array ForkChoiceNode),
      (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
        store K n).run t = .ok (xs, t) →
      ∀ x ∈ xs, ∃ d, NodeBelow store x d ∧
        (∃ cs, (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store d).run t
          = .ok (cs, t) ∧ cs.isEmpty = true) ∧
        (leafOk store d).run t = .ok (true, t) := by
  intro K
  induction K with
  | zero =>
    intro n t xs h x hx
    simp only [EthCLSpecs.Heze.filterNodeTree.go] at h
    rw [run_pure_eq_ok _ _ _ _ h] at hx
    simp at hx
  | succ K ih =>
    intro n t xs h x hx
    obtain ⟨-, cs, hcs, hcase⟩ := filterNodeTree_go_succ_run store K n t t xs h
    have hedge := getNodeChildren_run_edge store t t n cs hcs
    rcases hcase with ⟨-, -, hm⟩ | ⟨hemp, b, hb, hm⟩
    · rcases (hm x).mp hx with ⟨rfl, c, hc, ys, hys, y, hy⟩ | ⟨c, hc, ys, hys, hxc⟩
      · obtain ⟨d, hyd, hd⟩ := ih c t ys hys y hy
        have hcy := go_result_below store K c t ys hys y hy
        exact ⟨d, NodeBelow.of_edge (hedge c (Array.mem_toList_iff.mp hc))
          (NodeBelow.trans store _ _ _ hcy hyd), hd⟩
      · exact ih c t ys hys x hxc
    · obtain ⟨rfl, hbt⟩ := (hm x).mp hx
      subst hbt
      exact ⟨x, .refl, ⟨cs, hcs, hemp⟩, hb⟩

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **A leaf passes when its voting source is recent and the finalized test passes.** The
justified test passes through its second branch: the voting source epoch plus two is at least
the current epoch, and the sum does not overflow. -/
theorem leafOk_true_of (store : Store map) (n : ForkChoiceNode) (u : Store map)
    {E : EthCLSpecs.Heze.Epoch} {vs : EthCLSpecs.Heze.Checkpoint}
    (hE : (EthCLSpecs.Heze.getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run u = .ok (E, u))
    (hvs : (EthCLSpecs.Heze.getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map))
      store n.root).run u = .ok (vs, u))
    (hfit : vs.epoch.toNat + 2 < 2 ^ 64) (hge : E.toNat ≤ vs.epoch.toNat + 2)
    (hfin : (finRead store n.root).run u = .ok (true, u)) :
    (leafOk store n).run u = .ok (true, u) := by
  have hadd : (vs.epoch + 2).toNat = vs.epoch.toNat + 2 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hfit
  have hno : ¬ (vs.epoch + 2 < vs.epoch) := by
    rw [UInt64.lt_iff_toNat_lt, hadd]
    omega
  have hgeU : vs.epoch + 2 ≥ E := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le, hadd]
    exact hge
  rw [leafOk_eq_finRead, EthCLLib.Proofs.run_bind, hE, EthCLLib.Proofs.except_bind_ok]
  dsimp only
  rw [EthCLLib.Proofs.run_bind, hvs, EthCLLib.Proofs.except_bind_ok]
  dsimp only
  split
  · simp only [pure_bind]
    rw [EthCLLib.Proofs.run_bind, hfin, EthCLLib.Proofs.except_bind_ok]
    rfl
  · simp only [EthCLLib.Spec.checkedAdd, hno, ↓reduceIte, pure_bind, decide_eq_true hgeU]
    rw [EthCLLib.Proofs.run_bind, hfin, EthCLLib.Proofs.except_bind_ok]
    rfl

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **The stored state of a node below `n` comes from the stored state of `n` by a run.** An
EMPTY or FULL edge keeps the root. A block edge goes to a stored block whose parent is the
root before it. Its stored state is the state transition of the parent's stored state
(`StateLink`), which is a run (`stateTransition_chainRun`). The anchor has no stored state
transition, so no node of the path other than `n` sits at the anchor root. -/
theorem NodeBelow.stateRun [EthCLLib.Spec.CryptoBackend]
    [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
      EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
    {store : Store map} {a0 : EthCLSpecs.Heze.Root} (hlink : StateLink a0 store)
    {n x : ForkChoiceNode} (h : NodeBelow store n x)
    (hna : ∀ y, NodeBelow store n y → y.root = a0 → y.root = n.root)
    {wn : EthCLSpecs.Heze.BeaconState}
    (hwn : FcMap.lookup store.blockStates n.root = some (pureState wn)) :
    ∃ q wx, FcMap.lookup store.blockStates x.root = some (pureState wx) ∧
      ChainRun (2 ^ 64 - 1) q wn wx := by
  induction h with
  | refl => exact ⟨[], wn, hwn, .nil _⟩
  | step p c hpd hedge ih =>
    obtain ⟨q, wp, hwp, hrun⟩ := ih
    cases hedge with
    | empty root => exact ⟨q, wp, hwp, hrun⟩
    | full root => exact ⟨q, wp, hwp, hrun⟩
    | block parent root b s s' hb hpar hps =>
      by_cases hr0 : root = a0
      · have hrn : root = n.root :=
          hna _ (.step _ _ hpd (.block _ root b s s' hb hpar hps)) hr0
        refine ⟨[], wn, ?_, .nil _⟩
        show FcMap.lookup store.blockStates root = some (pureState wn)
        rw [hrn]
        exact hwn
      · obtain ⟨sb, pv, w, hsb, hpv, hw, ht⟩ := hlink root b hb hr0
        rw [hpar, hwp] at hpv
        injection hpv with hpv
        have hpv' := pureState_inj hpv
        subst hpv'
        obtain ⟨k, hk⟩ := stateTransition_chainRun sb true (2 ^ 64 - 1)
          (by have := sb.message.slot.toNat_lt; omega) _ w ht
        exact ⟨q ++ (List.replicate k .slot ++ [.block sb true]), w, hw, hrun.append hk⟩

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **`NodeBelow.stateRun` as a store run.** Start from a store run `pre` to the stored state of
`n`. Each block edge appends the slot steps and the validated block step of the block's state
transition, and the block to the ancestor path. So `pre` followed by the run to `x` is a store
run of the store. The block of each edge has a nonzero state root (`hzr`). -/
theorem NodeBelow.storeRun [EthCLLib.Spec.CryptoBackend]
    [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
      EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
    {store : Store map} {A : EthCLSpecs.Heze.BeaconState} {a : EthCLSpecs.Heze.BeaconBlock}
    (hslot : SlotInv a store) (hlink : StateLink (htr a) store)
    (hzr : ∀ k b, FcMap.lookup store.blocks k = some b → k ≠ htr a →
      b.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    {n x : ForkChoiceNode} (h : NodeBelow store n x)
    (hna : ∀ y, NodeBelow store n y → y.root = htr a → y.root = n.root)
    {wn : EthCLSpecs.Heze.BeaconState}
    (hwn : FcMap.lookup store.blockStates n.root = some (pureState wn))
    {pre : List ChainStep} (hpre : ChainRun (2 ^ 64 - 1) pre A wn)
    (hpath : AncestorPath a store n.root (blocksOf pre)) (hval : ValidatedSteps pre)
    (hend : EndsAtBlock pre) :
    ∃ q wx, FcMap.lookup store.blockStates x.root = some (pureState wx) ∧
      ChainRun (2 ^ 64 - 1) q wn wx ∧ StoreRun A a store (pre ++ q) := by
  suffices H : ∃ q wx, FcMap.lookup store.blockStates x.root = some (pureState wx) ∧
      ChainRun (2 ^ 64 - 1) q wn wx ∧ AncestorPath a store x.root (blocksOf (pre ++ q)) ∧
      ValidatedSteps (pre ++ q) ∧ EndsAtBlock (pre ++ q) by
    obtain ⟨q, wx, hwx, hq, hp, hv, he⟩ := H
    exact ⟨q, wx, hwx, hq, x.root, wx, hpre.append hq, hp, hv, he⟩
  induction h with
  | refl => exact ⟨[], wn, hwn, .nil _, by rw [List.append_nil]; exact hpath,
      by rw [List.append_nil]; exact hval, by rw [List.append_nil]; exact hend⟩
  | step p c hpd hedge ih =>
    obtain ⟨q, wp, hwp, hrun, hp, hv, he⟩ := ih
    cases hedge with
    | empty root => exact ⟨q, wp, hwp, hrun, hp, hv, he⟩
    | full root => exact ⟨q, wp, hwp, hrun, hp, hv, he⟩
    | block parent root b s s' hb hpar hps =>
      by_cases hr0 : root = htr a
      · have hrn : root = n.root :=
          hna _ (.step _ _ hpd (.block _ root b s s' hb hpar hps)) hr0
        refine ⟨[], wn, ?_, .nil _, ?_, by rw [List.append_nil]; exact hval,
          by rw [List.append_nil]; exact hend⟩
        · show FcMap.lookup store.blockStates root = some (pureState wn)
          rw [hrn]
          exact hwn
        · show AncestorPath a store root _
          rw [List.append_nil, hrn]
          exact hpath
      · obtain ⟨sb, pv, w, hsb, hpv, hw, ht⟩ := hlink root b hb hr0
        rw [hpar, hwp] at hpv
        injection hpv with hpv
        have hpv' := pureState_inj hpv
        subst hpv'
        obtain ⟨k, hk⟩ := stateTransition_chainRun sb true (2 ^ 64 - 1)
          (by have := sb.message.slot.toNat_lt; omega) _ w ht
        have hba : b ≠ a := fun e => hr0 (by rw [← hslot.atRoot root b hb, e])
        have hbl : blocksOf (pre ++ (q ++ (List.replicate k .slot ++ [.block sb true]))) =
            blocksOf (pre ++ q) ++ [b] := by
          rw [← List.append_assoc, blocksOf_append, blocksOf_append (List.replicate k .slot),
            blocksOf_replicate_slot]
          show _ ++ ([] ++ [sb.message]) = _
          rw [hsb]
          rfl
        refine ⟨q ++ (List.replicate k .slot ++ [.block sb true]), w, hw, hrun.append hk, ?_, ?_,
          .inr ⟨pre ++ q ++ List.replicate k .slot, sb, true, by simp⟩⟩
        · show AncestorPath a store root _
          rw [hbl]
          exact .cons hb hba (hpar ▸ hp)
        · rw [← List.append_assoc]
          exact hv.append_transition k sb (hsb ▸ hzr root b hb hr0)

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **A passed target test of the previous epoch justifies at least that epoch.** The pull-up
of a state after the first two epochs runs the weigh step. The step sets the justified
checkpoint to the current epoch when the current test passes, else to the previous epoch when
the previous test passes (`weighJustificationAndFinalization_run_ok`). -/
theorem pullup_cj_ge [EthCLLib.Spec.CryptoBackend] {v pulled : EthCLSpecs.Heze.BeaconState}
    (hp : runPure (EthCLSpecs.Heze.processJustificationAndFinalization
      (StateTransition := HezeRun)) v = .ok ((), pulled))
    (h2 : 2 ≤ v.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch) (hjp : jpOf v = true) :
    (EthCLSpecs.Heze.previousEpochOf (pureState v)).toNat ≤
      pulled.currentJustifiedCheckpoint.epoch.toNat ∧
    pulled.currentJustifiedCheckpoint.epoch.toNat ≤
      v.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := by
  have hE : (EthCLSpecs.Heze.currentEpochOf (pureState v)).toNat =
      v.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := currentEpochOf_toNat v
  have hP := previousEpochOf_toNat_sub v
  have hg : ¬ EthCLSpecs.Heze.currentEpochOf (pureState v) ≤
      EthCLSpecs.Heze.Const.genesisEpoch + 1 := by
    intro h'
    have hg' := UInt64.le_iff_toNat_le.mp h'
    rw [hE] at hg'
    simp [EthCLSpecs.Heze.Const.genesisEpoch] at hg'
    omega
  obtain ⟨prevIdx, currIdx, tot, prev, curr, h1, h2', h3, h4, h5, hjf⟩ :=
    processJustificationAndFinalization_run_ok hp hg
  have et : totBal v = tot := totBal_of_ok h3
  have etp : tgtBal v (EthCLSpecs.Heze.previousEpochOf (pureState v)) = prev := tgtBal_of_ok h1 h4
  obtain ⟨pr, cr, hw⟩ := weighJustificationAndFinalization_run_ok _ _ _ _ _ hjf
  have hcj := hw.2.1
  unfold jpOf at hjp
  rw [et, etp] at hjp
  rw [hcj]
  by_cases hjc : decide (curr.toNat * 3 ≥ tot.toNat * 2) = true
  · rw [ite_eq_left hjc]
    show (EthCLSpecs.Heze.previousEpochOf (pureState v)).toNat ≤
      (EthCLSpecs.Heze.currentEpochOf (pureState v)).toNat ∧
      (EthCLSpecs.Heze.currentEpochOf (pureState v)).toNat ≤ _
    omega
  · rw [ite_eq_right hjc, ite_eq_left hjp]
    show (EthCLSpecs.Heze.previousEpochOf (pureState v)).toNat ≤
      (EthCLSpecs.Heze.previousEpochOf (pureState v)).toNat ∧
      (EthCLSpecs.Heze.previousEpochOf (pureState v)).toNat ≤ _
    omega

/-- **The justified epoch below the honest tip.** Take a state `s` after the first two epochs
whose honest validators of the target test of the previous epoch `e₀` have their flags and hold
two thirds of the total. A run from `s` with no honest validator slashed and readable totals
ends at `w`:

- `w` in the epoch of `s`: the target test of `e₀` passes at `w` (`jp_along`), so the pull-up
  of `w` justifies `e₀` or later (`pullup_cj_ge`).
- `w` in the next epoch: the run crosses one boundary at a state `v` of the epoch of `s`. The
  test of `e₀` passes at `v`, so the weigh step justifies `e₀` or later
  (`SlotStep.weigh`), and the steps of the next epoch keep it (`ChainRun.ckView_of_epoch`). -/
theorem leaf_cj [EthCLLib.Spec.CryptoBackend] {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1)
    {q : List ChainStep} {s w : EthCLSpecs.Heze.BeaconState} (h : ChainRun hi q s w)
    {honestOf : EthCLSpecs.Heze.ValidatorIndex → Bool}
    (h2 : 2 ≤ s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch)
    (hw₀ : CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState s)) (pureState s))
    (hw₁ : CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState s)) (pureState s))
    (hus : ∀ j < s.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (s.validators.val[j]!).slashed = false)
    (hflags : ∀ x ∈ honestList s honestOf (EthCLSpecs.Heze.previousEpochOf (pureState s)),
      TargetFlagSet s x.toNat (EthCLSpecs.Heze.previousEpochOf (pureState s)))
    (hstake : 3 * honestStake s honestOf (EthCLSpecs.Heze.previousEpochOf (pureState s)) ≥
      2 * (totBal s).toNat)
    (hall : ∀ p r z, q = p ++ r → ChainRun hi p s z →
      (∀ j < z.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (z.validators.val[j]!).slashed = false) ∧ RunTotals z) :
    (w.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch =
        s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch →
      ∀ pulled, runPure (EthCLSpecs.Heze.processJustificationAndFinalization
        (StateTransition := HezeRun)) w = .ok ((), pulled) →
      s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch - 1 ≤
        pulled.currentJustifiedCheckpoint.epoch.toNat ∧
      pulled.currentJustifiedCheckpoint.epoch.toNat ≤
        s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch) ∧
    (w.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch =
        s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch + 1 →
      s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch - 1 ≤
        w.currentJustifiedCheckpoint.epoch.toNat ∧
      w.currentJustifiedCheckpoint.epoch.toNat ≤
        s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch) := by
  have hp := EthCLSpecs.Heze.Const.slotsPerEpochPos
  have hPs := previousEpochOf_toNat_sub s
  have hCs : (EthCLSpecs.Heze.currentEpochOf (pureState s)).toNat =
      s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := currentEpochOf_toNat s
  have hne : EthCLSpecs.Heze.previousEpochOf (pureState s) ≠
      EthCLSpecs.Heze.currentEpochOf (pureState s) := fun he => by
    have := congrArg UInt64.toNat he
    omega
  refine ⟨fun hep pulled hpl => ?_, fun hep => ?_⟩
  · -- `w` is in the epoch of `s`. The pull-up read the counted indices of the previous epoch.
    obtain ⟨huz, htot⟩ := hall q [] w (List.append_nil _).symm h
    have hPw : EthCLSpecs.Heze.previousEpochOf (pureState w) =
        EthCLSpecs.Heze.previousEpochOf (pureState s) := (epochs_eq_of_toNat hep).2
    have hgw : ¬ EthCLSpecs.Heze.currentEpochOf (pureState w) ≤
        EthCLSpecs.Heze.Const.genesisEpoch + 1 := by
      intro h'
      have hg' := UInt64.le_iff_toNat_le.mp h'
      have hCw : (EthCLSpecs.Heze.currentEpochOf (pureState w)).toNat =
          w.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := currentEpochOf_toNat w
      rw [hCw] at hg'
      simp [EthCLSpecs.Heze.Const.genesisEpoch] at hg'
      omega
    obtain ⟨idx, -, -, -, -, hidx, -⟩ := processJustificationAndFinalization_run_ok hpl hgw
    rw [hPw] at hidx
    have hjp := jp_along hhi h hep.symm rfl hne hw₀ hw₁ hus huz hflags hstake htot hidx
    have hj : jpOf w = true := by
      unfold jpOf
      rw [hPw]
      exact decide_eq_true hjp
    have := pullup_cj_ge hpl (by omega) hj
    rw [hPw, hPs, hep] at this
    exact this
  · -- `w` is in the next epoch: the run crosses the boundary at `v`.
    obtain ⟨v, s₁, s₂, hq, hrv, hbv, hev⟩ := h.weighAt_of_cross hhi
      (s.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch)
      (by have := Nat.lt_div_mul_add (a := s.slot.toNat) hp; rw [Nat.succ_mul]; omega)
      (by rw [← hep]; exact Nat.div_mul_le_self _ _)
    obtain ⟨huv, htot⟩ := hall s₁ (.slot :: s₂) v hq hrv
    have hPv : EthCLSpecs.Heze.previousEpochOf (pureState v) =
        EthCLSpecs.Heze.previousEpochOf (pureState s) := (epochs_eq_of_toNat hev).2
    -- The boundary step and the rest of the run.
    have h' := h
    rw [hq] at h'
    obtain ⟨m, hm1, hm2⟩ := h'.split
    rw [← hrv.det hm1] at hm2
    obtain ⟨v', hlt, hstep, hrest⟩ : ∃ v', v.slot.toNat < hi ∧ SlotStep v v' ∧
        ChainRun hi s₂ v' w := by
      cases hm2 with
      | slot hlt hstep hrest => exact ⟨_, hlt, hstep, hrest⟩
    -- The boundary step read the counted indices of the previous epoch.
    obtain ⟨idx, hidx⟩ := hstep.prev_read_ok (by omega) hbv (by omega)
    rw [hPv] at hidx
    have hjp := jp_along hhi hrv hev.symm rfl hne hw₀ hw₁ hus huv hflags hstake htot hidx
    have hs' := hstep.slot (by omega)
    have hev' : v'.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch =
        w.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := by
      rw [hs', succ_div_of_mod_eq hbv, hev, hep]
    have hck := hrest.ckView_of_epoch hhi hev'
    have hcw : w.currentJustifiedCheckpoint = v'.currentJustifiedCheckpoint :=
      congrArg (fun x => x.2.1) hck
    rw [hcw]
    rcases hstep.weigh (by omega) hbv with ⟨hle, -⟩ | ⟨-, pr, cr, -, hc, -⟩
    · omega
    · rw [hc]
      have hjv : decide ((tgtBal v (EthCLSpecs.Heze.previousEpochOf (pureState v))).toNat * 3 ≥
          (totBal v).toNat * 2) = true := by
        rw [hPv]
        exact decide_eq_true hjp
      have hCv : (EthCLSpecs.Heze.currentEpochOf (pureState v)).toNat =
          v.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := currentEpochOf_toNat v
      by_cases hjc : decide ((tgtBal v (EthCLSpecs.Heze.currentEpochOf (pureState v))).toNat * 3 ≥
          (totBal v).toNat * 2) = true
      · rw [ite_eq_left hjc]
        show _ ≤ (EthCLSpecs.Heze.currentEpochOf (pureState v)).toNat ∧
          (EthCLSpecs.Heze.currentEpochOf (pureState v)).toNat ≤ _
        omega
      · rw [ite_eq_right hjc, ite_eq_left hjv]
        show _ ≤ (EthCLSpecs.Heze.previousEpochOf (pureState v)).toNat ∧
          (EthCLSpecs.Heze.previousEpochOf (pureState v)).toNat ≤ _
        rw [hPv, hPs]
        omega

/-- **EMPTY `r` is viable when every leaf below a tip below it passes, once FULL `r` is.**
Suppose that the filtered tree holds FULL `r`. A leaf below FULL `r` then passes the leaf check
(`go_kept_leaf`). From that leaf, `hleaf` gives every leaf below `pending T`. So `pending T` is
kept (`kept_of_leaves`), and EMPTY `r` above it is in the tree (`emptyViable_of_kept`). A FULL
node on the path to `pending T` has a verified payload (`FullVerified.path`). -/
theorem emptyViable_of_tip (store : Store map) (hslots : SlotsIncrease store)
    (hfv : FullVerified store) {jb : EthCLSpecs.Heze.BeaconBlock}
    (hj : FcMap.lookup store.blocks store.justifiedCheckpoint.root = some jb)
    (r T : EthCLSpecs.Heze.Root) (hrT : NodeBelow store (.empty r) (.pending T))
    (hJr : NodeBelow store (.pending store.justifiedCheckpoint.root) (.empty r))
    (hleaf : ∀ dF : ForkChoiceNode, NodeBelow store (.full r) dF →
      (∃ u₀, (leafOk store dF).run u₀ = .ok (true, u₀)) →
      ∀ d, NodeBelow store (.pending T) d → ∀ u cs,
        (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store d).run u
          = .ok (cs, u) → cs.isEmpty = true → (leafOk store d).run u = .ok (true, u)) :
    EmptyViableWithFull store r := by
  intro nodes t t' hrun hfull
  have hrun' : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root)).run t = .ok (nodes, t') := hrun
  obtain ⟨ht, -⟩ := (filterNodeTree_go_stateFree store _ _).run_eq hrun'
  subst t'
  -- A passing leaf below FULL `r`.
  obtain ⟨dF, hdF, -, hdFok⟩ := go_kept_leaf store _ _ t nodes hrun' (.full r)
    (Array.contains_iff_mem.mp hfull)
  have hkept : KeptAt store (.pending T) :=
    kept_of_leaves store hslots _ (hleaf dF hdF ⟨t, hdFok⟩)
  exact emptyViable_of_kept store hslots hj r (.pending T) hkept hrT
    (fun h => payloadStatus_empty_ne_pending (congrArg ForkChoiceNode.payloadStatus h).symm) hJr
    (fun z _ hz => hfv.path z T hz) nodes t t hrun hfull

/-- **`emptyViable_of_tip` for a tip node `m` at or below EMPTY `r`.** For `m` strictly below,
it is `emptyViable_of_kept`. For `m = empty r`, the kept node is EMPTY `r` itself, and the walk
from the justified root keeps it (`go_keeps_desc`). -/
theorem emptyViable_of_node (store : Store map) (hslots : SlotsIncrease store)
    {jb : EthCLSpecs.Heze.BeaconBlock}
    (hj : FcMap.lookup store.blocks store.justifiedCheckpoint.root = some jb)
    (r : EthCLSpecs.Heze.Root) (m : ForkChoiceNode) (hrm : NodeBelow store (.empty r) m)
    (hJr : NodeBelow store (.pending store.justifiedCheckpoint.root) (.empty r))
    (hJfull : ∀ z, NodeBelow store (.pending store.justifiedCheckpoint.root) (.full z) →
      NodeBelow store (.full z) (.empty r) → isPayloadVerified store z = true)
    (hver : ∀ z, NodeBelow store (.full z) m → NodeBelow store (.empty r) (.full z) →
      isPayloadVerified store z = true)
    (hleaf : ∀ dF : ForkChoiceNode, NodeBelow store (.full r) dF →
      (∃ u₀, (leafOk store dF).run u₀ = .ok (true, u₀)) →
      ∀ d, NodeBelow store m d → ∀ u cs,
        (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map)) store d).run u
          = .ok (cs, u) → cs.isEmpty = true → (leafOk store d).run u = .ok (true, u)) :
    EmptyViableWithFull store r := by
  intro nodes t t' hrun hfull
  have hrun' : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root)).run t = .ok (nodes, t') := hrun
  obtain ⟨ht, -⟩ := (filterNodeTree_go_stateFree store _ _).run_eq hrun'
  subst t'
  obtain ⟨dF, hdF, -, hdFok⟩ := go_kept_leaf store _ _ t nodes hrun' (.full r)
    (Array.contains_iff_mem.mp hfull)
  have hkept : KeptAt store m := kept_of_leaves store hslots _ (hleaf dF hdF ⟨t, hdFok⟩)
  -- EMPTY `r` is kept: it is `m`, or a strict ancestor of `m`.
  have hke : KeptAt store (.empty r) := by
    by_cases hme : m = .empty r
    · rw [← hme]
      exact hkept
    · intro K P xb u ys hxb hP hPs hxP hbud hys
      exact go_keeps_anc store hslots m hkept K (.empty r) P xb u ys hxb hP hPs hxP hbud hys hrm
        (Ne.symm hme) (fun z hz hzm => hver z hzm hz)
  have hbud : Budget store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root) [store.justifiedCheckpoint.root] := by
    simp only [Budget, ForkChoiceNode.pending, ite_true, List.length_singleton]
    omega
  rw [Array.contains_iff_mem]
  exact go_keeps_desc store hslots (.empty r) hke _ _ [store.justifiedCheckpoint.root] jb t nodes hj
    (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun y hy => by rw [List.mem_singleton.mp hy]; exact ⟨jb, hj, UInt64.le_refl _⟩)
    (List.mem_singleton_self _) hbud hrun' hJr hJfull

omit [Config] in
/-- **A node whose blocks after `r` all start after the epoch has the checkpoint block of
`r`.** Each block edge on the path from `r` goes to a block after the first slot `S` of the
epoch, so the child and its parent have one checkpoint block (`getCheckpointBlock_child_eq`). An
EMPTY or FULL edge keeps the root. -/
theorem cb_below_eq (store : Store map) (hslots : SlotsIncrease store) {r : EthCLSpecs.Heze.Root}
    {rb : EthCLSpecs.Heze.BeaconBlock} (hrb : FcMap.lookup store.blocks r = some rb)
    (e : EthCLSpecs.Heze.Epoch) (S : EthCLSpecs.Heze.Slot)
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch e :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) = .ok S)
    {x : ForkChoiceNode} (hx : NodeBelow store (.pending r) x)
    (hpath : ∀ y, NodeBelow store (.pending r) y → NodeBelow store y x → y.root ≠ r →
      ∃ yb, FcMap.lookup store.blocks y.root = some yb ∧ S < yb.slot) :
    ∀ u, (EthCLSpecs.Heze.getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
        store x.root e).run u =
      (EthCLSpecs.Heze.getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
        store r e).run u := by
  revert hpath
  induction hx with
  | refl => intro _ u; rfl
  | step p c hpd hedge ih =>
    intro hpath
    have ih' := ih fun y hy hyp hne => hpath y hy (.step _ _ hyp hedge) hne
    cases hedge with
    | empty root => exact ih'
    | full root => exact ih'
    | block _ root b s s' hb hpar hps =>
      by_cases hr : root = r
      · intro u
        show (EthCLSpecs.Heze.getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
          store root e).run u = _
        rw [hr]
      · obtain ⟨yb, hyb, hlt⟩ := hpath (.pending root)
          (.step _ _ hpd (.block _ root b s s' hb hpar hps)) .refl hr
        change FcMap.lookup store.blocks root = some yb at hyb
        rw [hb] at hyb
        cases hyb
        -- The parent's block.
        obtain ⟨pb, hpb⟩ : ∃ pb, FcMap.lookup store.blocks p.root = some pb := by
          by_cases hp : p.root = r
          · exact ⟨rb, hp ▸ hrb⟩
          · obtain ⟨pb, hpb, -⟩ := hpath p hpd (.step _ _ .refl (.block _ root b s s' hb hpar hps)) hp
            exact ⟨pb, hpb⟩
        intro u
        exact (getCheckpointBlock_child_eq store hslots hpb hb hpar e S hS hlt u).trans (ih' u)

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- `finRead` reads no runner state. -/
theorem finRead_stateFree (store : Store map) (x : EthCLSpecs.Heze.Root) :
    EthCLLib.Proofs.StateFree (finRead store x) := by
  unfold finRead
  rw [map_eq_pure_bind]
  unfold EthCLSpecs.Heze.getCheckpointBlock EthCLSpecs.Heze.getAncestor
    EthCLSpecs.Heze.getParentPayloadStatus EthCLLib.Spec.liftErr
  dsimp only
  free_solve

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A passing leaf check passes the finalized test, at every runner state. `leafOk` ends with
`pure (correctJustified && correctFinalized)`. -/
theorem finRead_of_leafOk (store : Store map) (n : ForkChoiceNode) {u : Store map}
    (h : (leafOk store n).run u = .ok (true, u)) :
    ∀ t, (finRead store n.root).run t = .ok (true, t) := by
  rw [leafOk_eq_finRead] at h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
  split at h
  · try simp only [pure_bind] at h
    obtain ⟨cf, _, h3, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
    obtain ⟨hc, -⟩ := EthCLLib.Proofs.run_pure_eq_ok_state h
    have hcf : cf = true := by simpa using hc
    subst hcf
    exact ((finRead_stateFree store n.root).run_eq h3).2
  · obtain ⟨_, _, -, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
    try simp only [pure_bind] at h
    obtain ⟨cf, _, h4, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
    obtain ⟨hc, -⟩ := EthCLLib.Proofs.run_pure_eq_ok_state h
    have hcf : cf = true := by
      cases cf
      · simp at hc
      · rfl
    subst hcf
    exact ((finRead_stateFree store n.root).run_eq h4).2

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A node strictly above a decided node of `r` is at or above `pending r`: the only edge into
the EMPTY or FULL node of `r` comes from `pending r`. -/
theorem below_decided_pending {store : Store map} {n x : ForkChoiceNode} (h : NodeBelow store n x)
    (hx : x.payloadStatus ≠ EthCLSpecs.Heze.Const.payloadStatusPending) (hne : n ≠ x) :
    NodeBelow store n (.pending x.root) := by
  cases h with
  | refl => exact absurd rfl hne
  | step p c hpd hedge =>
    cases hedge with
    | empty root => exact hpd
    | full root => exact hpd
    | block _ root b s s' _ _ _ => exact absurd rfl hx

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **A stored block hangs below the decided node of its parent that its bid names.** The bid
names the parent's payload hash or not; `get_parent_payload_status` reads FULL or EMPTY from
that, and the block edge goes from that decided node. -/
theorem child_edge {store : Store map} {c : EthCLSpecs.Heze.Root}
    {cb pb : EthCLSpecs.Heze.BeaconBlock} (hc : FcMap.lookup store.blocks c = some cb)
    (hp : FcMap.lookup store.blocks cb.parentRoot = some pb) :
    ((cb.body.signedExecutionPayloadBid.message.parentBlockHash ==
        pb.body.signedExecutionPayloadBid.message.blockHash) = false →
      NodeEdge store (.empty cb.parentRoot) (.pending c)) ∧
    ((cb.body.signedExecutionPayloadBid.message.parentBlockHash ==
        pb.body.signedExecutionPayloadBid.message.blockHash) = true →
      NodeEdge store (.full cb.parentRoot) (.pending c)) := by
  have hs : ∀ u, (EthCLSpecs.Heze.getParentPayloadStatus
      (StoreTransition := ForkChoiceStoreRun (Store map)) store cb).run u =
      .ok ((if (cb.body.signedExecutionPayloadBid.message.parentBlockHash ==
        pb.body.signedExecutionPayloadBid.message.blockHash) = true then
          EthCLSpecs.Heze.Const.payloadStatusFull else EthCLSpecs.Heze.Const.payloadStatusEmpty), u) := by
    intro u
    unfold EthCLSpecs.Heze.getParentPayloadStatus
    rw [EthCLLib.Proofs.run_bind, getOrThrow_run_of_lookup _ _ _ hp u,
      EthCLLib.Proofs.except_bind_ok]
    rfl
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have h := hs store
    rw [hne] at h
    exact .block (.empty cb.parentRoot) c cb store store hc rfl h
  · have h := hs store
    rw [heq] at h
    exact .block (.full cb.parentRoot) c cb store store hc rfl h

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A stored block with a stored parent is below the pending node of its parent. -/
theorem child_below {store : Store map} {c : EthCLSpecs.Heze.Root}
    {cb pb : EthCLSpecs.Heze.BeaconBlock} (hc : FcMap.lookup store.blocks c = some cb)
    (hp : FcMap.lookup store.blocks cb.parentRoot = some pb) :
    NodeBelow store (.pending cb.parentRoot) (.pending c) := by
  obtain ⟨he, hf⟩ := child_edge hc hp
  cases h : (cb.body.signedExecutionPayloadBid.message.parentBlockHash ==
      pb.body.signedExecutionPayloadBid.message.blockHash)
  · exact .step _ _ (.step _ _ .refl (NodeEdge.empty _)) (he h)
  · exact .step _ _ (.step _ _ .refl (NodeEdge.full _)) (hf h)

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- Every node below a stored node has a stored block at its root. -/
theorem below_stored {store : Store map} {n d : ForkChoiceNode} (h : NodeBelow store n d)
    {nb : EthCLSpecs.Heze.BeaconBlock} (hn : FcMap.lookup store.blocks n.root = some nb) :
    ∃ db, FcMap.lookup store.blocks d.root = some db := by
  induction h with
  | refl => exact ⟨nb, hn⟩
  | step p c _ hedge ih =>
    cases hedge with
    | empty root => exact ih
    | full root => exact ih
    | block _ root b _ _ hb _ _ => exact ⟨b, hb⟩

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- A node below `pending r` other than the three nodes of `r` has a block later than `r`. -/
theorem below_slot_gt (store : Store map) (hslots : SlotsIncrease store)
    {r : EthCLSpecs.Heze.Root} {rb : EthCLSpecs.Heze.BeaconBlock}
    (hrb : FcMap.lookup store.blocks r = some rb) {y : ForkChoiceNode}
    (hy : NodeBelow store (.pending r) y) (hne : y.root ≠ r) :
    ∃ yb, FcMap.lookup store.blocks y.root = some yb ∧ rb.slot < yb.slot := by
  have hyp : y ≠ .pending r := fun h => hne (by rw [h]; rfl)
  rcases NodeBelow.pending_split store r y hy hyp with h | h
  · rcases NodeBelow.slot_gt_decided store hslots (.empty r) payloadStatus_empty_ne_pending rb hrb
      y h with h' | h'
    · exact absurd (by rw [h']; rfl) hne
    · exact h'
  · rcases NodeBelow.slot_gt_decided store hslots (.full r) payloadStatus_full_ne_pending rb hrb
      y h with h' | h'
    · exact absurd (by rw [h']; rfl) hne
    · exact h'

omit [Config] [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- The checkpoint block of `r` is `r` when the epoch starts at or after the block. -/
theorem cb_self (store : Store map) {r : EthCLSpecs.Heze.Root} {rb : EthCLSpecs.Heze.BeaconBlock}
    (hrb : FcMap.lookup store.blocks r = some rb) (e : EthCLSpecs.Heze.Epoch)
    (S : EthCLSpecs.Heze.Slot)
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch e :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) = .ok S)
    (hle : ¬ rb.slot > S) (u : Store map) :
    (EthCLSpecs.Heze.getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      store r e).run u = .ok (r, u) := by
  unfold EthCLSpecs.Heze.getCheckpointBlock
  rw [hS]
  show (do
    let a ← EthCLSpecs.Heze.getAncestor (StoreTransition := ForkChoiceStoreRun (Store map))
      store (.pending r) S
    pure a.root).run u = _
  rw [getAncestor_eq_fuelLoop, EthCLLib.Proofs.run_bind]
  simp only [EthCLLib.Spec.fuelLoop, EthCLLib.Proofs.run_bind,
    ancStep_run_done store S (.pending r) rb hrb hle u, EthCLLib.Proofs.except_bind_ok]
  rfl

omit [Config] in
/-- **The finalized test of a leaf below `r`.** `dF` below `pending r` passes the test. Take the
first slot `S` of the finalized epoch:

- `S` before the block of `r`: the blocks below `r` other than `r` come after `S`, so `d`,
  `dF`, and `r` have one checkpoint block (`cb_below_eq`), and `d` passes as `dF` does;
- `S` at or after the block of `r`: `hlate` gives the finalized root `r` (or the genesis
  epoch) and blocks after `S` on the path from `r` to `d`, so the checkpoint block of `d` is
  `r` (`cb_below_eq`, `cb_self`). -/
theorem leaf_fin (store : Store map) (hslots : SlotsIncrease store) {r : EthCLSpecs.Heze.Root}
    {rb : EthCLSpecs.Heze.BeaconBlock} (hrb : FcMap.lookup store.blocks r = some rb)
    {S : EthCLSpecs.Heze.Slot}
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch store.finalizedCheckpoint.epoch :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) = .ok S)
    {dF : ForkChoiceNode} (hdF : NodeBelow store (.pending r) dF) {u₀ : Store map}
    (hfF : (finRead store dF.root).run u₀ = .ok (true, u₀))
    {d : ForkChoiceNode} (hd : NodeBelow store (.pending r) d)
    (hlate : ¬ S < rb.slot →
      (store.finalizedCheckpoint.epoch = EthCLSpecs.Heze.Const.genesisEpoch ∨
        store.finalizedCheckpoint.root = r) ∧
      ∀ y, NodeBelow store (.pending r) y → NodeBelow store y d → y.root ≠ r →
        ∃ yb, FcMap.lookup store.blocks y.root = some yb ∧ S < yb.slot)
    (u : Store map) : (finRead store d.root).run u = .ok (true, u) := by
  obtain ⟨-, hfF'⟩ := (finRead_stateFree store dF.root).run_eq hfF
  by_cases hSr : S < rb.slot
  · have hp : ∀ (x y : ForkChoiceNode), NodeBelow store (.pending r) y → NodeBelow store y x →
        y.root ≠ r → ∃ yb, FcMap.lookup store.blocks y.root = some yb ∧ S < yb.slot :=
      fun _ y hy _ hne => by
      obtain ⟨yb, hyb, hlt⟩ := below_slot_gt store hslots hrb hy hne
      exact ⟨yb, hyb, UInt64.lt_trans hSr hlt⟩
    have e1 := cb_below_eq store hslots hrb _ S hS hd (hp d)
    have e2 := cb_below_eq store hslots hrb _ S hS hdF (hp dF)
    rw [finRead_eq_of store d.root dF.root u (.inl ((e1 u).trans (e2 u).symm))]
    exact hfF' u
  · obtain ⟨hg, hp⟩ := hlate hSr
    have e1 := cb_below_eq store hslots hrb _ S hS hd hp
    unfold finRead
    rw [StateT.run_map, e1 u, cb_self store hrb _ S hS (fun h => hSr h) u]
    rcases hg with h | h
    · simp [Functor.map, Except.map, h]
    · simp [Functor.map, Except.map, h]

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **The voting source of a leaf below the honest tip is recent.** `T` is a stored block of
epoch `E - 1`, not the anchor, and its stored state `sT` meets the premises of `leaf_cj`. A
node `d` below `pending T` has a stored state reached from `sT` by a run
(`NodeBelow.stateRun`), at the slot of its block. Its block is from epoch `E - 1` or `E`:

- epoch `E - 1`: `get_voting_source` reads the unrealized justification, the pull-up of the
  stored state (`UnrealInv`), which `leaf_cj` bounds;
- epoch `E`: it reads the justified checkpoint of the stored state, which `leaf_cj` bounds.

The voting source epoch is `E - 2` or `E - 1`, so the horizon sum does not overflow. -/
theorem leaf_vs_store [EthCLLib.Spec.CryptoBackend]
    [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
      EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
    {store : Store map} {A : EthCLSpecs.Heze.BeaconState} {a : EthCLSpecs.Heze.BeaconBlock}
    (hslot : SlotInv a store) (hlink : StateLink (htr a) store)
    (hzr : ∀ k b, FcMap.lookup store.blocks k = some b → k ≠ htr a →
      b.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hunr : UnrealInv (htr a) store) (hkeys : UnrealKeys store)
    {T : EthCLSpecs.Heze.Root} (hTa : T ≠ htr a) {sT : EthCLSpecs.Heze.BeaconState}
    (hsT : FcMap.lookup store.blockStates T = some (pureState sT))
    {preT : List ChainStep} (hpreT : ChainRun (2 ^ 64 - 1) preT A sT)
    (hpathT : AncestorPath a store T (blocksOf preT)) (hvalT : ValidatedSteps preT)
    (hendT : EndsAtBlock preT)
    {d : ForkChoiceNode} (hd : NodeBelow store (.pending T) d)
    (hna : ∀ y, NodeBelow store (.pending T) y → y.root = htr a → y.root = T)
    {db : EthCLSpecs.Heze.BeaconBlock} (hdb : FcMap.lookup store.blocks d.root = some db)
    {E : EthCLSpecs.Heze.Epoch} (u : Store map)
    (hE : (EthCLSpecs.Heze.getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run u = .ok (E, u))
    (hET : E.toNat = sT.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch + 1)
    (hdE : (EthCLSpecs.Heze.computeEpochAtSlot db.slot).toNat ≤ E.toNat)
    (hroom : E.toNat + 2 < 2 ^ 64)
    {honestOf : EthCLSpecs.Heze.ValidatorIndex → Bool}
    (h2 : 2 ≤ sT.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch)
    (hw₀ : CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState sT)) (pureState sT))
    (hw₁ : CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState sT)) (pureState sT))
    (hus : ∀ j < sT.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (sT.validators.val[j]!).slashed = false)
    (hflags : ∀ x ∈ honestList sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)),
      TargetFlagSet sT x.toNat (EthCLSpecs.Heze.previousEpochOf (pureState sT)))
    (hstake : 3 * honestStake sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)) ≥
      2 * (totBal sT).toNat)
    (hall : ∀ p q z, StoreRun A a store (p ++ q) → ChainRun (2 ^ 64 - 1) p A z →
      (∀ j < z.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (z.validators.val[j]!).slashed = false) ∧ RunTotals z) :
    ∃ vs : EthCLSpecs.Heze.Checkpoint,
      (EthCLSpecs.Heze.getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map))
        store d.root).run u = .ok (vs, u) ∧
      E.toNat ≤ vs.epoch.toNat + 2 ∧ vs.epoch.toNat + 2 < 2 ^ 64 := by
  have hh : (2 ^ 64 - 1 : Nat) ≤ 2 ^ 64 - 1 := Nat.le_refl _
  obtain ⟨q, wd, hwd, hq, hsr⟩ := NodeBelow.storeRun hslot hlink hzr hd hna hsT hpreT hpathT
    hvalT hendT
  have hcj := leaf_cj hh hq h2 hw₀ hw₁ hus hflags hstake fun p r z hqe hz =>
    hall (preT ++ p) r z (by rw [List.append_assoc, ← hqe]; exact hsr) (hpreT.append hz)
  -- The node is not the anchor, and its state has the slot of its block.
  have hd0 : d.root ≠ htr a := fun h0 => hTa ((hna d hd h0).symm.trans h0)
  obtain ⟨sb, pv, w', hsb, -, hw', ht⟩ := hlink d.root db hdb hd0
  rw [hwd] at hw'
  injection hw' with hw'
  have hw'' := pureState_inj hw'
  subst hw''
  have hslot : wd.slot.toNat = db.slot.toNat := by rw [transition_slot ht, hsb]
  have hdb' := computeEpochAtSlot_toNat db.slot
  have hle := hq.epoch_le hh
  by_cases hlt : E > EthCLSpecs.Heze.computeEpochAtSlot db.slot
  · -- An earlier epoch: the unrealized justification, the pull-up of the stored state.
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hkeys d.root db hdb)
    rcases hunr.2 d.root j hj with h0 | ⟨v, pulled, hv, hjf, rfl⟩
    · exact absurd h0 hd0
    rw [hwd] at hv
    injection hv with hv
    have hv' := pureState_inj hv
    subst hv'
    have hep : wd.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch =
        sT.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := by
      rw [hslot] at hle ⊢
      omega
    obtain ⟨b1, b2⟩ := hcj.1 hep pulled hjf
    refine ⟨pulled.currentJustifiedCheckpoint,
      getVotingSource_run_unreal store d.root db hdb E u hE hlt _ hj, ?_, ?_⟩ <;> omega
  · -- The current epoch: the justified checkpoint of the stored state.
    have hge : ¬ (EthCLSpecs.Heze.computeEpochAtSlot db.slot).toNat < E.toNat := fun h' =>
      hlt (UInt64.lt_iff_toNat_lt.mpr h')
    have hep : wd.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch =
        sT.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch + 1 := by
      rw [hslot]
      omega
    obtain ⟨b1, b2⟩ := hcj.2 hep
    refine ⟨wd.currentJustifiedCheckpoint,
      getVotingSource_run_state store d.root db hdb E u hE hlt wd hwd, ?_, ?_⟩ <;> omega

omit [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root] in
/-- **In the epoch of `rb`, a node below `pending r` reads the voting source of `r`.** Its block
is at or after `rb`, and in the current epoch, so `get_voting_source` reads the justified
checkpoint of its stored state. That state comes from the state of `r` by a run inside the
epoch (`NodeBelow.stateRun`), which keeps the checkpoint (`ChainRun.ckView_of_epoch`). -/
theorem votingSource_same_epoch [EthCLLib.Spec.CryptoBackend]
    [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
      EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
    (store : Store map) (hslots : SlotsIncrease store) {a0 : EthCLSpecs.Heze.Root}
    (hlink : StateLink a0 store) {r : EthCLSpecs.Heze.Root} {rb : EthCLSpecs.Heze.BeaconBlock}
    (hrb : FcMap.lookup store.blocks r = some rb) (hra : r ≠ a0)
    (hna : ∀ y, NodeBelow store (.pending r) y → y.root = a0 → y.root = r)
    {E : EthCLSpecs.Heze.Epoch}
    (hE : ∀ u, (EthCLSpecs.Heze.getCurrentStoreEpoch
      (StoreTransition := ForkChoiceStoreRun (Store map)) store).run u = .ok (E, u))
    (hrE : EthCLSpecs.Heze.computeEpochAtSlot rb.slot = E)
    (hclock : ∀ k b, FcMap.lookup store.blocks k = some b →
      (EthCLSpecs.Heze.computeEpochAtSlot b.slot).toNat ≤ E.toNat)
    {d : ForkChoiceNode} (hd : NodeBelow store (.pending r) d) :
    ∃ wr : EthCLSpecs.Heze.BeaconState,
      FcMap.lookup store.blockStates r = some (pureState wr) ∧
      ∀ u, (EthCLSpecs.Heze.getVotingSource (StoreTransition := ForkChoiceStoreRun (Store map))
        store d.root).run u = .ok (wr.currentJustifiedCheckpoint, u) := by
  have hh : (2 ^ 64 - 1 : Nat) ≤ 2 ^ 64 - 1 := Nat.le_refl _
  obtain ⟨sb, pv, wr, hsb, -, hwr, ht⟩ := hlink r rb hrb hra
  refine ⟨wr, hwr, fun u => ?_⟩
  obtain ⟨q, wd, hwd, hq⟩ := NodeBelow.stateRun hlink hd hna hwr
  obtain ⟨db, hdb⟩ := below_stored hd hrb
  have hEn := computeEpochAtSlot_toNat db.slot
  have hrn := computeEpochAtSlot_toNat rb.slot
  rw [hrE] at hrn
  -- The block of `d` is at or after `rb`.
  have hge : rb.slot.toNat ≤ db.slot.toNat := by
    by_cases hr : d.root = r
    · rw [hr, hrb] at hdb
      cases hdb
      exact Nat.le_refl _
    · obtain ⟨yb, hyb, hlt⟩ := below_slot_gt store hslots hrb hd hr
      rw [hdb] at hyb
      cases hyb
      exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt)
  have hdE := hclock _ _ hdb
  have hle : ¬ E > EthCLSpecs.Heze.computeEpochAtSlot db.slot := fun h' => by
    have := UInt64.lt_iff_toNat_lt.mp h'
    have := Nat.div_le_div_right (c := EthCLSpecs.Heze.Const.slotsPerEpoch) hge
    omega
  rw [getVotingSource_run_state store d.root db hdb E u (hE u) hle wd hwd]
  -- The state of `d` is in the epoch of the state of `r`.
  have hd0 : d.root ≠ a0 := fun h0 => hra ((hna d hd h0).symm.trans h0)
  obtain ⟨sb', pv', w', hsb', -, hw', ht'⟩ := hlink d.root db hdb hd0
  rw [hwd] at hw'
  injection hw' with hw'
  have hw'' := pureState_inj hw'
  subst hw''
  have hsd : wd.slot.toNat = db.slot.toNat := by rw [transition_slot ht', hsb']
  have hsr : wr.slot.toNat = rb.slot.toNat := by rw [transition_slot ht, hsb]
  have hep : wr.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch =
      wd.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch := by
    rw [hsd, hsr]
    have := Nat.div_le_div_right (c := EthCLSpecs.Heze.Const.slotsPerEpoch) hge
    omega
  have hck := hq.ckView_of_epoch hh hep
  have hcw : wd.currentJustifiedCheckpoint = wr.currentJustifiedCheckpoint :=
    congrArg (fun x => x.2.1) hck
  rw [hcw]

/-- **EMPTY `r` is viable beside FULL `r` in the epoch of `rb`.** Every node below `pending r`
reads the voting source of `r` (`votingSource_same_epoch`). The finalized epoch starts before
`rb`, so every such node has the checkpoint block of `r` (`cb_below_eq`). So a leaf below EMPTY
`r` passes as a passing leaf below FULL `r` does (`leafOk_eq_of_fin`). -/
theorem viable_same_epoch [EthCLLib.Spec.CryptoBackend]
    [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
      EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
    (store : Store map) (hslots : SlotsIncrease store) {a0 : EthCLSpecs.Heze.Root}
    (hlink : StateLink a0 store) {r : EthCLSpecs.Heze.Root} {rb : EthCLSpecs.Heze.BeaconBlock}
    (hrb : FcMap.lookup store.blocks r = some rb) (hra : r ≠ a0)
    (hna : ∀ y, NodeBelow store (.pending r) y → y.root = a0 → y.root = r)
    {jb : EthCLSpecs.Heze.BeaconBlock}
    (hj : FcMap.lookup store.blocks store.justifiedCheckpoint.root = some jb)
    (hJr : NodeBelow store (.pending store.justifiedCheckpoint.root) (.empty r))
    (hJfull : ∀ z, NodeBelow store (.pending store.justifiedCheckpoint.root) (.full z) →
      NodeBelow store (.full z) (.empty r) → isPayloadVerified store z = true)
    {E : EthCLSpecs.Heze.Epoch}
    (hE : ∀ u, (EthCLSpecs.Heze.getCurrentStoreEpoch
      (StoreTransition := ForkChoiceStoreRun (Store map)) store).run u = .ok (E, u))
    (hrE : EthCLSpecs.Heze.computeEpochAtSlot rb.slot = E)
    (hclock : ∀ k b, FcMap.lookup store.blocks k = some b →
      (EthCLSpecs.Heze.computeEpochAtSlot b.slot).toNat ≤ E.toNat)
    {S : EthCLSpecs.Heze.Slot}
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch store.finalizedCheckpoint.epoch :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) = .ok S)
    (hSr : S < rb.slot) :
    EmptyViableWithFull store r := by
  refine emptyViable_of_node store hslots hj r (.empty r) .refl hJr hJfull
    (fun z hz hze => ?_) ?_
  · -- No FULL node lies between EMPTY `r` and itself: slots grow along the loop.
    exfalso
    rcases NodeBelow.slot_gt_decided store hslots (.empty r) payloadStatus_empty_ne_pending rb hrb
        _ hze with h1 | ⟨zb, hzb, hlt1⟩
    · exact payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus h1).symm
    · rcases NodeBelow.slot_gt_decided store hslots (.full z) payloadStatus_full_ne_pending zb hzb
          _ hz with h2 | ⟨rb', hrb', hlt2⟩
      · exact payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus h2)
      · change FcMap.lookup store.blocks r = some rb' at hrb'
        rw [hrb] at hrb'
        cases hrb'
        exact absurd (UInt64.lt_trans hlt1 hlt2) (UInt64.lt_irrefl _)
  rintro dF hdF ⟨u₀, hok⟩ d hd u cs - -
  have hrE' : NodeBelow store (.pending r) (.empty r) := .step _ _ .refl (NodeEdge.empty r)
  have hdr : NodeBelow store (.pending r) d := NodeBelow.trans store _ _ _ hrE' hd
  have hdFr : NodeBelow store (.pending r) dF :=
    NodeBelow.trans store _ _ _ (.step _ _ .refl (NodeEdge.full r)) hdF
  obtain ⟨wr, hwr, hvd⟩ := votingSource_same_epoch store hslots hlink hrb hra hna hE hrE hclock hdr
  obtain ⟨wr', hwr', hvF⟩ := votingSource_same_epoch store hslots hlink hrb hra hna hE hrE hclock
    hdFr
  rw [hwr] at hwr'
  injection hwr' with hwr'
  have hww := pureState_inj hwr'
  subst hww
  have hp : ∀ (x y : ForkChoiceNode), NodeBelow store (.pending r) y → NodeBelow store y x →
      y.root ≠ r → ∃ yb, FcMap.lookup store.blocks y.root = some yb ∧ S < yb.slot :=
    fun _ y hy _ hne => by
      obtain ⟨yb, hyb, hlt⟩ := below_slot_gt store hslots hrb hy hne
      exact ⟨yb, hyb, UInt64.lt_trans hSr hlt⟩
  have e1 := cb_below_eq store hslots hrb _ S hS hdr (hp d)
  have e2 := cb_below_eq store hslots hrb _ S hS hdFr (hp dF)
  have heq : leafOk store d = leafOk store dF :=
    leafOk_eq_of_fin store d dF (fun t => (hvd t).trans (hvF t).symm)
      (fun t => finRead_eq_of store d.root dF.root t (.inl ((e1 t).trans (e2 t).symm)))
  rw [heq]
  exact ((leafOk_stateFree store dF).run_eq hok).2 u

/-- **EMPTY `r` is viable beside FULL `r` at one store.** The tip node `m` lies at or below
EMPTY `r` and below `pending T`, for a stored block `T` that is not the anchor. Every leaf `d`
below `m` passes the leaf check:

- its voting source is recent (`leaf_vs_store`, from the premises of `leaf_cj` at the stored
  state of `T`);
- it passes the finalized test (`leaf_fin`), given a leaf below FULL `r` that passes the check
  and `hlate` for the case where the finalized epoch starts at or after the block of `r`.

So EMPTY `r` is in the filtered tree whenever FULL `r` is (`emptyViable_of_node`). -/
theorem viable_store_core [EthCLLib.Spec.CryptoBackend]
    [EthCLLib.Spec.ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
      EthCLSpecs.Heze.ExecutionRequests] [EthCLLib.Spec.DataAvailability]
    (store : Store map) {A : EthCLSpecs.Heze.BeaconState} {a : EthCLSpecs.Heze.BeaconBlock}
    (hslot : SlotInv a store) (hlink : StateLink (htr a) store)
    (hzr : ∀ k b, FcMap.lookup store.blocks k = some b → k ≠ htr a →
      b.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hunr : UnrealInv (htr a) store) (hkeys : UnrealKeys store)
    {r : EthCLSpecs.Heze.Root} {rb : EthCLSpecs.Heze.BeaconBlock}
    (hrb : FcMap.lookup store.blocks r = some rb) {jb : EthCLSpecs.Heze.BeaconBlock}
    (hj : FcMap.lookup store.blocks store.justifiedCheckpoint.root = some jb)
    (hJr : NodeBelow store (.pending store.justifiedCheckpoint.root) (.empty r))
    (hJfull : ∀ z, NodeBelow store (.pending store.justifiedCheckpoint.root) (.full z) →
      NodeBelow store (.full z) (.empty r) → isPayloadVerified store z = true)
    (m : ForkChoiceNode) (hrm : NodeBelow store (.empty r) m)
    (hver : ∀ z, NodeBelow store (.full z) m → NodeBelow store (.empty r) (.full z) →
      isPayloadVerified store z = true)
    {T : EthCLSpecs.Heze.Root} (hTm : NodeBelow store (.pending T) m) (hTa : T ≠ htr a)
    {tb : EthCLSpecs.Heze.BeaconBlock} (hTb : FcMap.lookup store.blocks T = some tb)
    {sT : EthCLSpecs.Heze.BeaconState}
    (hsT : FcMap.lookup store.blockStates T = some (pureState sT))
    {preT : List ChainStep} (hpreT : ChainRun (2 ^ 64 - 1) preT A sT)
    (hpathT : AncestorPath a store T (blocksOf preT)) (hvalT : ValidatedSteps preT)
    (hendT : EndsAtBlock preT)
    (hna : ∀ y, NodeBelow store (.pending T) y → y.root = htr a → y.root = T)
    {E : EthCLSpecs.Heze.Epoch}
    (hE : ∀ u, (EthCLSpecs.Heze.getCurrentStoreEpoch
      (StoreTransition := ForkChoiceStoreRun (Store map)) store).run u = .ok (E, u))
    (hET : E.toNat = sT.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch + 1)
    (hclock : ∀ k b, FcMap.lookup store.blocks k = some b →
      (EthCLSpecs.Heze.computeEpochAtSlot b.slot).toNat ≤ E.toNat)
    (hroom : E.toNat + 2 < 2 ^ 64)
    {honestOf : EthCLSpecs.Heze.ValidatorIndex → Bool}
    (h2 : 2 ≤ sT.slot.toNat / EthCLSpecs.Heze.Const.slotsPerEpoch)
    (hw₀ : CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState sT)) (pureState sT))
    (hw₁ : CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState sT)) (pureState sT))
    (hus : ∀ j < sT.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (sT.validators.val[j]!).slashed = false)
    (hflags : ∀ x ∈ honestList sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)),
      TargetFlagSet sT x.toNat (EthCLSpecs.Heze.previousEpochOf (pureState sT)))
    (hstake : 3 * honestStake sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)) ≥
      2 * (totBal sT).toNat)
    (hall : ∀ p q z, StoreRun A a store (p ++ q) → ChainRun (2 ^ 64 - 1) p A z →
      (∀ j < z.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (z.validators.val[j]!).slashed = false) ∧ RunTotals z)
    {S : EthCLSpecs.Heze.Slot}
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch store.finalizedCheckpoint.epoch :
      Except EthCLLib.Spec.StateTransitionError EthCLSpecs.Heze.Slot) = .ok S)
    (hlate : ∀ dF, NodeBelow store (.full r) dF →
      (∀ u, (finRead store dF.root).run u = .ok (true, u)) →
      ∀ d, NodeBelow store m d → ¬ S < rb.slot →
      (store.finalizedCheckpoint.epoch = EthCLSpecs.Heze.Const.genesisEpoch ∨
        store.finalizedCheckpoint.root = r) ∧
      ∀ y, NodeBelow store (.pending r) y → NodeBelow store y d → y.root ≠ r →
        ∃ yb, FcMap.lookup store.blocks y.root = some yb ∧ S < yb.slot) :
    EmptyViableWithFull store r := by
  have hslots := hslot.slots
  refine emptyViable_of_node store hslots hj r m hrm hJr hJfull hver ?_
  rintro dF hdF ⟨u₀, hok⟩ d hd u cs - -
  have hfF := finRead_of_leafOk store dF hok
  have hrE : NodeBelow store (.pending r) (.empty r) := .step _ _ .refl (NodeEdge.empty r)
  have hdr : NodeBelow store (.pending r) d :=
    NodeBelow.trans store _ _ _ hrE (NodeBelow.trans store _ _ _ hrm hd)
  have hdFr : NodeBelow store (.pending r) dF :=
    NodeBelow.trans store _ _ _ (.step _ _ .refl (NodeEdge.full r)) hdF
  have hfin := leaf_fin store hslots hrb hS hdFr (hfF u₀) hdr (hlate dF hdF hfF d hd) u
  have hdT : NodeBelow store (.pending T) d := NodeBelow.trans store _ _ _ hTm hd
  obtain ⟨db, hdb⟩ := below_stored hdT hTb
  obtain ⟨vs, hvs, hge, hfit⟩ := leaf_vs_store hslot hlink hzr hunr hkeys hTa hsT hpreT hpathT
    hvalT hendT hdT hna hdb u (hE u) hET (hclock _ _ hdb) hroom h2 hw₀ hw₁ hus hflags hstake hall
  exact leafOk_true_of store d u (hE u) hvs hfit hge hfin

end EthCLSpecs.Proofs.Heze
