import EthCLSpecs.Proofs.Heze.ViableHonest

/-!
# `EthCLSpecs.Proofs.Heze.WindowCheck`: the carrier window as computations

`CarrierWindow` (`ViableHonest.lean`) states its premises over the carrier chain `H` and over the
store runs of the honest stores. A witness evaluates them on one concrete chain `W` with the
states `L` of its run. This module gives a `Bool` check for the premises that quantify over
votes and weigh states, and a lemma that turns each check into its premise.

- `includedB` checks the weigh states of a range of epochs (`included_of_check`).
- `attSetsB` lists each vote of `W` with its attesting indices at the state before its block.
  `singleB` checks that two votes of one honest validator with one target epoch carry one data
  (`single_of_check`).
- `unslashedB` checks that no state of `L` has an honest validator slashed
  (`unslashed_of_check`).

The vote lemmas rest on `RunVote.attesting`: the voter of a placed vote is an attesting index
at the run state before its block. The block keeps the committees of the epoch of the vote up
to the attestation (`BlockReach.keeps_com`), so the attesting indices of `process_attestation`
are those of that state (`getAttestingIndices_eq_of_comView`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState SignedBeaconBlock ValidatorIndex Attestation
  AttestationData getAttestingIndices computeEpochAtSlot previousEpochOf)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

/-- An element at index `n` splits the list there. -/
theorem split_of_getElem? {α : Type} {l : List α} {n : Nat} {x : α} (h : l[n]? = some x) :
    l = l.take n ++ x :: l.drop (n + 1) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
  conv => lhs; rw [← List.take_append_drop n l]
  rw [List.drop_eq_getElem_cons hn, show l[n] = x from
    Option.some.inj ((List.getElem?_eq_getElem hn).symm.trans h)]

section Votes
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **The block step keeps the committees of an epoch up to the attestation.** The functions of
`processBlock` before and inside the attestation loop keep a `comView` whose window flag is
`true` (`CommitteeFrame.lean`). -/
theorem BlockReach.keeps_com {b : EthCLSpecs.Heze.BeaconBlock} {u pre : BeaconState}
    (hr : BlockReach b u pre) {e : EthCLSpecs.Heze.Epoch}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32} (hu : comView e (pureState u) = (true, c)) :
    comView e (pureState pre) = (true, c) :=
  hr (fun s => comView e (pureState s) = (true, c))
    ⟨fun _ _ h hs => processParentExecutionPayload_frame_com h hs,
      fun _ _ h hs => (processBlockHeader_frame_com h).trans hs,
      fun _ _ h hs => (processWithdrawals_frame_com h).trans hs,
      fun _ _ h hs => (processExecutionPayloadBid_frame_com h).trans hs,
      fun _ _ h hs => processRandao_frame_com h hs,
      fun _ _ _ h hs => processProposerSlashing_frame_com h hs,
      fun _ _ _ h hs => processAttesterSlashing_frame_com h hs,
      fun _ _ _ _ h hs => (processAttestation_frame_com h).trans hs⟩ hu

/-- **The voter of a placed vote is an attesting index at the run state before its block**,
when the committee window of the vote slot holds there. `process_attestation` read the attesting
indices on the loop state `pre`. The block keeps the committees of the epoch of the vote slot
from `u` to `pre` (`BlockReach.keeps_com`), so the read gives the same indices on `u`. -/
theorem RunVote.attesting {hi : Nat} {A : BeaconState} {steps : List ChainStep}
    {i : ValidatorIndex} {d : AttestationData} (hv : RunVote hi A steps i d) :
    ∃ (s₁ s₂ : List ChainStep) (sb : SignedBeaconBlock) (v : Bool) (u : BeaconState)
      (att : Attestation),
      steps = s₁ ++ .block sb v :: s₂ ∧ ChainRun hi s₁ A u ∧
      att ∈ sb.message.body.attestations.toArray ∧ att.data = d ∧
      (CommitteeWindow (computeEpochAtSlot att.data.slot) (pureState u) →
        ∃ idx, getAttestingIndices (pureState u) att = .ok idx ∧ i ∈ idx) := by
  obtain ⟨s₁, s₂, sb, v, u, pre, post, att, hs, hr, hatt, hd, hvote, -, -, -, hreach⟩ := hv
  obtain ⟨-, ⟨idx, hidx, hi⟩, -, -⟩ := hvote
  refine ⟨s₁, s₂, sb, v, u, att, hs, hr, hatt, hd, fun hwin => ?_⟩
  have hs0 : comView (computeEpochAtSlot att.data.slot) (pureState u) =
      (true, (comView (computeEpochAtSlot att.data.slot) (pureState u)).2) := by
    show ((comView _ (pureState u)).1, (comView _ (pureState u)).2) = _
    have : (comView (computeEpochAtSlot att.data.slot) (pureState u)).1 = true := by
      simpa [comView] using hwin
    rw [this]
  have hpre := hreach.keeps_com hs0
  refine ⟨idx, ?_, hi⟩
  rw [← getAttestingIndices_eq_of_comView (hpre.trans hs0.symm) att rfl]
  exact hidx

/-- The attesting indices of `att` at `u`, or none when the read faults. -/
def idxOf (u : BeaconState) (att : Attestation) : Array ValidatorIndex :=
  match getAttestingIndices (pureState u) att with
  | .ok idx => idx
  | .error _ => #[]

/-- Each vote of the blocks of `W`, with its attesting indices at the state before its block,
and whether the committee window of its slot holds there. `L` lists the state before each step,
as `runStates` does. -/
def attSetsB : List ChainStep → List BeaconState →
    List (AttestationData × Array ValidatorIndex × Bool)
  | .block sb _ :: W, u :: L =>
    sb.message.body.attestations.toArray.toList.map (fun att =>
      (att.data, idxOf u att,
        decide (CommitteeWindow (computeEpochAtSlot att.data.slot) (pureState u)))) ++
      attSetsB W L
  | .slot :: W, _ :: L => attSetsB W L
  | _, _ => []

/-- A vote of a block of a run that follows the messages of `W` is an entry of `attSetsB`, with
the attesting indices at the state before the block. -/
theorem mem_attSets : ∀ {W : List ChainStep} {A : BeaconState} {L : List BeaconState},
    runStates (2 ^ 64 - 1) W A = some L →
    ∀ {s₁ : List ChainStep} {sb : SignedBeaconBlock} {v : Bool} {u : BeaconState},
    (W.take (s₁.length + 1)).map stepMsg = (s₁ ++ [ChainStep.block sb v]).map stepMsg →
    ChainRun (2 ^ 64 - 1) s₁ A u →
    ∀ att ∈ sb.message.body.attestations.toArray,
      (att.data, idxOf u att,
        decide (CommitteeWindow (computeEpochAtSlot att.data.slot) (pureState u))) ∈
        attSetsB W L
  | [], _, _, _, s₁, _, _, _, hm, _, _, _ => by
    cases s₁ <;> simp at hm
  | x :: W, A, L, hL, s₁, sb, v, u, hm, hr, att, hatt => by
    simp only [runStates] at hL
    split at hL
    · rename_i st1 h1
      obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.mp hL
      cases s₁ with
      | nil =>
        cases hr
        cases x with
        | slot => simp [stepMsg] at hm
        | block sb' v' =>
          have hsb : sb'.message = sb.message := by simpa [stepMsg] using hm
          simp only [attSetsB]
          apply List.mem_append_left
          rw [hsb]
          exact List.mem_map.mpr ⟨att, by simpa using hatt, rfl⟩
      | cons y s₁' =>
        simp only [List.length_cons, List.take_succ_cons, List.cons_append, List.map_cons,
          List.cons.injEq] at hm
        obtain ⟨hxy, hm'⟩ := hm
        obtain ⟨m, hm1, hm2⟩ := (show ChainRun _ ([y] ++ s₁') A u from hr).split
        have hx := ChainRun.of_runChain [x] A st1 h1
        have hmst : m = st1 := hm1.det_msg hx (by simp [hxy])
        subst hmst
        have ih := mem_attSets hL' (s₁ := s₁') hm' hm2 att hatt
        cases x with
        | slot => simpa [attSetsB] using ih
        | block sb' v' =>
          simp only [attSetsB]
          exact List.mem_append_right _ ih
    · cases hL

/-- Two votes of one honest validator with one target epoch carry one data, and every vote has
its committee window. -/
def singleB (honestOf : ValidatorIndex → Bool)
    (S : List (AttestationData × Array ValidatorIndex × Bool)) : Bool :=
  S.all fun x => x.2.2 && S.all fun y =>
    !(x.1.target.epoch == y.1.target.epoch) || decide (x.1 = y.1) ||
      !(x.2.1.any fun j => honestOf j && y.2.1.contains j)

/-- **A placed vote on a run that follows the messages of `W` is an entry of `attSetsB`** whose
indices hold the voter. The entry has its committee window (`singleB`), so `RunVote.attesting`
names the voter among the indices. -/
theorem RunVote.entry {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    (hL : runStates (2 ^ 64 - 1) W A = some L) {honestOf : ValidatorIndex → Bool}
    (hchk : singleB honestOf (attSetsB W L) = true) {P : List ChainStep}
    (hmap : (W.take P.length).map stepMsg = P.map stepMsg)
    {i : ValidatorIndex} {d : AttestationData} (hv : RunVote (2 ^ 64 - 1) A P i d) :
    ∃ idx, (d, idx, true) ∈ attSetsB W L ∧ i ∈ idx := by
  obtain ⟨s₁, s₂, sb, v, u, att, hs, hr, hatt, hd, hidx⟩ := hv.attesting
  have hm : (W.take (s₁.length + 1)).map stepMsg =
      (s₁ ++ [ChainStep.block sb v]).map stepMsg := by
    have hle : s₁.length + 1 ≤ P.length := by rw [hs]; simp
    have h := congrArg (List.take (s₁.length + 1)) hmap
    rw [← List.map_take, ← List.map_take] at h
    have e : (W.take P.length).take (s₁.length + 1) = W.take (s₁.length + 1) := by
      rw [List.take_take]
      congr 1
      omega
    have e2 : P.take (s₁.length + 1) = s₁ ++ [ChainStep.block sb v] := by
      rw [hs, show s₁ ++ ChainStep.block sb v :: s₂ = (s₁ ++ [ChainStep.block sb v]) ++ s₂ by
        simp, show s₁.length + 1 = (s₁ ++ [ChainStep.block sb v]).length by simp, List.take_left]
    rw [e, e2] at h
    exact h
  have hmem := mem_attSets hL hm hr att hatt
  have hwin : CommitteeWindow (computeEpochAtSlot att.data.slot) (pureState u) := by
    have h := List.all_eq_true.mp hchk _ hmem
    simp only [Bool.and_eq_true] at h
    exact of_decide_eq_true h.1
  obtain ⟨idx, hok, hi⟩ := hidx hwin
  have hid : idxOf u att = idx := by
    unfold idxOf
    rw [hok]
  rw [decide_eq_true hwin, hid, hd] at hmem
  exact ⟨idx, hmem, hi⟩

/-- **`singleB` gives one vote per target epoch.** Two placed votes of an honest validator on
runs that follow the messages of `W`, with one target epoch, carry one data. -/
theorem single_of_check {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    (hL : runStates (2 ^ 64 - 1) W A = some L) {honestOf : ValidatorIndex → Bool}
    (hchk : singleB honestOf (attSetsB W L) = true) {P₁ P₂ : List ChainStep}
    (hm₁ : (W.take P₁.length).map stepMsg = P₁.map stepMsg)
    (hm₂ : (W.take P₂.length).map stepMsg = P₂.map stepMsg)
    {i : ValidatorIndex} (hhon : honestOf i = true) {d₁ d₂ : AttestationData}
    (hv₁ : RunVote (2 ^ 64 - 1) A P₁ i d₁) (hv₂ : RunVote (2 ^ 64 - 1) A P₂ i d₂)
    (he : d₂.target.epoch = d₁.target.epoch) : d₂ = d₁ := by
  obtain ⟨idx₁, he₁, hi₁⟩ := hv₁.entry hL hchk hm₁
  obtain ⟨idx₂, he₂, hi₂⟩ := hv₂.entry hL hchk hm₂
  have h := List.all_eq_true.mp hchk _ he₂
  simp only [Bool.and_eq_true] at h
  have h' := List.all_eq_true.mp h.2 _ he₁
  have hany : (idx₂.any fun j => honestOf j && idx₁.contains j) = true :=
    Array.any_eq_true'.mpr ⟨i, hi₂, by simp [hhon, hi₁]⟩
  simp only [he, hany] at h'
  simpa using h'

omit [HasherTag] [Config] [CryptoBackend] in
/-- A prefix of `W` follows the messages of `W`. -/
theorem take_map_of_prefix {W P Q : List ChainStep} (h : W = P ++ Q) :
    (W.take P.length).map stepMsg = P.map stepMsg := by
  rw [h, List.take_left]

omit [HasherTag] [Config] [CryptoBackend] in
/-- A run whose messages are those of a prefix of `W` follows `W`. -/
theorem take_map_of_msgs {W W₁ W₂ S : List ChainStep} (h : W = W₁ ++ W₂)
    (hm : W₁.map stepMsg = S.map stepMsg) : (W.take S.length).map stepMsg = S.map stepMsg := by
  have hlen : W₁.length = S.length := by simpa using congrArg List.length hm
  rw [← hlen, h, List.take_left, hm]

end Votes

/-! ## The weigh states and the slashed flags -/

section States
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- A state at the last slot of an epoch from `lo` to `hi`. -/
def weighsIn (u : BeaconState) (lo hi : Nat) : Bool :=
  decide ((u.slot.toNat + 1) % slotsPerEpoch = 0) &&
    decide (lo ≤ u.slot.toNat / slotsPerEpoch) && decide (u.slot.toNat / slotsPerEpoch ≤ hi)

/-- At each weigh state of an epoch from `lo` to `hi`, each validator of `honestList` has a
placed vote for the previous epoch, and these validators hold two thirds of the total. -/
def includedB (W : List ChainStep) (L : List BeaconState) (honestOf : ValidatorIndex → Bool)
    (lo hi : Nat) : Bool :=
  L.all fun u => !weighsIn u lo hi ||
    (((honestList u honestOf (previousEpochOf (pureState u))).all fun x =>
        placedB W L x (previousEpochOf (pureState u))) &&
      decide (3 * honestStake u honestOf (previousEpochOf (pureState u)) ≥
        2 * (totBal u).toNat))

/-- **`includedB` gives the `included` premise of `CarrierWindow`** for the epochs from `lo` to
`hi`. A weigh state is a state of `L` (`runStates_mem`). -/
theorem included_of_check {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    (hL : runStates (2 ^ 64 - 1) W A = some L) {honestOf : ValidatorIndex → Bool} {lo hi : Nat}
    (h : includedB W L honestOf lo hi = true) :
    ∀ e, lo ≤ e → e ≤ hi → ∀ u, WeighAt (2 ^ 64 - 1) W A e u →
      (∀ x ∈ honestList u honestOf (previousEpochOf (pureState u)),
        PlacedVote (2 ^ 64 - 1) A W x (previousEpochOf (pureState u))) ∧
      3 * honestStake u honestOf (previousEpochOf (pureState u)) ≥ 2 * (totBal u).toNat := by
  intro e h1 h2 u ⟨s₁, s₂, hs, hu, hlast, hep⟩
  have hm := runStates_mem hL hs hu
  have hw : weighsIn u lo hi = true := by
    simp only [weighsIn, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hc := List.all_eq_true.mp h u hm
  rw [hw, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨fun x hx => PlacedVote.of_check hL (List.all_eq_true.mp hc.1 x hx), hc.2⟩

/-- No state of `L` has an honest validator slashed. -/
def unslashedB (L : List BeaconState) (honestOf : ValidatorIndex → Bool) : Bool :=
  L.all fun u => (List.range u.validators.val.size).all fun j =>
    !honestOf (UInt64.ofNat j) || !(u.validators.val[j]!).slashed

omit [HasherTag] [Config] [CryptoBackend] in
/-- `unslashedB` gives the slashed flags of each state of `L`. -/
theorem unslashed_of_check {L : List BeaconState} {honestOf : ValidatorIndex → Bool}
    (h : unslashedB L honestOf = true) {u : BeaconState} (hu : u ∈ L) :
    ∀ j < u.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (u.validators.val[j]!).slashed = false := by
  intro j hj hh
  have hc := List.all_eq_true.mp (List.all_eq_true.mp h u hu) j (List.mem_range.mpr hj)
  simpa [hh] using hc

end States

/-! ## The path to `pending r` -/

section Path
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

open EthCLSpecs.Heze (Store Root ForkChoiceNode)

/-- The check of `FinalitySetting.pathBefore` at one store for the node `x` of slot `t`: the walk
up from `pending r` ends within `fuel` steps, it passes `x`, and each node on it that a message
of `t` can support lies below `x`. -/
def pathB (store : Store map) (fuel : Nat) (r : Root) (x : ForkChoiceNode) (t : Nat) : Bool :=
  let up := ancestorsB store fuel (.pending r)
  let upX := ancestorsB store fuel x
  walkDone store fuel (.pending r) && nodeIn up x &&
    up.all fun y => !decide (supSlot store y ≤ t) || nodeIn upX y

/-- **`pathB` gives the path facts of `pathBefore`.** The walk lists every ancestor of
`pending r` (`mem_ancestorsB_of_below`), and a node on a walk is an ancestor
(`below_of_mem_ancestorsB`). -/
theorem path_of_check {store : Store map} {fuel : Nat} {r : Root} {x : ForkChoiceNode} {t : Nat}
    (h : pathB store fuel r x t = true) :
    NodeBelow store x (.pending r) ∧ ∀ y, NodeBelow store y (.pending r) →
      supSlot store y ≤ t → NodeBelow store y x := by
  simp only [pathB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨hdone, hx⟩, hall⟩ := h
  refine ⟨below_of_mem_ancestorsB fuel _ (nodeIn_iff.mp hx), fun y hy hs => ?_⟩
  rcases hall y (mem_ancestorsB_of_below hy fuel hdone) with h | h
  · exact absurd hs h
  · exact below_of_mem_ancestorsB fuel x (nodeIn_iff.mp h)

/-- The check of the fork counts of `FinalitySetting.cases` at one store: the walk up from
`pending r` ends within `fuel` steps, and at each node `y` on it whose parent `x` has a block
`xb`, the count `ok y (xb.slot + 1)` holds. -/
def forkB (store : Store map) (fuel : Nat) (r : Root) (ok : ForkChoiceNode → Nat → Bool) :
    Bool :=
  walkDone store fuel (.pending r) &&
  (ancestorsB store fuel (.pending r)).all fun y =>
    match nodeParent store y with
    | some x => (FcMap.lookup store.blocks x.root).all fun xb => ok y (xb.slot.toNat + 1)
    | none => true

/-- **`forkB` gives the count at each fork of the path to `pending r`.** A child `y` above
`pending r` is on the walk (`mem_ancestorsB_of_below`), and its parent is the one parent of
`y` (`nodeParent_of_edge`). -/
theorem fork_of_check {store : Store map} {fuel : Nat} {r : Root}
    {ok : ForkChoiceNode → Nat → Bool} (h : forkB store fuel r ok = true) :
    ∀ x y xb, NodeEdge store x y → NodeBelow store y (.pending r) →
      FcMap.lookup store.blocks x.root = some xb → ok y (xb.slot.toNat + 1) = true := by
  intro x y xb hxy hy hxb
  simp only [forkB, Bool.and_eq_true, List.all_eq_true] at h
  have hc := h.2 y (mem_ancestorsB_of_below hy fuel h.1)
  rw [nodeParent_of_edge hxy] at hc
  simp only at hc
  rw [hxb] at hc
  simpa using hc

end Path

end EthCLSpecs.Proofs.Heze
