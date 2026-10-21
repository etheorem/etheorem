import EthCLSpecs.Proofs.Heze.ParticipationFrame
import EthCLSpecs.Proofs.Heze.CheckpointInvariants

/-!
# `EthCLSpecs.Proofs.Heze.Participation`: each target flag comes from an included vote

The target flag of validator `i` for epoch `e` is set in a state (`TargetFlagSet`) when its
target bit is set in the list of `e`: the current list for the current epoch, the previous
list for the previous epoch. `processJustificationAndFinalization` weighs these flags. This
module ties each flag to a vote of the chain.

## The attestation

`processAttestation` checks an attestation, then sets flags for its attesting indices
(`processAttestation_run_flags`). It writes into the current list when the target epoch is
the current epoch, else into the previous list. `get_attestation_participation_flag_indices`
asserts a matching source after its root reads, so the run rejects without one. It puts the
target flag in the list exactly when the target root matches (`gapfi_run_ok`, `gapfi_target`,
`gapfi_target_of_root`).
So two facts hold:

- A target bit that the run sets belongs to an attesting index of the attestation, whose
  source matches and whose target root matches (`processAttestation_explained`).
- With a matching source and target root, the run sets the target bit of every attesting
  index (`processAttestation_sets_target`).

The two loops of `processAttestation` thread the state next to counters. The proof walks
them by `forIn_run_inv` and by `forIn_run_all`, a loop rule for a monotone relation.

## The run

A block step runs `processAttestation` for each attestation of the block body
(`processBlock_flags`). The other functions of the block step keep the target bits
(`ParticipationFrame.lean`). A slot step keeps the target flags of each epoch, and at an
epoch boundary it moves the current flags to the previous list (`SlotStep.targetFlag`).

So along a chain run, each target flag of an epoch after the current epoch of the start
state comes from an attestation that a block of the run includes
(`ChainRun.flag_explained`, `IncludedVote`). The start state has no flag of such an epoch,
because that epoch is neither its current nor its previous epoch.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure runPure_of_run_ok run_bind_eq_ok
  run_get_bind_eq_ok run_pure run_assert_bind_eq_ok run_ite_eq_ok forIn_run_inv
  run_bind_eq_ok_pure keepsUncached_bind keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot Epoch BeaconState Checkpoint Attestation
  AttestationData ValidatorIndex SignedBeaconBlock BeaconBlock currentEpochOf previousEpochOf
  getAttestingIndices getBlockRoot processAttestation)
open EthCLSpecs.Heze.Const (slotsPerEpoch timelyTargetFlagIndex)

/-! ## Run facts at any state type -/

section Generic
variable {σ ε α β : Type}

/-- Every successful run of `x` returns a value that satisfies `P`. -/
def RetP (P : α → Prop) (x : StateT σ (Except ε) α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → P a

theorem RetP.pure {P : α → Prop} (a : α) (h : P a) :
    RetP P (Pure.pure a : StateT σ (Except ε) α) :=
  fun s b s' hr => (EthCLLib.Proofs.run_pure_eq_ok a b s s' hr) ▸ h

theorem RetP.bind {P : β → Prop} {x : StateT σ (Except ε) α} {k : α → StateT σ (Except ε) β}
    (hk : ∀ a, RetP P (k a)) : RetP P (x >>= k) := by
  intro s b s' hr
  obtain ⟨a, s1, -, h2⟩ := run_bind_eq_ok _ _ _ _ hr
  exact hk a _ _ _ h2

/-- The rule for an `if`: each branch may use its condition. -/
theorem RetP.ite {P : α → Prop} {c : Prop} [Decidable c] {x y : StateT σ (Except ε) α}
    (hx : c → RetP P x) (hy : ¬ c → RetP P y) : RetP P (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]; exact hx hc
  · rw [if_neg hc]; exact hy hc

/-- The rule for an `assert`: the rest may use the condition. -/
theorem RetP.assert {P : α → Prop} {c : Prop} [Decidable c] {e : ε}
    {k : PUnit → StateT σ (Except ε) α} (hk : c → RetP P (k PUnit.unit)) :
    RetP P ((if c then (Pure.pure PUnit.unit : StateT σ (Except ε) PUnit) else throw e) >>= k) := by
  intro s a s' hr
  obtain ⟨hc, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok e k s _ hr
  exact hk hc s a s' h

/-- Read the fact off a successful run. -/
theorem RetP.elim {P : α → Prop} {x : StateT σ (Except ε) α} {s : σ} {a : α} {s' : σ}
    (hx : RetP P x) (h : x.run s = .ok (a, s')) : P a :=
  hx s a s' h

/-- A successful `liftErr` of an index read: the read succeeded, and the state stays. -/
theorem liftErr_run_ok {x : Except SizzLean.Cache.IndexError α} {s s' : σ} {a : α}
    (h : (liftErr (m := StateT σ (Except StateTransitionError)) x).run s = .ok (a, s')) :
    x = .ok a ∧ s' = s := by
  cases x with
  | error e => cases e; cases h
  | ok b =>
    injection h with h
    injection h with h1 h2
    exact ⟨h1 ▸ rfl, h2.symm⟩

/-- A successful `liftErr` of a checked computation, such as the start slot of an epoch: the
computation succeeded, and the state stays. -/
theorem liftErr_run_ok_spec {x : Except StateTransitionError α} {s s' : σ} {a : α}
    (h : (liftErr (m := StateT σ (Except StateTransitionError)) x).run s = .ok (a, s')) :
    x = .ok a ∧ s' = s := by
  cases x with
  | error e => cases h
  | ok b =>
    injection h with h
    injection h with h1 h2
    exact ⟨h1 ▸ rfl, h2.symm⟩

/-- A successful `sszGetIdx`: the entry exists, and the state stays. -/
theorem sszGetIdx_run_ok {cap : Nat} {xs : SizzLean.Repr.SSZList α cap} {n : Nat}
    {s s' : σ} {a : α}
    (h : (sszGetIdx (m := StateT σ (Except StateTransitionError)) xs n).run s = .ok (a, s')) :
    xs.val[n]? = some a ∧ s' = s := by
  unfold sszGetIdx at h
  split at h
  · rename_i b hb
    obtain ⟨h1, h2⟩ := liftErr_run_ok h
    injection h1 with h1
    exact ⟨h1 ▸ hb, h2⟩
  · obtain ⟨h1, -⟩ := liftErr_run_ok h
    cases h1

/-- A successful `checkedAdd` keeps the state. -/
theorem checkedAdd_run_state {a b : UInt64} {d : String} {s s' : σ} {r : UInt64}
    (h : (checkedAdd (m := StateT σ (Except StateTransitionError)) a b d).run s
      = .ok (r, s')) : s' = s := by
  unfold checkedAdd throwArithmetic at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · cases h
  · exact EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h

/-- A loop rule for a monotone relation `R`. Each body step yields, its value follows the old
one by `R`, and its value satisfies `Q a` for the element `a` of the step. `Q a` survives
`R`. Then the result follows the start value by `R`, and satisfies `Q a` for every element. -/
theorem forIn_run_all (R : β → β → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c) (Q : α → β → Prop)
    (hmono : ∀ a b b', Q a b → R b b' → Q a b')
    (f : α → β → StateT σ (Except ε) (ForInStep β)) :
    ∀ (l : List α),
      (∀ a ∈ l, ∀ b s s' st, (f a b).run s = .ok (st, s') →
        ∃ b', st = .yield b' ∧ R b b' ∧ Q a b') →
      ∀ (init : β) (s s' : σ) (r : β), (forIn l init f).run s = .ok (r, s') →
        R init r ∧ ∀ a ∈ l, Q a r := by
  intro l
  induction l with
  | nil =>
    intro _ init s s' r h
    rw [List.forIn_nil] at h
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
    subst this
    exact ⟨hrefl _, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a rest ih =>
    intro hstep init s s' r h
    rw [List.forIn_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨b', rfl, hR, hQ⟩ := hstep a List.mem_cons_self init s s1 st hbody
    obtain ⟨hR', hQ'⟩ := ih (fun x hx => hstep x (List.mem_cons_of_mem a hx)) b' s1 s' r hrest
    refine ⟨htrans _ _ _ hR hR', fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hmono _ _ _ hQ hR'
    · exact hQ' x hx

/-- `forIn_run_all` with an invariant `I` of the accumulator. Each body step starts from a
value with `I`, and yields a value with `I`. -/
theorem forIn_run_all_inv (I : β → Prop) (R : β → β → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c) (Q : α → β → Prop)
    (hmono : ∀ a b b', Q a b → R b b' → Q a b')
    (f : α → β → StateT σ (Except ε) (ForInStep β)) :
    ∀ (l : List α),
      (∀ a ∈ l, ∀ b s s' st, I b → (f a b).run s = .ok (st, s') →
        ∃ b', st = .yield b' ∧ I b' ∧ R b b' ∧ Q a b') →
      ∀ (init : β) (s s' : σ) (r : β), I init → (forIn l init f).run s = .ok (r, s') →
        I r ∧ R init r ∧ ∀ a ∈ l, Q a r := by
  intro l
  induction l with
  | nil =>
    intro _ init s s' r hI h
    rw [List.forIn_nil] at h
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
    subst this
    exact ⟨hI, hrefl _, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a rest ih =>
    intro hstep init s s' r hI h
    rw [List.forIn_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨b', rfl, hI', hR, hQ⟩ := hstep a List.mem_cons_self init s s1 st hI hbody
    obtain ⟨hIr, hR', hQ'⟩ :=
      ih (fun x hx => hstep x (List.mem_cons_of_mem a hx)) b' s1 s' r hI' hrest
    refine ⟨hIr, htrans _ _ _ hR hR', fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hmono _ _ _ hQ hR'
    · exact hQ' x hx

/-- A successful bind through an action that returns a box, from a plain start: the action
returns a plain state and ends at a plain state. -/
theorem run_bind_eq_ok_ret {T : Type} [SizzLean.SSZRepr T] [HasherTag]
    {x : StateT (SizzLean.Cache.SSZ.Box HasherTag.H T) (Except ε)
      (SizzLean.Cache.SSZ.Box HasherTag.H T)}
    {k : SizzLean.Cache.SSZ.Box HasherTag.H T →
      StateT (SizzLean.Cache.SSZ.Box HasherTag.H T) (Except ε) α}
    (hx : EthCLLib.Proofs.ReturnsUncached x) {v : T}
    {r : α × SizzLean.Cache.SSZ.Box HasherTag.H T} (h : (x >>= k).run (pureState v) = .ok r) :
    ∃ b w : T, x.run (pureState v) = .ok (pureState b, pureState w) ∧
      (k (pureState b)).run (pureState w) = .ok r := by
  obtain ⟨b0, s1, h1, h2⟩ := run_bind_eq_ok x k _ r h
  obtain ⟨⟨b, rfl⟩, hs⟩ := hx v b0 s1 h1
  obtain ⟨w, rfl⟩ : ∃ w, s1 = pureState w := ⟨_, hs⟩
  exact ⟨b, w, h1, h2⟩

/-- A successful `runPure` is a successful run on the uncached box, whose result box has the
returned view. -/
theorem runPure_ok_run {T : Type} [SizzLean.SSZRepr T] [HasherTag]
    {x : StateT (SizzLean.Cache.SSZ.Box HasherTag.H T) (Except ε) α} {v w : T} {a : α}
    (h : runPure x v = .ok (a, w)) :
    ∃ s, x.run (pureState v) = .ok (a, s) ∧ s.view = w := by
  rw [EthCLLib.Proofs.runPure_eq] at h
  cases hr : x.run (pureState v) with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨p.2, by rw [← h.1], h.2⟩

end Generic

/-! ## Flag bytes and the entry write -/

set_option maxRecDepth 100000 in
/-- Bit 1 of a flag byte after `addFlag` of a flag index below 3, on every byte. -/
theorem hasFlag_addFlag_table : ∀ n : Fin 256, ∀ k : Fin 3,
    hasFlag (addFlag (UInt8.ofFin n) k) 1 = (hasFlag (UInt8.ofFin n) 1 || k.val == 1) := by
  decide

section
variable [Preset]

omit [Preset] in
/-- `addFlag` of a flag index below 3 sets the target bit exactly when the index is the
target index, and it keeps a target bit. -/
theorem hasFlag_addFlag_target (y : UInt8) (k : Nat) (hk : k < 3) :
    hasFlag (addFlag y k) timelyTargetFlagIndex = (hasFlag y timelyTargetFlagIndex || k == timelyTargetFlagIndex) := by
  have := hasFlag_addFlag_table y.toFin ⟨k, hk⟩
  simpa using this

/-- The target bit of an entry that the list holds. -/
theorem bitOf_of_getElem? (l : PartList) (n : Nat) (y : EthCLSpecs.Heze.ParticipationFlags)
    (hy : l.val[n]? = some y) : bitOf l n = hasFlag y timelyTargetFlagIndex := by
  unfold bitOf
  have hn : n < l.size := by
    rcases Nat.lt_or_ge n l.val.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hy; cases hy
  rw [getElem!_pos (dom := fun (xs : PartList) i => i < xs.size) (h := hn)]
  show hasFlag l.val[n] _ = _
  rw [Array.getElem?_eq_getElem hn] at hy
  rw [Option.some.inj hy]

/-- The write of `processAttestation` sets a target bit only at its own index, and only for
the target flag index. -/
theorem bitOf_set_addFlag (l : PartList) (n j : Nat) (y : EthCLSpecs.Heze.ParticipationFlags)
    (hy : l.val[n]? = some y) (k : Nat) (hk : k < 3)
    (hb : bitOf (l.set! n (addFlag y k)) j = true) :
    bitOf l j = true ∨ (j = n ∧ k = timelyTargetFlagIndex) := by
  by_cases hnj : n = j
  · subst hnj
    have hn : n < l.size := by
      rcases Nat.lt_or_ge n l.val.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hy; cases hy
    unfold bitOf at hb
    rw [SizzLean.Proofs.sszListSet!_getElem!_self _ _ _ hn, hasFlag_addFlag_target _ _ hk] at hb
    rw [bitOf_of_getElem? _ _ _ hy]
    rcases Bool.or_eq_true_iff.mp hb with h | h
    · exact .inl h
    · exact .inr ⟨rfl, beq_iff_eq.mp h⟩
  · unfold bitOf at hb ⊢
    rw [SizzLean.Proofs.sszListSet!_getElem!_ne _ _ _ _ hnj] at hb
    exact .inl hb

/-- The write of `processAttestation` keeps every target bit. -/
theorem bitOf_set_addFlag_mono (l : PartList) (n j : Nat)
    (y : EthCLSpecs.Heze.ParticipationFlags) (hy : l.val[n]? = some y) (k : Nat) (hk : k < 3)
    (hb : bitOf l j = true) : bitOf (l.set! n (addFlag y k)) j = true := by
  by_cases hnj : n = j
  · subst hnj
    have hn : n < l.size := by
      rcases Nat.lt_or_ge n l.val.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hy; cases hy
    rw [bitOf_of_getElem? _ _ _ hy] at hb
    unfold bitOf
    rw [SizzLean.Proofs.sszListSet!_getElem!_self _ _ _ hn, hasFlag_addFlag_target _ _ hk, hb,
      Bool.true_or]
  · unfold bitOf at hb ⊢
    rw [SizzLean.Proofs.sszListSet!_getElem!_ne _ _ _ _ hnj]
    exact hb

/-- The write of the target flag sets the target bit at its index. -/
theorem bitOf_set_addFlag_self (l : PartList) (n : Nat) (y : EthCLSpecs.Heze.ParticipationFlags)
    (hy : l.val[n]? = some y) : bitOf (l.set! n (addFlag y timelyTargetFlagIndex)) n = true := by
  have hn : n < l.size := by
    rcases Nat.lt_or_ge n l.val.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hy; cases hy
  unfold bitOf
  rw [SizzLean.Proofs.sszListSet!_getElem!_self _ _ _ hn,
    hasFlag_addFlag_target _ _ (by decide)]
  simp

/-- Two checkpoints with equal epochs and roots are equal. -/
theorem checkpoint_eq_of_beq {a b : Checkpoint}
    (h : (a.epoch == b.epoch && a.root == b.root) = true) : a = b := by
  obtain ⟨ae, ar⟩ := a
  obtain ⟨be, br⟩ := b
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

end

/-! ## The flag indices of an attestation -/

section
variable [Preset] [HasherTag]

/-- The justified checkpoint that a vote with target epoch `e` names as its source in `st`:
the current one for the current epoch, else the previous one. -/
def sourceFor (st : BeaconState) (e : Epoch) : Checkpoint :=
  if e = currentEpochOf (pureState st) then st.currentJustifiedCheckpoint
  else st.previousJustifiedCheckpoint

/-- The source test of `get_attestation_participation_flag_indices` is `sourceFor`. -/
theorem source_of_beq (st : BeaconState) (data : AttestationData)
    (h : (data.source.epoch == (if (data.target.epoch == currentEpochOf (pureState st)) = true
          then st.currentJustifiedCheckpoint else st.previousJustifiedCheckpoint).epoch &&
        data.source.root == (if (data.target.epoch == currentEpochOf (pureState st)) = true
          then st.currentJustifiedCheckpoint else st.previousJustifiedCheckpoint).root) = true) :
    data.source = sourceFor st data.target.epoch := by
  unfold sourceFor
  by_cases hc : data.target.epoch = currentEpochOf (pureState st)
  · rw [if_pos (beq_iff_eq.mpr hc)] at h
    rw [if_pos hc]
    exact checkpoint_eq_of_beq h
  · rw [if_neg (by simpa using hc)] at h
    rw [if_neg hc]
    exact checkpoint_eq_of_beq h

/-- The flag list of an accepted vote. The run read the target root `tr`, and that read keeps
the state. The source matches, since the run asserts it after its root reads. The list holds
the target flag exactly when the target root is `tr`. -/
theorem gapfi_run_ok (st : BeaconState) (data : AttestationData) (d : UInt64)
    (f : Array Nat) (st1 : BeaconState)
    (h₀ : runPure (EthCLSpecs.Heze.getAttestationParticipationFlagIndices
      (StateTransition := HezeRun) (pureState st) data d) st = .ok (f, st1)) :
    ∃ tr, runPure (getBlockRoot (StateTransition := HezeRun) (pureState st) data.target.epoch) st
        = .ok (tr, st) ∧
      data.source = sourceFor st data.target.epoch ∧
      (f.contains timelyTargetFlagIndex = true ↔ data.target.root = tr) := by
  obtain ⟨_, h, -⟩ := runPure_ok_run h₀
  unfold EthCLSpecs.Heze.getAttestationParticipationFlagIndices at h
  extract_lets justified isMatchingSource at h
  obtain ⟨tr, s2, htr, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- `getBlockRoot` reads the state only: the checked start slot, two asserts, a checked
  -- sum, and a `pure`.
  have e2 : s2 = pureState st := by
    have htr := htr
    unfold EthCLSpecs.Heze.getBlockRoot EthCLSpecs.Heze.getBlockRootAtSlot at htr
    obtain ⟨_, s4, hs4, htr⟩ := run_bind_eq_ok _ _ _ _ htr
    obtain ⟨-, e4⟩ := liftErr_run_ok_spec hs4
    subst e4
    obtain ⟨-, htr⟩ := run_assert_bind_eq_ok _ _ _ _ htr
    obtain ⟨b, s3, hb, htr⟩ := run_bind_eq_ok _ _ _ _ htr
    have e3 := checkedAdd_run_state hb
    subst e3
    obtain ⟨-, htr⟩ := run_assert_bind_eq_ok _ _ _ _ htr
    exact EthCLLib.Proofs.run_pure_state_eq _ _ _ _ htr
  subst e2
  -- Every leaf sits below the source assert. The target flag sits below the target test.
  have key : isMatchingSource = true ∧
      f.contains timelyTargetFlagIndex = (isMatchingSource && data.target.root == tr) := by
    refine RetP.elim (P := fun g : Array Nat => isMatchingSource = true ∧
      g.contains timelyTargetFlagIndex = (isMatchingSource && data.target.root == tr)) ?_ h
    -- The leaves need the flag lists only. The source test stays a name.
    clear h h₀ htr
    clear_value isMatchingSource justified
    repeat' first
      | refine RetP.assert fun _ => ?_
      | refine RetP.bind fun _ => ?_
      | refine RetP.ite (fun _ => ?_) (fun _ => ?_)
      | (refine RetP.pure _ ⟨by assumption, ?_⟩
         -- The flag lists of the leaves are `let`s of the body. Unfold them in the goal.
         dsimp +zetaDelta only
         simp_all [timelyTargetFlagIndex, EthCLSpecs.Heze.Const.timelySourceFlagIndex,
           EthCLSpecs.Heze.Const.timelyHeadFlagIndex])
  refine ⟨tr, runPure_of_run_ok htr, source_of_beq st data key.1, ?_⟩
  rw [key.2, key.1, Bool.true_and, beq_iff_eq]

/-- The flag list of an accepted vote: the source matches, and the target flag is in the
list only when the target root matches. -/
theorem gapfi_target (st : BeaconState) (data : AttestationData) (d : UInt64)
    (f : Array Nat) (st1 : BeaconState)
    (h₀ : runPure (EthCLSpecs.Heze.getAttestationParticipationFlagIndices
      (StateTransition := HezeRun) (pureState st) data d) st = .ok (f, st1)) :
    data.source = sourceFor st data.target.epoch ∧
    (f.contains timelyTargetFlagIndex = true →
      runPure (getBlockRoot (StateTransition := HezeRun) (pureState st) data.target.epoch) st
        = .ok (data.target.root, st)) := by
  obtain ⟨tr, htr, hs, hiff⟩ := gapfi_run_ok st data d f st1 h₀
  exact ⟨hs, fun hc => by rw [hiff.mp hc]; exact htr⟩

/-- With a matching target root, the flag list of an accepted vote holds the target flag. -/
theorem gapfi_target_of_root (st : BeaconState) (data : AttestationData) (d : UInt64)
    (f : Array Nat) (st1 : BeaconState)
    (h₀ : runPure (EthCLSpecs.Heze.getAttestationParticipationFlagIndices
      (StateTransition := HezeRun) (pureState st) data d) st = .ok (f, st1))
    (htgt : runPure (getBlockRoot (StateTransition := HezeRun) (pureState st)
      data.target.epoch) st = .ok (data.target.root, st)) :
    f.contains timelyTargetFlagIndex = true := by
  obtain ⟨tr, htr, -, hiff⟩ := gapfi_run_ok st data d f st1 h₀
  -- The read of the target root returns one root.
  rw [htr] at htgt
  injection htgt with htgt
  injection htgt with htgt
  exact hiff.mpr htgt.symm

/-! ## The attestation run -/

variable [Config] [CryptoBackend]

/-- A successful `processAttestation` run. It read a flag list `f` and the attesting indices
`idx`, and the target epoch is the previous or the current epoch. Then three facts hold:

- A target bit that is set after the run was set before, or it belongs to an index of
  `idx` in the list of the target epoch, and `f` holds the target flag.
- A target bit that is set before the run stays set.
- When `f` holds the target flag, every index of `idx` has its target bit set after the run,
  in the list of the target epoch. -/
theorem processAttestation_run_flags (att : Attestation) (st st' : BeaconState)
    (h : (processAttestation (StateTransition := HezeRun) att).run
      (pureState st) = .ok ((), pureState st')) :
    ∃ (f : Array Nat) (idx : Array ValidatorIndex),
      getAttestingIndices (pureState st) att = .ok idx ∧
      (∃ st1 : BeaconState, runPure (EthCLSpecs.Heze.getAttestationParticipationFlagIndices
        (StateTransition := HezeRun) (pureState st) att.data ((pureState st).view.slot - att.data.slot))
          st = .ok (f, st1)) ∧
      (att.data.target.epoch == previousEpochOf (pureState st) ||
        att.data.target.epoch == currentEpochOf (pureState st)) = true ∧
      (∀ w j, partBit w j (pureState st') = true → partBit w j (pureState st) = true ∨
        (w = (att.data.target.epoch == currentEpochOf (pureState st)) ∧
          UInt64.ofNat j ∈ idx ∧ f.contains timelyTargetFlagIndex = true)) ∧
      (∀ w j, partBit w j (pureState st) = true → partBit w j (pureState st') = true) ∧
      (f.contains timelyTargetFlagIndex = true → ∀ vi ∈ idx,
        partBit (att.data.target.epoch == currentEpochOf (pureState st))
          vi.toNat (pureState st') = true) := by
  unfold EthCLSpecs.Heze.processAttestation at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  -- The shape checks keep the state. Each read keeps the uncached box.
  obtain ⟨hep, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨incl, s1, hincl, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have e1 := (pureState_inj (checkedAdd_run_state hincl)).symm
  subst e1
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The offset step is a `liftErr` of `attestationCommitteeOffset`. A successful `liftErr` run
  -- returns its input state (`liftErr_run_ok_spec`), so the state after the step is
  -- `pureState st`.
  obtain ⟨off, s1', hoff, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have e2 := (pureState_inj (liftErr_run_ok_spec hoff).2).symm
  subst e2
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨f, s2, hfo, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨idx0, s4, hidx0, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨l0, s5, -, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨vb, s5', -, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨ss, s6, -, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨idx, s7, hidx, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨⟨pn, sa, wt⟩, s8, hr, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have hidx' := (liftErr_run_ok_spec hidx).1
  refine ⟨f, idx, hidx', ⟨s2, by rw [EthCLLib.Proofs.runPure_eq, hfo]; rfl⟩, hep, ?_⟩
  generalize hctd : (att.data.target.epoch == currentEpochOf (pureState st)) = ct at hr ⊢
  rw [← Array.forIn_toList] at hr
  -- A bit that the loop sets belongs to an attesting index and the target flag. The state
  -- of the accumulator stays a plain state.
  have hinv := forIn_run_inv
    (fun r : MProd EthCLSpecs.Heze.Gwei (MProd State EthCLSpecs.Heze.Gwei) =>
      (∃ u, r.2.1 = pureState u) ∧ ∀ w j, partBit w j r.2.1 = true →
        partBit w j (pureState st) = true ∨
        (w = ct ∧ UInt64.ofNat j ∈ idx ∧ f.contains timelyTargetFlagIndex = true)) _ idx.toList
    ?bstep _ _ _ _ ?binit hr
  case binit => exact ⟨⟨st, rfl⟩, fun w j hb => .inl hb⟩
  case bstep =>
    intro vi hvi rr s s' stp hP hb
    obtain ⟨r1, s1, hin, hb⟩ := run_bind_eq_ok _ _ _ _ hb
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hin
    have h1 := forIn_run_inv (fun r : MProd EthCLSpecs.Heze.Gwei (MProd State Bool) =>
        (∃ u, r.2.1 = pureState u) ∧ ∀ w j, partBit w j r.2.1 = true →
          partBit w j (pureState st) = true ∨
          (w = ct ∧ UInt64.ofNat j ∈ idx ∧ f.contains timelyTargetFlagIndex = true)) _ _
      ?bistep _ _ _ _ ?biinit hin
    case biinit => exact hP
    · -- The weight step reads the validator and adds its balance, or it skips. Neither
      -- writes the accumulator state.
      rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
      · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
        obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
        obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
        rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb]
        exact h1
      · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
        rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb]
        exact h1
    case bistep =>
      intro k hk rr s s' stp ⟨⟨u, hu⟩, hP⟩ hb
      obtain ⟨n, sa, ws⟩ := rr
      try dsimp only at hu hP hb
      subst hu
      have hk3 : k < 3 := by
        simp [List.mem_range'] at hk
        omega
      have hmem : UInt64.ofNat vi.toNat ∈ idx := by
        rw [UInt64.ofNat_toNat]
        exact Array.mem_toList_iff.mp hvi
      -- A flag outside the list leaves the accumulator as it is.
      rcases run_ite_eq_ok hb with ⟨hcon, hb⟩ | ⟨-, hb⟩
      rotate_left
      · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
        rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb]
        exact ⟨⟨u, rfl⟩, hP⟩
      -- A flag in the list reads the entry. A new flag writes it, then the run forms the
      -- reward through a checked product and a checked sum.
      rcases run_ite_eq_ok hb with ⟨hct, hb⟩ | ⟨hct, hb⟩
      · obtain ⟨y1, s1, hy1, hb⟩ := run_bind_eq_ok _ _ _ _ hb
        obtain ⟨hy1', -⟩ := sszGetIdx_run_ok hy1
        rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
        · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb]
          simp only [ForInStep.value, if_pos hct]
          refine ⟨⟨_, rfl⟩, fun w j hbit => ?_⟩
          have hb2 := (congrArg Prod.fst
            (partView_set_cur (cur := w) (i := j) u vi.toNat (addFlag y1 k))).symm.trans hbit
          cases w
          · exact hP false j hb2
          · rcases bitOf_set_addFlag _ _ _ _ hy1' k hk3 hb2 with h2 | ⟨rfl, rfl⟩
            · exact hP true j h2
            · exact .inr ⟨hct.symm, hmem, hcon⟩
        · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb]
          exact ⟨⟨u, rfl⟩, hP⟩
      · obtain ⟨y1, s1, hy1, hb⟩ := run_bind_eq_ok _ _ _ _ hb
        obtain ⟨hy1', -⟩ := sszGetIdx_run_ok hy1
        rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
        · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb]
          simp only [ForInStep.value, if_neg hct]
          refine ⟨⟨_, rfl⟩, fun w j hbit => ?_⟩
          have hb2 := (congrArg Prod.fst
            (partView_set_prev (cur := w) (i := j) u vi.toNat (addFlag y1 k))).symm.trans hbit
          cases w
          · rcases bitOf_set_addFlag _ _ _ _ hy1' k hk3 hb2 with h2 | ⟨rfl, rfl⟩
            · exact hP false j h2
            · exact .inr ⟨(Bool.not_eq_true _ ▸ hct).symm, hmem, hcon⟩
          · exact hP true j hb2
        · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          rw [EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb]
          exact ⟨⟨u, rfl⟩, hP⟩
  obtain ⟨⟨u0, hu0⟩, hback⟩ := hinv
  try dsimp only at hu0 hback
  subst hu0
  -- The final state: the payment write and the proposer reward keep the target bits.
  have hpost : ∀ w j, partBit w j (pureState st') = partBit w j (pureState u0) := by
    intro w j
    obtain ⟨x, s9, hinc, hset⟩ :=
      run_bind_eq_ok_ret (EthCLSpecs.Proofs.Heze.returnsUncached_increaseBalance _ _ _) h
    have e9 := pureState_inj (EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset)
    subst e9
    exact congrArg Prod.fst ((increaseBalance_ret_part (cur := w) (i := j) hinc).trans rfl)
  -- Each index gets its bit when the loop reaches it, and every write only adds flags. The
  -- accumulator stays a plain state, as `hinv` shows.
  have hall := forIn_run_all_inv
    (fun b : MProd EthCLSpecs.Heze.Gwei (MProd State EthCLSpecs.Heze.Gwei) =>
      ∃ u, b.2.1 = pureState u)
    (fun a b : MProd EthCLSpecs.Heze.Gwei (MProd State EthCLSpecs.Heze.Gwei) =>
      ∀ w j, partBit w j a.2.1 = true → partBit w j b.2.1 = true)
    (fun _ _ _ h => h) (fun _ _ _ h1 h2 w j hb => h2 w j (h1 w j hb))
    (fun (vi : ValidatorIndex) r => f.contains timelyTargetFlagIndex = true →
      partBit ct vi.toNat r.2.1 = true)
    (fun _ _ _ hq hr hTT => hr _ _ (hq hTT)) _ idx.toList ?fostep _ _ _ _ ⟨st, rfl⟩ hr
  case fostep =>
      intro vi _ rr s s' stp hI hb
      obtain ⟨r1, s1, hin, hb⟩ := run_bind_eq_ok _ _ _ _ hb
      rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hin
      have hin2 := forIn_run_all_inv
        (fun b : MProd EthCLSpecs.Heze.Gwei (MProd State Bool) => ∃ u, b.2.1 = pureState u)
        (fun a b : MProd EthCLSpecs.Heze.Gwei (MProd State Bool) =>
          ∀ w j, partBit w j a.2.1 = true → partBit w j b.2.1 = true)
        (fun _ _ _ h => h) (fun _ _ _ h1 h2 w j hb => h2 w j (h1 w j hb))
        (fun (k : Nat) r => f.contains timelyTargetFlagIndex = true →
          k = timelyTargetFlagIndex → partBit ct vi.toNat r.2.1 = true)
        (fun _ _ _ hq hr hTT he => hr _ _ (hq hTT he)) _ _ ?fistep _ _ _ _ hI hin
      · obtain ⟨hI1, hR1, hQ1⟩ := hin2
        have hbit := fun hTT => hQ1 timelyTargetFlagIndex
          (by simp [List.mem_range', timelyTargetFlagIndex]) hTT rfl
        rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
        · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          exact ⟨_, EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb, hI1, hR1, hbit⟩
        · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          exact ⟨_, EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb, hI1, hR1, hbit⟩
      · intro k hk rr s s' stp ⟨u, hu⟩ hb
        obtain ⟨n, sa, ws⟩ := rr
        try dsimp only at hu hb
        subst hu
        have hk3 : k < 3 := by
          simp [List.mem_range'] at hk
          omega
        -- A flag outside the list is not the target flag, since the list holds that one.
        rcases run_ite_eq_ok hb with ⟨hcon, hb⟩ | ⟨hcon, hb⟩
        rotate_left
        · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          refine ⟨_, EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb, ⟨u, rfl⟩,
            fun w j hbit => hbit, ?_⟩
          rintro hTT rfl
          exact absurd hTT hcon
        rcases run_ite_eq_ok hb with ⟨hct, hb⟩ | ⟨hct, hb⟩
        · obtain ⟨y1, s1, hy1, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨hy1', -⟩ := sszGetIdx_run_ok hy1
          rcases run_ite_eq_ok hb with ⟨hc, hb⟩ | ⟨hc, hb⟩
          · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            refine ⟨_, EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb, ?_, ?_, ?_⟩
            · show ∃ u', (if ct = true then _ else _) = pureState u'
              rw [if_pos hct]
              exact ⟨_, rfl⟩
            · intro w j hbit
              show partBit w j (if ct = true then _ else _) = true
              rw [if_pos hct]
              refine (congrArg Prod.fst
                (partView_set_cur (cur := w) (i := j) u vi.toNat (addFlag y1 k))).trans ?_
              cases w
              · exact hbit
              · exact bitOf_set_addFlag_mono _ _ _ _ hy1' k hk3 hbit
            · rintro - rfl
              show partBit ct vi.toNat (if ct = true then _ else _) = true
              rw [if_pos hct, hct]
              refine (congrArg Prod.fst
                (partView_set_cur (cur := true) (i := vi.toNat) u vi.toNat
                  (addFlag y1 _))).trans ?_
              exact bitOf_set_addFlag_self _ _ _ hy1'
          · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            refine ⟨_, EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb, ⟨u, rfl⟩,
              fun w j hbit => hbit, ?_⟩
            rintro - rfl
            rw [hct]
            -- The flag is in the entry already, since the run did not write it.
            have hf : hasFlag y1 timelyTargetFlagIndex = true := by simpa using hc
            show bitOf (sszGet (pureState u) currentEpochParticipation) vi.toNat = true
            rw [bitOf_of_getElem? _ _ _ hy1']
            exact hf
        · obtain ⟨y1, s1, hy1, hb⟩ := run_bind_eq_ok _ _ _ _ hb
          obtain ⟨hy1', -⟩ := sszGetIdx_run_ok hy1
          have hct' : ct = false := by simpa using hct
          rcases run_ite_eq_ok hb with ⟨hc, hb⟩ | ⟨hc, hb⟩
          · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            refine ⟨_, EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb, ?_, ?_, ?_⟩
            · show ∃ u', (if ct = true then _ else _) = pureState u'
              rw [if_neg hct]
              exact ⟨_, rfl⟩
            · intro w j hbit
              show partBit w j (if ct = true then _ else _) = true
              rw [if_neg hct]
              refine (congrArg Prod.fst
                (partView_set_prev (cur := w) (i := j) u vi.toNat (addFlag y1 k))).trans ?_
              cases w
              · exact bitOf_set_addFlag_mono _ _ _ _ hy1' k hk3 hbit
              · exact hbit
            · rintro - rfl
              show partBit ct vi.toNat (if ct = true then _ else _) = true
              rw [if_neg hct, hct']
              refine (congrArg Prod.fst
                (partView_set_prev (cur := false) (i := vi.toNat) u vi.toNat
                  (addFlag y1 _))).trans ?_
              exact bitOf_set_addFlag_self _ _ _ hy1'
          · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
            refine ⟨_, EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb, ⟨u, rfl⟩,
              fun w j hbit => hbit, ?_⟩
            rintro - rfl
            rw [hct']
            -- The flag is in the entry already, since the run did not write it.
            have hf : hasFlag y1 timelyTargetFlagIndex = true := by simpa using hc
            show bitOf (sszGet (pureState u) previousEpochParticipation) vi.toNat = true
            rw [bitOf_of_getElem? _ _ _ hy1']
            exact hf
  obtain ⟨-, hmono, hset⟩ := hall
  refine ⟨?back, ?mono, ?fwd⟩
  case back =>
    intro w j hb
    rw [hpost] at hb
    exact hback w j hb
  case mono =>
    intro w j hb
    rw [hpost]
    exact hmono w j hb
  case fwd =>
    intro hTT vi hvi
    rw [hpost]
    exact hset vi (Array.mem_toList_iff.mpr hvi) hTT

end

/-! ## Target flags and votes -/

section
variable [Preset] [HasherTag]

/-- The target flag of validator `i` for epoch `e` is set in `st`: in the current list when
`e` is the current epoch, in the previous list when `e` is the previous epoch and not the
current one. -/
def TargetFlagSet (st : BeaconState) (i : Nat) (e : Epoch) : Prop :=
  (e = currentEpochOf (pureState st) ∧ partBit true i (pureState st) = true) ∨
  (e = previousEpochOf (pureState st) ∧ e ≠ currentEpochOf (pureState st) ∧
    partBit false i (pureState st) = true)

/-- Two states whose slots give one epoch have one current and one previous epoch. -/
theorem epochs_eq_of_toNat {a b : BeaconState}
    (h : a.slot.toNat / slotsPerEpoch = b.slot.toNat / slotsPerEpoch) :
    currentEpochOf (pureState a) = currentEpochOf (pureState b) ∧
      previousEpochOf (pureState a) = previousEpochOf (pureState b) := by
  refine ⟨UInt64.toNat_inj.mp ?_, UInt64.toNat_inj.mp ?_⟩
  · rw [currentEpochOf_toNat, currentEpochOf_toNat]; exact h
  · rw [previousEpochOf_toNat_sub, previousEpochOf_toNat_sub, h]

/-- A state with the target bits and the slot of another state has its target flags. -/
theorem TargetFlagSet.of_partView {s s' : BeaconState} {i : Nat} {e : Epoch}
    (hb : ∀ w, partView w i (pureState s') = partView w i (pureState s))
    (hf : TargetFlagSet s' i e) : TargetFlagSet s i e := by
  have hs : s'.slot = s.slot := congrArg Prod.snd (hb true)
  obtain ⟨hc, hp⟩ := epochs_eq_of_toNat (a := s') (b := s) (by rw [hs])
  have hb' : ∀ w, partBit w i (pureState s') = partBit w i (pureState s) := fun w =>
    congrArg Prod.fst (hb w)
  unfold TargetFlagSet at hf ⊢
  rw [hc, hp, hb', hb'] at hf
  exact hf

/-- No target flag of an epoch after the current epoch is set. -/
theorem TargetFlagSet.le_current {st : BeaconState} {i : Nat} {e : Epoch}
    (hf : TargetFlagSet st i e) : e.toNat ≤ (currentEpochOf (pureState st)).toNat := by
  rcases hf with ⟨rfl, -⟩ | ⟨rfl, -, -⟩
  · exact Nat.le_refl _
  · rw [previousEpochOf_toNat_sub, currentEpochOf_toNat]
    exact Nat.sub_le _ _

/-- One vote at the state `pre`: `processAttestation` accepted the attestation and ran to
`post`. The validator is an attesting index. The source is the justified checkpoint of the
target epoch, and the target root is the block root at the target epoch. -/
def VoteAt [CryptoBackend] (pre post : BeaconState) (att : Attestation) (i : ValidatorIndex) :
    Prop :=
  runPure (processAttestation (StateTransition := HezeRun) att) pre = .ok ((), post) ∧
  (∃ idx, getAttestingIndices (pureState pre) att = .ok idx ∧ i ∈ idx) ∧
  att.data.source = sourceFor pre att.data.target.epoch ∧
  runPure (getBlockRoot (StateTransition := HezeRun) (pureState pre) att.data.target.epoch) pre
    = .ok (att.data.target.root, pre)

variable [Config] [CryptoBackend]

/-- A target flag after an attestation run was set before the run, or the run sets it for a
vote with that target epoch. -/
theorem processAttestation_explained (att : Attestation) {pre post : BeaconState}
    (h : (processAttestation (StateTransition := HezeRun) att).run (pureState pre)
      = .ok ((), pureState post)) {j : Nat} {e : Epoch} (hf : TargetFlagSet post j e) :
    TargetFlagSet pre j e ∨
      (att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j)) := by
  obtain ⟨f, idx, hidx, ⟨s1, hfo⟩, hep, hback, -⟩ := processAttestation_run_flags att pre post h
  have hsl : post.slot = pre.slot := congrArg Prod.snd (processAttestation_frame_ord h)
  obtain ⟨hc, hp⟩ := epochs_eq_of_toNat (a := post) (b := pre) (by rw [hsl])
  obtain ⟨hsrc, htgt⟩ := gapfi_target pre att.data _ f s1 hfo
  -- The vote at `pre`, once the bit is new.
  have hvote : f.contains timelyTargetFlagIndex = true → UInt64.ofNat j ∈ idx →
      VoteAt pre post att (UInt64.ofNat j) := fun hTT hj =>
    ⟨runPure_of_run_ok h, ⟨idx, hidx, hj⟩, hsrc, htgt hTT⟩
  rcases hf with ⟨he, hb⟩ | ⟨he, hne, hb⟩
  · rcases hback true j hb with h0 | ⟨hw, hj, hTT⟩
    · exact .inl (.inl ⟨he.trans hc, h0⟩)
    · refine .inr ⟨?_, hvote hTT hj⟩
      rw [he, hc]
      exact (beq_iff_eq.mp hw.symm)
  · rcases hback false j hb with h0 | ⟨hw, hj, hTT⟩
    · exact .inl (.inr ⟨he.trans hp, by rw [← hc]; exact hne, h0⟩)
    · refine .inr ⟨?_, hvote hTT hj⟩
      have hne' : att.data.target.epoch ≠ currentEpochOf (pureState pre) := by
        intro heq
        rw [heq, beq_self_eq_true] at hw
        cases hw
      rcases Bool.or_eq_true_iff.mp hep with h1 | h1
      · rw [he, hp]
        exact beq_iff_eq.mp h1
      · exact absurd (beq_iff_eq.mp h1) hne'

/-- `processAttestation` with a matching source and target sets the target flag of each
attesting index. -/
theorem processAttestation_sets_target (att : Attestation) (pre post : BeaconState)
    (idx : Array ValidatorIndex)
    (h : runPure (processAttestation (StateTransition := HezeRun) att) pre = .ok ((), post))
    (hidx : getAttestingIndices (pureState pre) att = .ok idx)
    (htgt : runPure (getBlockRoot (StateTransition := HezeRun) (pureState pre)
      att.data.target.epoch) pre = .ok (att.data.target.root, pre)) :
    ∀ i ∈ idx, TargetFlagSet post i.toNat att.data.target.epoch := by
  have hr := (EthCLLib.Proofs.runPure_iff_run_of_keepsUncached
    (keepsUncached_processAttestation att) pre post ()).mp h
  obtain ⟨f, idx', hidx', ⟨s1, hfo⟩, hep, -, -, hfwd⟩ :=
    processAttestation_run_flags att pre post hr
  rw [hidx] at hidx'
  injection hidx' with hidx'
  subst hidx'
  have hTT := gapfi_target_of_root pre att.data _ f s1 hfo htgt
  have hsl : post.slot = pre.slot :=
    congrArg Prod.snd (processAttestation_frame_ord hr)
  obtain ⟨hc, hp⟩ := epochs_eq_of_toNat (a := post) (b := pre) (by rw [hsl])
  intro i hi
  have hb := hfwd hTT i hi
  by_cases hcur : att.data.target.epoch = currentEpochOf (pureState pre)
  · rw [beq_iff_eq.mpr hcur] at hb
    exact .inl ⟨hcur.trans hc.symm, hb⟩
  · have hf : (att.data.target.epoch == currentEpochOf (pureState pre)) = false := by
      simpa using hcur
    rw [hf] at hb
    rcases Bool.or_eq_true_iff.mp hep with h1 | h1
    · exact .inr ⟨(beq_iff_eq.mp h1).trans hp.symm, by rw [hc]; exact hcur, hb⟩
    · exact absurd (beq_iff_eq.mp h1) hcur

end

/-! ## The block step and the slot step -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]
open EthCLSpecs.Heze.Const (slotsPerEpochPos slotsPerEpochLt)

/-- A target flag after `processOperations` was set before it, or an attestation of the body
set it. Only the attestation loop writes the participation lists. -/
theorem processOperations_flags (body : EthCLSpecs.Heze.BeaconBlockBody) {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run (pureState st)
      = .ok ((), pureState st')) {j : Nat} {e : Epoch} (hf : TargetFlagSet st' j e) :
    TargetFlagSet st j e ∨ ∃ att ∈ body.attestations.toArray, ∃ pre post : BeaconState,
      att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j) := by
  -- The predicate: a flag of `(j, e)` comes from `st` or from an attestation of the body.
  let P : BeaconState → Prop := fun s => TargetFlagSet s j e → TargetFlagSet st j e ∨
    ∃ att ∈ body.attestations.toArray, ∃ pre post : BeaconState,
      att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j)
  have keep : ∀ s s' : BeaconState, P s →
      (∀ w, partView w j (pureState s') = partView w j (pureState s)) → P s' :=
    fun s s' hs hb hf' => hs (hf'.of_partView hb)
  unfold EthCLSpecs.Heze.processOperations at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun ps _ =>
    keepsUncached_bind (keepsUncached_processProposerSlashing ps)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t1 : P s1 := forIn_array_ops_inv P _ keepsUncached_processProposerSlashing
    body.proposerSlashings.val
    (fun ps _ s s' hs hr => keep s s' hs fun w =>
      processProposerSlashing_frame_part (cur := w) (i := j) hr)
    st s1 (fun h0 => .inl h0) h1
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttesterSlashing a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t2 : P s2 := forIn_array_ops_inv P _ keepsUncached_processAttesterSlashing
    body.attesterSlashings.val
    (fun a _ s s' hs hr => keep s s' hs fun w =>
      processAttesterSlashing_frame_part (cur := w) (i := j) hr)
    s1 s2 t1 h2
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  -- The attestation loop: a new flag comes from the attestation that sets it.
  have t3 : P s3 := forIn_array_ops_inv P _ keepsUncached_processAttestation
    body.attestations.val
    (fun a ha s s' hs hr hf' => by
      rcases processAttestation_explained a hr hf' with h0 | ⟨he, hv⟩
      · exact hs h0
      · exact .inr ⟨a, ha, s, s', he, hv⟩)
    s2 s3 t2 h3
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processVoluntaryExit a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t4 : P s4 := forIn_array_ops_inv P _ keepsUncached_processVoluntaryExit
    body.voluntaryExits.val
    (fun a _ s s' hs hr => keep s s' hs fun w =>
      processVoluntaryExit_frame_part (cur := w) (i := j) hr)
    s3 s4 t3 h4
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processBlsToExecutionChange a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t5 : P s5 := forIn_array_ops_inv P _ keepsUncached_processBlsToExecutionChange
    body.blsToExecutionChanges.val
    (fun a _ s s' hs hr => keep s s' hs fun w =>
      processBlsToExecutionChange_frame_part (cur := w) (i := j) hr)
    s4 s5 t4 h5
  obtain ⟨⟨⟩, s6, h6, hp⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processPayloadAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  rw [pureState_inj (EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hp)] at hf
  exact forIn_array_ops_inv P _ keepsUncached_processPayloadAttestation
    body.payloadAttestations.val
    (fun a _ s s' hs hr => keep s s' hs fun w =>
      frame_of_reads (processPayloadAttestation_frame hr))
    s5 s6 t5 h6 hf

/-- A target flag after `processBlock` was set before it, or an attestation of the block body
set it. -/
theorem processBlock_flags (b : BeaconBlock) {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState st)
      = .ok ((), pureState st')) {j : Nat} {e : Epoch} (hf : TargetFlagSet st' j e) :
    TargetFlagSet st j e ∨ ∃ att ∈ b.body.attestations.toArray, ∃ pre post : BeaconState,
      att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j) := by
  unfold EthCLSpecs.Heze.processBlock at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) h
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) h
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processWithdrawals h
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_processExecutionPayloadBid _) h
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_processRandao _) h
  obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_processEth1Data _) h
  obtain ⟨⟨⟩, s7, h7, h8⟩ := run_bind_eq_ok_pure (keepsUncached_processOperations _) h
  -- Every step but the operations keeps the target bits and the slot.
  have f8 := hf.of_partView fun w => processSyncAggregate_frame_part (cur := w) (i := j) h8
  rcases processOperations_flags b.body h7 f8 with f7 | hv
  · refine .inl ?_
    have f6 := f7.of_partView fun w => processEth1Data_frame_part (cur := w) (i := j) h6
    have f5 := f6.of_partView fun w => processRandao_frame_part (cur := w) (i := j) h5
    have f4 := f5.of_partView fun w =>
      processExecutionPayloadBid_frame_part (cur := w) (i := j) h4
    have f3 := f4.of_partView fun w => processWithdrawals_frame_part (cur := w) (i := j) h3
    have f2 := f3.of_partView fun w => processBlockHeader_frame_part (cur := w) (i := j) h2
    exact f2.of_partView fun w =>
      processParentExecutionPayload_frame_part (cur := w) (i := j) h1
  · exact .inr hv

/-- A block step: a target flag after it was set before it, or an attestation of the block
set it. -/
theorem BlockStep.targetFlag {sb : SignedBeaconBlock} {v : Bool} {st st' : BeaconState}
    (h : BlockStep sb v st st') {j : Nat} {e : Epoch} (hf : TargetFlagSet st' j e) :
    TargetFlagSet st j e ∨ ∃ att ∈ sb.message.body.attestations.toArray,
      ∃ pre post : BeaconState, att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j) :=
  processBlock_flags sb.message h.2.1 hf

/-- A slot step keeps each target flag at its epoch. Without an epoch boundary, the lists and
the epochs stay. At a boundary, the epoch step moves the current flags to the previous list,
and the slot increment makes the old current epoch the previous one. When the increment wraps
to slot zero, the previous epoch is the current one, so no previous flag counts. -/
theorem SlotStep.targetFlag {st st' : BeaconState} (h : SlotStep st st') {i : Nat} {e : Epoch}
    (hf : TargetFlagSet st' i e) : TargetFlagSet st i e := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 : ∀ w, partView w i (pureState st1) = partView w i (pureState st) := fun w =>
    processSlot_frame_part (cur := w) h1
  have sl1 : st1.slot = st.slot := congrArg Prod.snd (e1 true)
  have b1 : ∀ w, partBit w i (pureState st1) = partBit w i (pureState st) := fun w =>
    congrArg Prod.fst (e1 w)
  have b' : ∀ w, partBit w i (pureState st') = partBit w i (pureState st2) := by
    intro w
    rw [hst']
    rfl
  have sl' : st'.slot = st2.slot + 1 := by
    change sszGet (pureState st') slot = _
    rw [hst']
    rfl
  split at h2
  · rename_i htest
    obtain ⟨c2, p2, sl2⟩ := processEpoch_part h2 i
    rcases hf with ⟨-, hb⟩ | ⟨hep, hne, hb⟩
    · rw [b', c2] at hb
      cases hb
    · rw [b'] at hb
      have hc1 := p2 hb
      rw [b1] at hc1
      refine .inl ⟨?_, hc1⟩
      rw [sl2, sl1] at sl'
      by_cases hw : st.slot.toNat + 1 < 2 ^ 64
      · have hb0 := (epochTest_iff st1.slot (by rw [sl1]; exact hw)).mp htest
        rw [sl1] at hb0
        have hsn : st'.slot.toNat = st.slot.toNat + 1 := by
          rw [sl', UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hw]
        rw [hep]
        apply UInt64.toNat_inj.mp
        rw [previousEpochOf_toNat_sub, currentEpochOf_toNat, hsn, succ_div_of_mod_eq hb0]
        rfl
      · -- The increment wraps: the previous epoch is the current epoch.
        exfalso
        have h0 : st'.slot.toNat = 0 := by
          rw [sl', UInt64.toNat_add, UInt64.toNat_one]
          have := st.slot.toNat_lt
          rw [show st.slot.toNat + 1 = 2 ^ 64 by omega, Nat.mod_self]
        apply hne
        rw [hep]
        apply UInt64.toNat_inj.mp
        rw [previousEpochOf_toNat_sub, currentEpochOf_toNat]
        change st'.slot.toNat / slotsPerEpoch - 1 = st'.slot.toNat / slotsPerEpoch
        rw [h0, Nat.zero_div]
  · rename_i htest
    rw [h2] at sl' b'
    -- No epoch boundary: the increment does not wrap, and the epoch stays.
    have hw : st.slot.toNat + 1 < 2 ^ 64 := by
      refine Classical.byContradiction fun hw => htest ?_
      have hz : st1.slot + 1 = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_one, sl1]
        have := st.slot.toNat_lt
        rw [show st.slot.toNat + 1 = 2 ^ 64 by omega, Nat.mod_self]
        rfl
      change ((st1.slot + 1) % UInt64.ofNat slotsPerEpoch == 0) = true
      rw [hz]
      simp
    have hb0 : (st.slot.toNat + 1) % slotsPerEpoch ≠ 0 := fun hb0 =>
      htest ((epochTest_iff st1.slot (by rw [sl1]; exact hw)).mpr (by rw [sl1]; exact hb0))
    have hsn : st'.slot.toNat = st.slot.toNat + 1 := by
      rw [sl', sl1, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hw]
    obtain ⟨hcur, hprev⟩ := epochs_eq_of_toNat (a := st') (b := st)
      (by rw [hsn, succ_div_of_mod_ne hb0])
    unfold TargetFlagSet at hf ⊢
    rw [hcur, hprev, b', b', b1, b1] at hf
    exact hf

end

/-! ## Along a chain run -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- An included vote of validator `i` with the data `data`: a block step of the run carries an
attestation with that data, which `processAttestation` accepted on a state `pre`. The
validator is an attesting index there. The source is the justified checkpoint of the target
epoch, and the target root is the block root at the target epoch, both in `pre`. -/
structure IncludedVote (steps : List ChainStep) (i : ValidatorIndex) (data : AttestationData) :
    Prop where
  exists_att : ∃ (sb : SignedBeaconBlock) (v : Bool) (pre post : BeaconState) (att : Attestation)
    (idx : Array ValidatorIndex),
    ChainStep.block sb v ∈ steps ∧ att ∈ sb.message.body.attestations.toArray ∧ att.data = data ∧
    runPure (processAttestation (StateTransition := HezeRun) att) pre = .ok ((), post) ∧
    getAttestingIndices (pureState pre) att = .ok idx ∧ i ∈ idx ∧
    data.source = sourceFor pre data.target.epoch ∧
    runPure (getBlockRoot (StateTransition := HezeRun) (pureState pre) data.target.epoch) pre
      = .ok (data.target.root, pre)

omit [Config] in
/-- An included vote stays included in a longer list of steps. -/
theorem IncludedVote.mono {steps steps' : List ChainStep} {i : ValidatorIndex}
    {data : AttestationData} (h : IncludedVote steps i data)
    (hs : ∀ x ∈ steps, x ∈ steps') : IncludedVote steps' i data := by
  obtain ⟨sb, v, pre, post, att, idx, hb, rest⟩ := h.exists_att
  exact ⟨⟨sb, v, pre, post, att, idx, hs _ hb, rest⟩⟩

omit [Config] in
/-- A vote of a block in the steps is an included vote. -/
theorem IncludedVote.of_voteAt {steps : List ChainStep} {sb : SignedBeaconBlock} {v : Bool}
    {pre post : BeaconState} {att : Attestation} {i : ValidatorIndex}
    (hb : ChainStep.block sb v ∈ steps) (ha : att ∈ sb.message.body.attestations.toArray)
    (hv : VoteAt pre post att i) : IncludedVote steps i att.data := by
  obtain ⟨hrun, ⟨idx, hidx, hi⟩, hsrc, htgt⟩ := hv
  exact ⟨⟨sb, v, pre, post, att, idx, hb, ha, rfl, hrun, hidx, hi, hsrc, htgt⟩⟩

/-- Along a chain run, a target flag at the end was set at the start, or a vote of the run
with that target epoch set it. -/
theorem ChainRun.flag_cases {hi : Nat} {steps : List ChainStep} {u st : BeaconState}
    (h : ChainRun hi steps u st) :
    ∀ (i : Nat) (e : Epoch), TargetFlagSet st i e → TargetFlagSet u i e ∨
      ∃ data : AttestationData, data.target.epoch = e ∧
        IncludedVote steps (UInt64.ofNat i) data := by
  induction h with
  | nil => exact fun _ _ hf => .inl hf
  | slot _ hstep _ ih =>
    intro i e hf
    rcases ih i e hf with h1 | ⟨d, hd, hv⟩
    · exact .inl (hstep.targetFlag h1)
    · exact .inr ⟨d, hd, hv.mono fun x hx => List.mem_cons_of_mem _ hx⟩
  | block sb v hstep _ ih =>
    intro i e hf
    rcases ih i e hf with h1 | ⟨d, hd, hv⟩
    · rcases hstep.targetFlag h1 with h2 | ⟨att, ha, pre, post, he, hv⟩
      · exact .inl h2
      · exact .inr ⟨att.data, he, IncludedVote.of_voteAt List.mem_cons_self ha hv⟩
    · exact .inr ⟨d, hd, hv.mono fun x hx => List.mem_cons_of_mem _ hx⟩

/-- Along a chain run, each target flag of an epoch after the current epoch of the start
state comes from an included vote with that target epoch. -/
theorem ChainRun.flag_explained {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    (h : ChainRun hi steps st₀ st) (i : Nat) (e : Epoch)
    (he : currentEpochOf (pureState st₀) < e) (hf : TargetFlagSet st i e) :
    ∃ data, data.target.epoch = e ∧ IncludedVote steps (UInt64.ofNat i) data := by
  rcases h.flag_cases i e hf with h0 | hv
  · have := h0.le_current
    rw [UInt64.lt_iff_toNat_lt] at he
    omega
  · exact hv

end

end EthCLSpecs.Proofs.Heze
