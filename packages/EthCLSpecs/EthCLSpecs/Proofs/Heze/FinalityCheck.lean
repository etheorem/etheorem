import EthCLSpecs.Proofs.Heze.FinalizationLiveness
import EthCLSpecs.Proofs.Heze.RaceCheck

/-!
# `EthCLSpecs.Proofs.Heze.FinalityCheck`: the finality premises as computations

`censored_payload_final` (`FinalizationLiveness.lean`) takes `FinalitySetting`. Its premises
quantify over the store runs of honest stores, the runs of a chain, and the head runs of a
window. A concrete execution needs a computation for each one. This module gives the checks,
and the lemmas that turn a passing check into a premise. `Tests/HezeFinalityWitness.lean` and
`Tests/HezeAccountableWitness.lean` run them.

## Store runs

A store run of `s` follows an ancestor path of `s` (`StoreRun`). Take a store whose blocks are
the anchor block and blocks of a chain `W` of steps. Each block of `W` has the root of the block
before it as its parent root, and the roots of the anchor and the blocks of `W` are distinct.

- Every block of a traced store sits at its root (`NodeTrace.blocks_at`).
- So an ancestor path lists the first `j` blocks of `W` (`AncestorPath.take_of_linked`).
- A run that ends at a block and lists the first `j` blocks of `W` takes the steps of a prefix of
  `W` (`steps_prefix`). A block step needs the block slot to be the state slot, so the slot steps
  between two blocks are fixed by the block slots.
- So every state on a store run is a state on the run of `W` (`ChainStore.state_mem`). A check
  over the states of `W` (`runStates`) then gives `StoreTotals` and the stake bound of
  `allChains`.
- A vote on a store run is a vote of a block of `W` (`RunVote.data_mem`). A check over the votes
  of `W` gives `honestVotes` (`honestVotes_of_check`).

## Checkpoint blocks

`getCheckpointBlock` reads only its store argument (`getCheckpointBlock_run_transfer`). At an
epoch whose first slot is at or after the block, it returns the block itself
(`getCheckpointBlock_run_self`). At an epoch whose first slot does not fit in `uint64`, it
raises. So a check over the epochs up to the one after the head block gives `early`
(`early_of_check`).

## Slashing evidence

`SlashingEvidence.of_check` checks the pairs over the states of two runs. The stake of the
common validators is a sum over the registry of the fork state (`activeStake_commonOf`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure LawfulFcMap KeepsAt)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root SignedBeaconBlock
  SignedInclusionList ExecutionPayload Transaction ExecutionRequests onBlock)

/-! ## The blocks of a traced store -/

section Blocks
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability]

/-- **Every block of a traced store sits at its root and meets `P`.** The seed has this
property, and `P` holds for the block of every block event. `onBlock` inserts a block at its
root (`onBlock_run_maps`), and the other handlers keep the block map. -/
theorem NodeTrace.blocks_at {P : BeaconBlock → Prop} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s)
    (h0 : ∀ k b, FcMap.lookup s0.blocks k = some b → htr b = k ∧ P b)
    (hev : ∀ sb, TraceEvent.handler (.block sb) ∈ events → P sb.message) :
    ∀ k b, FcMap.lookup s.blocks k = some b → htr b = k ∧ P b := by
  induction h with
  | nil => exact h0
  | @handler events arrs pre post e htrace hrun ih =>
    have ih' := ih fun sb hm => hev sb (List.mem_append_left _ hm)
    have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
        KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
          (pre.blocks, pre.blockStates) x →
        x.run pre = .ok ((), post) → post.blocks = pre.blocks := by
      intro x hx hrunx
      exact congrArg Prod.fst (hx pre () post rfl hrunx)
    have hsame : post.blocks = pre.blocks →
        ∀ k b, FcMap.lookup post.blocks k = some b → htr b = k ∧ P b := fun he k b hb =>
      ih' k b (he ▸ hb)
    cases e with
    | tick time => exact hsame (hkeep _ (onTick_keeps_blockMaps _ time) hrun)
    | attestation att isFromBlock =>
      exact hsame (hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock) hrun)
    | attesterSlashing asl =>
      exact hsame (hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl) hrun)
    | payloadAttestation msg isFromBlock =>
      exact hsame (hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock) hrun)
    | envelope signedEnv =>
      exact hsame (onExecutionPayloadEnvelope_run_keys signedEnv pre post hrun).1
    | block sb =>
      intro k b hb
      rw [(onBlock_run_maps sb pre post hrun).1] at hb
      by_cases hk : htr sb.message = k
      · subst hk
        rw [LawfulFcMap.lookup_insert_self] at hb
        cases hb
        exact ⟨rfl, hev sb (List.mem_append_right _ (List.mem_singleton_self _))⟩
      · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk] at hb
        exact ih' k b hb
  | @inclusionList events arrs pre post signed t htrace hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih fun sb hm => hev sb (List.mem_append_left _ hm)

/-- The anchor store holds the anchor block at its root and nothing else. -/
theorem getForkchoiceStore_blocks_at (A : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok s0) {k : Root}
    {b : BeaconBlock} (hb : FcMap.lookup s0.blocks k = some b) : htr b = k ∧ b = a := by
  have hba := getForkchoiceStore_blocks A a s0 h hb
  subst hba
  refine ⟨?_, rfl⟩
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  by_cases hk : htr b = k
  · exact hk
  · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk, LawfulFcMap.lookup_empty] at hb
    cases hb

end Blocks

/-! ## Ancestor paths along a chain of blocks -/

section Paths
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The roots of the anchor `a` and of the blocks `bs`, in order. -/
def chainRoots (a : BeaconBlock) (bs : List BeaconBlock) : List Root :=
  htr a :: bs.map htr

/-- The blocks `bs` form a chain from `a`: the parent root of each block is the root of the
block before it, and the first block names `a`. -/
def linkedB (a : BeaconBlock) (bs : List BeaconBlock) : Bool :=
  (List.range bs.length).all fun i =>
    decide ((bs[i]!).parentRoot = (chainRoots a bs)[i]!)

omit [FcMap map] in
/-- The `i`-th block of a linked chain names the `i`-th root of `chainRoots`. -/
theorem linkedB_parent {a : BeaconBlock} {bs : List BeaconBlock} (h : linkedB a bs = true)
    {i : Nat} (hi : i < bs.length) : bs[i].parentRoot = (chainRoots a bs)[i]! := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [decide_eq_true_eq, getElem!_pos bs i hi] at this
  exact this

omit [FcMap map] in
/-- Root `j + 1` of `chainRoots` is the root of block `j`. -/
theorem chainRoots_succ (a : BeaconBlock) (bs : List BeaconBlock) {j : Nat} (hj : j < bs.length) :
    (chainRoots a bs)[j + 1]! = htr bs[j] := by
  unfold chainRoots
  rw [getElem!_pos _ _ (by simp; omega)]
  simp

omit [FcMap map] in
/-- Root `j` of `chainRoots` for `j ≤ bs.length`, as a member of the list. -/
theorem chainRoots_get_mem (a : BeaconBlock) (bs : List BeaconBlock) {j : Nat}
    (hj : j ≤ bs.length) : (chainRoots a bs)[j]! = (chainRoots a bs)[j]'(by
      unfold chainRoots; simp; omega) :=
  getElem!_pos _ _ _

omit [Preset] [HasherTag] [FcMap map] in
/-- Two places of a list with no duplicate that hold one value are one place. -/
theorem nodup_getElem_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (he : l[i] = l[j]) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd he (List.pairwise_iff_getElem.mp h i j hi hj hlt)
  · exact heq
  · exact absurd he.symm (List.pairwise_iff_getElem.mp h j i hj hi hgt)

/-- **An ancestor path in a store of chain blocks lists a prefix of the chain.** Every block of
the store sits at its root and is the anchor or a block of `bs`. The blocks `bs` are linked from
`a`, and the roots of `chainRoots a bs` are distinct. Then an ancestor path to `k` lists the first
`j` blocks of `bs`, and `k` is root `j` of `chainRoots a bs`. -/
theorem AncestorPath.take_of_linked {a : BeaconBlock} {s : Store map} {bs : List BeaconBlock}
    (hs : ∀ k b, FcMap.lookup s.blocks k = some b → htr b = k ∧ (b = a ∨ b ∈ bs))
    (hl : linkedB a bs = true) (hnd : (chainRoots a bs).Nodup) {k : Root}
    {path : List BeaconBlock} (h : AncestorPath a s k path) :
    ∃ j, j ≤ bs.length ∧ path = bs.take j ∧ k = (chainRoots a bs)[j]! := by
  induction h with
  | anchor => exact ⟨0, Nat.zero_le _, rfl, by simp [chainRoots]⟩
  | @cons k b path hk hne _ ih =>
    obtain ⟨j, hj, rfl, hpar⟩ := ih
    obtain ⟨hroot, hmem⟩ := hs k b hk
    have hb : b ∈ bs := hmem.resolve_left hne
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    -- The parent root of block `i` is root `i`, and it is root `j`, so `i = j`.
    have hpi := linkedB_parent hl hi
    rw [hpar, chainRoots_get_mem a bs hj, chainRoots_get_mem a bs (Nat.le_of_lt hi)] at hpi
    have hij : i = j := nodup_getElem_inj hnd _ _ hpi.symm
    subst hij
    refine ⟨i + 1, hi, ?_, ?_⟩
    · rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    · rw [chainRoots_succ a bs hi, hroot]

end Paths

/-! ## Store runs follow the chain -/

section Steps
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [HasherTag] [Config] [CryptoBackend] in
/-- A run that ends at a block and starts with a slot step has a block after that step, and
the rest of it ends at a block. -/
theorem EndsAtBlock.of_slot {S : List ChainStep} (h : EndsAtBlock (.slot :: S)) :
    EndsAtBlock S ∧ blocksOf S ≠ [] := by
  rcases h with h | ⟨p, sb, v, hp⟩
  · cases h
  · cases p with
    | nil => cases hp
    | cons x p' =>
      injection hp with _ hS
      subst hS
      refine ⟨.inr ⟨p', sb, v, rfl⟩, ?_⟩
      rw [List.append_eq, blocksOf_append]
      simp [blocksOf]

omit [HasherTag] [Config] [CryptoBackend] in
/-- The rest of a run that ends at a block and starts with a block step ends at a block. -/
theorem EndsAtBlock.of_block {S : List ChainStep} {sb : SignedBeaconBlock} {v : Bool}
    (h : EndsAtBlock (.block sb v :: S)) : EndsAtBlock S := by
  rcases h with h | ⟨p, sb', v', hp⟩
  · cases h
  · cases p with
    | nil =>
      injection hp with _ hS
      exact .inl hS
    | cons x p' =>
      injection hp with _ hS
      exact .inr ⟨p', sb', v', hS⟩

/-- **A run that ends at a block and lists a prefix of the blocks of `W` takes the steps of a
prefix of `W`.** The two runs start at one state. Step by step they agree: a slot step against a
block step fails, because a block has the slot of its start state, and every block after a slot
step has a later slot (`ChainRun.slot_le`). Two block steps take one block, and two steps of one
kind reach one state. The step lists agree up to the signatures of their blocks
(`stepMsg`). -/
theorem steps_prefix {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {S : List ChainStep}
    {A sEnd : BeaconState} (hS : ChainRun hi S A sEnd) :
    ∀ {W : List ChainStep} {wEnd : BeaconState}, ChainRun hi W A wEnd → EndsAtBlock S →
      (∃ j, blocksOf S = (blocksOf W).take j) →
      ∃ W₁ W₂, W = W₁ ++ W₂ ∧ W₁.map stepMsg = S.map stepMsg := by
  induction hS with
  | nil => exact fun {W} _ _ _ _ => ⟨[], W, rfl, rfl⟩
  | @slot S st st1 _ hlt hstep hrest ih =>
    intro W wEnd hW hend ⟨j, hj⟩
    obtain ⟨hend', hne⟩ := EndsAtBlock.of_slot hend
    have hlt' : st.slot.toNat < hi := hlt
    have hs1 := hstep.slot (by omega)
    cases hW with
    | nil =>
      rw [show blocksOf (ChainStep.slot :: S) = blocksOf S from rfl] at hj
      simp [blocksOf] at hj
      exact absurd hj hne
    | slot _ hstep' hrest' =>
      rw [hstep.det hstep'] at ih
      obtain ⟨W₁, W₂, rfl, hmap⟩ := ih hrest' hend' ⟨j, hj⟩
      exact ⟨.slot :: W₁, W₂, rfl, by simp [hmap, stepMsg]⟩
    | @block W' _ w1 _ sb v hstep' hrest' =>
      -- The first block of `S` is the block of the block step, at the start slot.
      exfalso
      obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
      have hj' : blocksOf S = (sb.message :: blocksOf W').take j := hj
      rw [hbs] at hj'
      cases j with
      | zero => simp at hj'
      | succ j =>
        simp only [List.take_succ_cons, List.cons.injEq] at hj'
        have hb : b ∈ blocksOf S := by rw [hbs]; exact List.mem_cons_self
        have hge := ((hrest.slot_le hhi).2 b hb).1
        rw [hj'.1, hstep'.slot.2] at hge
        omega
  | @block S st st1 _ sb v hstep hrest ih =>
    intro W wEnd hW hend ⟨j, hj⟩
    have hend' := EndsAtBlock.of_block hend
    cases hW with
    | nil =>
      simp [blocksOf] at hj
    | @slot W' _ w1 _ hlt' hstep' hrest' =>
      -- A block of `W` after a slot step has a later slot than the block of `S`.
      exfalso
      have hlt'' : st.slot.toNat < hi := hlt'
      have hs1 := hstep'.slot (by omega)
      have hj' : sb.message :: blocksOf S = (blocksOf W').take j := hj
      cases j with
      | zero => simp at hj'
      | succ j =>
        cases hbw : blocksOf W' with
        | nil =>
          rw [hbw] at hj'
          simp at hj'
        | cons b bs =>
          rw [hbw] at hj'
          simp only [List.take_succ_cons, List.cons.injEq] at hj'
          have hb : b ∈ blocksOf W' := by rw [hbw]; exact List.mem_cons_self
          have hge := ((hrest'.slot_le hhi).2 b hb).1
          rw [← hj'.1, hstep.slot.2] at hge
          omega
    | @block W' _ w1 _ sb' v' hstep' hrest' =>
      have hj' : sb.message :: blocksOf S = (sb'.message :: blocksOf W').take j := hj
      cases j with
      | zero => simp at hj'
      | succ j =>
        simp only [List.take_succ_cons, List.cons.injEq] at hj'
        obtain ⟨hm, hj''⟩ := hj'
        rw [hstep.det_msg hstep' hm] at ih
        obtain ⟨W₁, W₂, rfl, hmap⟩ := ih hrest' hend' ⟨j, hj''⟩
        exact ⟨.block sb' v' :: W₁, W₂, rfl, by simp [hmap, stepMsg, hm]⟩

/-- The states of a run, in order: the start state and the state after each step. `none` when a
step fails. Each step is `runChain` of one step. -/
def runStates (hi : Nat) : List ChainStep → BeaconState → Option (List BeaconState)
  | [], st => some [st]
  | x :: rest, st =>
    match runChain hi [x] st with
    | some st1 => (runStates hi rest st1).map (st :: ·)
    | none => none

/-- State `n` of `runStates` is the end of the run of the first `n` steps. -/
theorem runStates_take {hi : Nat} :
    ∀ {W : List ChainStep} {A : BeaconState} {L : List BeaconState},
      runStates hi W A = some L → ∀ n, n ≤ W.length →
        ∃ u, L[n]? = some u ∧ ChainRun hi (W.take n) A u
  | [], A, L, h, n, hn => by
    cases h
    obtain rfl : n = 0 := by simpa using hn
    exact ⟨A, rfl, .nil A⟩
  | x :: rest, A, L, h, n, hn => by
    simp only [runStates] at h
    split at h
    · rename_i st1 h1
      obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.mp h
      cases n with
      | zero => exact ⟨A, rfl, .nil A⟩
      | succ m =>
        obtain ⟨u, hu, hrun⟩ := runStates_take hL' m (by simp at hn; omega)
        refine ⟨u, by simpa using hu, ?_⟩
        have h1 := ChainRun.of_runChain [x] A st1 h1
        simpa using h1.append hrun
    · cases h

/-- A state on a run of a prefix of `W` is a state of `runStates`. -/
theorem runStates_mem {hi : Nat} {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    (h : runStates hi W A = some L) {P Q : List ChainStep} (hW : W = P ++ Q) {u : BeaconState}
    (hu : ChainRun hi P A u) : u ∈ L := by
  obtain ⟨u', hu', hrun⟩ := runStates_take h P.length (by rw [hW]; simp)
  rw [hW, List.take_left] at hrun
  rw [hu.det hrun]
  exact List.mem_of_getElem? hu'

/-- The run of `W` itself, from `runStates`. -/
theorem runStates_run {hi : Nat} {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    (h : runStates hi W A = some L) : ∃ w, ChainRun hi W A w := by
  obtain ⟨w, -, hrun⟩ := runStates_take h W.length (Nat.le_refl _)
  rw [List.take_length] at hrun
  exact ⟨w, hrun⟩

/-- The premises that tie a store to the chain `W` from `A`: its states, and its blocks at
their roots, linked from `a` with distinct roots. -/
structure ChainStore {map : MapKind} [FcMap map] (A : BeaconState) (a : BeaconBlock)
    (W : List ChainStep) (L : List BeaconState) (s : Store map) : Prop where
  /-- The states of the run of `W`. -/
  states : runStates (2 ^ 64 - 1) W A = some L
  /-- Every block of the store sits at its root, and it is `a` or a block of `W`. -/
  blocks : ∀ k b, FcMap.lookup s.blocks k = some b → htr b = k ∧ (b = a ∨ b ∈ blocksOf W)
  /-- The blocks of `W` are linked from `a`. -/
  linked : linkedB a (blocksOf W) = true
  /-- The roots of `a` and of the blocks of `W` are distinct. -/
  nodup : (chainRoots a (blocksOf W)).Nodup

/-- The blocks of a store run are the first blocks of `W`. -/
theorem ChainStore.blocks_take {map : MapKind} [FcMap map] {A : BeaconState} {a : BeaconBlock}
    {W : List ChainStep} {L : List BeaconState} {s : Store map} (hc : ChainStore A a W L s)
    {steps : List ChainStep} (hsr : StoreRun A a s steps) :
    ∃ j, blocksOf steps = (blocksOf W).take j := by
  obtain ⟨k, v, -, hpath, -, -⟩ := hsr
  obtain ⟨j, -, hb, -⟩ := AncestorPath.take_of_linked hc.blocks hc.linked hc.nodup hpath
  exact ⟨j, hb⟩

/-- **Every state on a store run is a state of the run of `W`.** The store run takes the steps
of a prefix of `W` (`steps_prefix`). So a prefix `p` of the store run is a prefix of `W` up to
the signatures of its blocks, and it reaches the state that `W` reaches there
(`ChainRun.det_msg`). -/
theorem ChainStore.state_mem {map : MapKind} [FcMap map] {A : BeaconState} {a : BeaconBlock}
    {W : List ChainStep} {L : List BeaconState} {s : Store map} (hc : ChainStore A a W L s)
    {p q : List ChainStep} (hsr : StoreRun A a s (p ++ q)) {u : BeaconState}
    (hp : ChainRun (2 ^ 64 - 1) p A u) : u ∈ L := by
  have hj := hc.blocks_take hsr
  obtain ⟨k, v, hrun, -, -, hend⟩ := hsr
  obtain ⟨w, hW⟩ := runStates_run hc.states
  obtain ⟨W₁, W₂, hW12, hmap⟩ := steps_prefix (Nat.le_refl _) hrun hW hend hj
  rw [List.map_append] at hmap
  obtain ⟨P₁, P₂, rfl, h1, -⟩ := List.map_eq_append_iff.mp hmap
  rw [List.append_assoc] at hW12
  rw [hW12] at hW
  obtain ⟨m, hm, -⟩ := ChainRun.split hW
  rw [hp.det_msg hm h1.symm]
  exact runStates_mem hc.states hW12 hm

end Steps

section TraceStore
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability]

/-- **A traced store of chain blocks is a `ChainStore`.** The store starts at the anchor store
of `A` and `a`, and every block event of the trace is a block of `W`. -/
theorem ChainStore.of_trace {A : BeaconState} {a : BeaconBlock} {W : List ChainStep}
    {L : List BeaconState} {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)}
    (hs0 : EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok s0)
    (h : NodeTrace s0 events arrivals s)
    (hev : ∀ sb, TraceEvent.handler (.block sb) ∈ events → sb.message ∈ blocksOf W)
    (hL : runStates (2 ^ 64 - 1) W A = some L) (hl : linkedB a (blocksOf W) = true)
    (hnd : (chainRoots a (blocksOf W)).Nodup) : ChainStore A a W L s :=
  ⟨hL, h.blocks_at (P := fun b => b = a ∨ b ∈ blocksOf W)
    (fun _ _ hb => let h' := getForkchoiceStore_blocks_at A a s0 hs0 hb; ⟨h'.1, .inl h'.2⟩)
    (fun sb hm => .inr (hev sb hm)), hl, hnd⟩

end TraceStore

/-! ## The node tree as a computation -/

section Walk
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

open EthCLSpecs.Heze (ForkChoiceNode getParentPayloadStatus)
open EthCLSpecs.Heze.Const (payloadStatusPending payloadStatusEmpty payloadStatusFull)

/-- The parent of a node in the node tree of `store`. A pending node has the node that its
block's parent root and parent payload status name. An EMPTY or FULL node has the pending node
of its root. Each node has at most one parent (`NodeEdge.parent_unique`). -/
def nodeParent (store : Store map) (n : ForkChoiceNode) : Option ForkChoiceNode :=
  if n.payloadStatus = payloadStatusPending then
    match FcMap.lookup store.blocks n.root with
    | some b =>
      match (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
          store b).run store with
      | .ok (ps, _) => some { root := b.parentRoot, payloadStatus := ps }
      | .error _ => none
    | none => none
  else if n.payloadStatus = payloadStatusEmpty ∨ n.payloadStatus = payloadStatusFull then
    some (.pending n.root)
  else none

/-- `nodeParent` names an edge of the node tree. -/
theorem nodeParent_edge {store : Store map} {n p : ForkChoiceNode}
    (h : nodeParent store n = some p) : NodeEdge store p n := by
  unfold nodeParent at h
  split at h
  · rename_i hpend
    split at h
    · rename_i b hb
      split at h
      · rename_i ps s' hps
        cases h
        have hn : n = .pending n.root :=
          node_eq_of_root_status _ _ rfl hpend
        rw [hn]
        exact .block _ n.root b store s' hb rfl hps
      · cases h
    · cases h
  · split at h
    · rename_i hdec
      cases h
      rcases hdec with he | hf
      · have hn : n = .empty n.root := node_eq_of_root_status _ _ rfl he
        rw [hn]
        exact .empty n.root
      · have hn : n = .full n.root := node_eq_of_root_status _ _ rfl hf
        rw [hn]
        exact .full n.root
    · cases h

/-- An edge of the node tree is the edge that `nodeParent` names. -/
theorem nodeParent_of_edge {store : Store map} {p n : ForkChoiceNode} (h : NodeEdge store p n) :
    nodeParent store n = some p := by
  rcases NodeEdge.cases_on_child store p n h with
    ⟨hp, hn | hn⟩ | ⟨root, b, s, s', hn, hb, hpar, hps⟩
  · rw [hn, hp]
    simp [nodeParent, ForkChoiceNode.empty, ForkChoiceNode.pending, payloadStatusEmpty,
      payloadStatusPending]
  · rw [hn, hp]
    simp [nodeParent, ForkChoiceNode.full, ForkChoiceNode.pending, payloadStatusFull,
      payloadStatusPending, payloadStatusEmpty]
  · subst hn
    obtain ⟨pb, hpb⟩ := getParentPayloadStatus_run_parent store s s' b _ hps
    have hrun := getParentPayloadStatus_run_transfer store store b pb hpb hpb hps store
    simp only [nodeParent, ForkChoiceNode.pending, if_pos, hb, hrun, hpar]

/-- The nodes from `n` up the node tree, `n` first, for at most `fuel` steps. -/
def ancestorsB (store : Store map) : Nat → ForkChoiceNode → List ForkChoiceNode
  | 0, n => [n]
  | fuel + 1, n =>
    n :: match nodeParent store n with
      | some p => ancestorsB store fuel p
      | none => []

/-- The walk up from `n` reaches a node with no parent within `fuel` steps. -/
def walkDone (store : Store map) : Nat → ForkChoiceNode → Bool
  | 0, _ => false
  | fuel + 1, n =>
    match nodeParent store n with
    | some p => walkDone store fuel p
    | none => true

/-- A node of the walk is an ancestor. -/
theorem below_of_mem_ancestorsB {store : Store map} {anc : ForkChoiceNode} :
    ∀ (fuel : Nat) (n : ForkChoiceNode), anc ∈ ancestorsB store fuel n → NodeBelow store anc n
  | 0, n, h => by
    simp only [ancestorsB, List.mem_singleton] at h
    subst h
    exact .refl
  | fuel + 1, n, h => by
    simp only [ancestorsB, List.mem_cons] at h
    rcases h with rfl | h
    · exact .refl
    · split at h
      · rename_i p hp
        exact .step p n (below_of_mem_ancestorsB fuel p h) (nodeParent_edge hp)
      · cases h

/-- A complete walk lists every ancestor. Each node has one parent, so the walk follows the
only path up. -/
theorem mem_ancestorsB_of_below {store : Store map} {anc n : ForkChoiceNode}
    (h : NodeBelow store anc n) :
    ∀ fuel, walkDone store fuel n = true → anc ∈ ancestorsB store fuel n := by
  induction h with
  | refl =>
    intro fuel _
    cases fuel <;> simp [ancestorsB]
  | step p c _ hpc ih =>
    intro fuel hdone
    cases fuel with
    | zero => simp [walkDone] at hdone
    | succ fuel =>
      have hpar := nodeParent_of_edge hpc
      simp only [walkDone, hpar] at hdone
      simp only [ancestorsB, hpar, List.mem_cons]
      exact .inr (ih fuel hdone)

end Walk

/-! ## Runs that read only the store argument -/

section Transfer
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

open EthCLLib.Proofs (run_bind run_pure run_bind_eq_ok run_pure_eq_ok except_bind_ok
  run_liftErr_of_ok run_liftErr_of_error)
open EthCLSpecs.Heze (ForkChoiceNode getCheckpointBlock getAncestor)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

/-- A loop whose steps ignore the runner state ignores it too. -/
theorem fuelLoop_run_transfer {σ ε β α : Type} (step : β → StateT σ (Except ε) (Step β α))
    (hstep : ∀ b x (s s' : σ), (step b).run s = .ok (x, s') → ∀ u, (step b).run u = .ok (x, u)) :
    ∀ (fuel : Nat) (init : β) (exhausted : α) (s s' : σ) (a : α),
      (fuelLoop fuel init exhausted step).run s = .ok (a, s') →
      ∀ u, (fuelLoop fuel init exhausted step).run u = .ok (a, u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro init exhausted s s' a h u
    simp only [fuelLoop] at h ⊢
    rw [run_pure_eq_ok _ _ _ _ h]
    rfl
  | succ fuel ih =>
    intro init exhausted s s' a h u
    simp only [fuelLoop] at h ⊢
    obtain ⟨x, s1, hx, h⟩ := run_bind_eq_ok _ _ _ _ h
    rw [run_bind, hstep init x s s1 hx u, except_bind_ok]
    cases x with
    | done a' =>
      simp only at h ⊢
      rw [run_pure_eq_ok _ _ _ _ h]
      rfl
    | next b => exact ih b exhausted s1 s' a h u

/-- A step of the ancestor walk ignores the runner state. -/
theorem ancStep_run_transfer (store : Store map) (slot : EthCLSpecs.Heze.Slot)
    (n : ForkChoiceNode) (x : Step ForkChoiceNode ForkChoiceNode) (s s' : Store map)
    (h : (ancStep store slot n).run s = .ok (x, s')) (u : Store map) :
    (ancStep store slot n).run u = .ok (x, u) := by
  unfold ancStep at h ⊢
  cases hb : FcMap.lookup store.blocks n.root with
  | none =>
    simp only [FcMap.getOrThrow, FcMap.getOrThrowKey, hb] at h
    cases h
  | some b =>
    simp only [FcMap.getOrThrow, FcMap.getOrThrowKey, hb, pure_bind] at h ⊢
    split at h
    · rename_i hgt
      rw [if_pos hgt]
      obtain ⟨ps, s1, hps, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨pb, hpb⟩ := getParentPayloadStatus_run_parent store s s1 b ps hps
      rw [run_bind, getParentPayloadStatus_run_transfer store store b pb hpb hpb hps u,
        except_bind_ok, run_pure_eq_ok _ _ _ _ h]
      rfl
    · rename_i hle
      rw [if_neg hle, run_pure_eq_ok _ _ _ _ h]
      rfl

/-- A successful `liftErr` ignores the runner state. -/
theorem liftErr_run_transfer {σ ε' ε α : Type} [ErrorConv ε' ε] {x : Except ε' α} {s s' : σ}
    {a : α} (h : (liftErr (m := StateT σ (Except ε)) (E := ε') (F := ε) x).run s = .ok (a, s'))
    (u : σ) : (liftErr (m := StateT σ (Except ε)) (E := ε') (F := ε) x).run u = .ok (a, u) := by
  cases x with
  | error e =>
    rw [run_liftErr_of_error _ s rfl] at h
    cases h
  | ok y =>
    rw [run_liftErr_of_ok _ s rfl] at h
    cases h
    exact run_liftErr_of_ok _ u rfl

/-- **`getCheckpointBlock` ignores the runner state.** It reads only its store argument. The
checked start slot of the epoch keeps the state, and so does the walk. -/
theorem getCheckpointBlock_run_transfer (store : Store map) (root : Root)
    (e : EthCLSpecs.Heze.Epoch) {c : Root} {s s' : Store map}
    (h : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store root
      e).run s = .ok (c, s')) (u : Store map) :
    (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store root e).run u
      = .ok (c, u) := by
  simp only [getCheckpointBlock, getAncestor_eq_fuelLoop] at h ⊢
  obtain ⟨m, s1, hm, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨n, s2, hn, h⟩ := run_bind_eq_ok _ _ _ _ h
  rw [run_bind, liftErr_run_transfer hm u, except_bind_ok, run_bind,
    fuelLoop_run_transfer _ (ancStep_run_transfer store _) _ _ _ s1 s2 n hn u,
    except_bind_ok, run_pure_eq_ok _ _ _ _ h]
  rfl

/-- **At an epoch whose first slot is no earlier than the block, the checkpoint block is the
block itself.** The first slot `e * SLOTS_PER_EPOCH` fits in `uint64`, so the checked start
slot succeeds. The walk then stops at its first step. -/
theorem getCheckpointBlock_run_self (store : Store map) (root : Root) (b : BeaconBlock)
    (hb : FcMap.lookup store.blocks root = some b) (e : EthCLSpecs.Heze.Epoch)
    (hfit : e.toNat * slotsPerEpoch < 2 ^ 64)
    (hle : b.slot ≤ e * UInt64.ofNat slotsPerEpoch) (u : Store map) :
    (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store root e).run u
      = .ok (root, u) := by
  have hl : (liftErr (m := ForkChoiceStoreRun (Store map))
      (EthCLSpecs.Heze.computeStartSlotAtEpoch e :
        Except StateTransitionError EthCLSpecs.Heze.Slot)).run u
      = .ok (e * UInt64.ofNat slotsPerEpoch, u) :=
    run_liftErr_of_ok _ u (by rw [computeStartSlotAtEpoch_ok_of_lt hfit]; rfl)
  unfold getCheckpointBlock
  simp only [run_bind, hl, except_bind_ok, getAncestor_eq_fuelLoop, fuelLoop, ancStep,
    FcMap.getOrThrow, FcMap.getOrThrowKey, hb, ForkChoiceNode.pending, pure_bind, gt_iff_lt,
    UInt64.not_lt.mpr hle, if_false]
  rfl

/-- When `e * SLOTS_PER_EPOCH` does not fit in `uint64`, `compute_start_slot_at_epoch(e)`
raises. A product that wraps does not give back `SLOTS_PER_EPOCH` when divided by `e`. -/
theorem computeStartSlotAtEpoch_not_ok_of_ge {e : EthCLSpecs.Heze.Epoch}
    (h : 2 ^ 64 ≤ e.toNat * slotsPerEpoch) {s : EthCLSpecs.Heze.Slot} :
    (EthCLSpecs.Heze.computeStartSlotAtEpoch e : Except StateTransitionError EthCLSpecs.Heze.Slot)
      ≠ .ok s := by
  intro hs
  simp only [EthCLSpecs.Heze.computeStartSlotAtEpoch, checkedMul] at hs
  split at hs
  · simp [throwArithmetic, liftErr, Except.mapError, MonadExcept.ofExcept] at hs
  · rename_i hg
    have hn : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
      UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
    have hpos : e ≠ 0 := by
      intro he
      subst he
      simp at h
    have hrec : e * UInt64.ofNat slotsPerEpoch / e = UInt64.ofNat slotsPerEpoch :=
      Classical.byContradiction fun hne => hg (by simp [hpos, hne])
    have hrec' := congrArg UInt64.toNat hrec
    rw [UInt64.toNat_div, UInt64.toNat_mul, hn] at hrec'
    -- The wrapped product is below `2 ^ 64`, and its quotient by `e` is `SLOTS_PER_EPOCH`.
    have hlt : e.toNat * slotsPerEpoch % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have hdm := Nat.div_mul_le_self (e.toNat * slotsPerEpoch % 2 ^ 64) e.toNat
    rw [hrec', Nat.mul_comm] at hdm
    omega

/-- Every checkpoint block of `root` from epoch `E₁` on is later than `rb`. The block of
`root` is later than `rb`. Each epoch from `E₁` to the epoch after the block passes the walk
or raises. -/
def earlyB (st : Store map) (root : Root) (rb : BeaconBlock) (E₁ : Nat) : Bool :=
  match FcMap.lookup st.blocks root with
  | some hb =>
    decide (rb.slot < hb.slot) &&
    (List.range' E₁ (hb.slot.toNat / slotsPerEpoch + 2 - E₁)).all fun e =>
      match (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) st root
          (UInt64.ofNat e)).run st with
      | .ok (c, _) =>
        match FcMap.lookup st.blocks c with
        | some cb => decide (rb.slot < cb.slot)
        | none => false
      | .error _ => true
  | none => false

/-- **`earlyB` gives the conclusion of `FinalitySetting.early`.** The walk ignores the runner
state, so the check at the store covers every run. An epoch up to the one after the block is
in the range of the check. A later epoch whose first slot fits in `uint64` has the block
itself as its checkpoint block (`getCheckpointBlock_run_self`). At a later epoch whose first
slot does not fit, the start slot raises, and no run succeeds. -/
theorem early_of_check {st : Store map} {root : Root} {rb : BeaconBlock} {E₁ : Nat}
    (h : earlyB st root rb E₁ = true) {e : EthCLSpecs.Heze.Epoch} {c : Root} {u u' : Store map}
    (he : E₁ ≤ e.toNat)
    (hrun : (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) st root
      e).run u = .ok (c, u')) :
    ∃ cb, FcMap.lookup st.blocks c = some cb ∧ rb.slot < cb.slot := by
  unfold earlyB at h
  split at h
  · rename_i hb hlook
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hrb, hall⟩ := h
    have hst := getCheckpointBlock_run_transfer st root e hrun st
    by_cases hk : e.toNat ≤ hb.slot.toNat / slotsPerEpoch + 1
    · have hm : e.toNat ∈ List.range' E₁ (hb.slot.toNat / slotsPerEpoch + 2 - E₁) :=
        List.mem_range'_1.mpr ⟨he, by omega⟩
      have hchk := List.all_eq_true.mp hall _ hm
      rw [UInt64.ofNat_toNat, hst] at hchk
      simp only at hchk
      split at hchk
      · rename_i cb hcb
        exact ⟨cb, hcb, of_decide_eq_true hchk⟩
      · cases hchk
    · by_cases hfit : e.toNat * slotsPerEpoch < 2 ^ 64
      · have hle : hb.slot ≤ e * UInt64.ofNat slotsPerEpoch := by
          have hn : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
            UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_mul, hn, Nat.mod_eq_of_lt hfit]
          have h1 := Nat.lt_mul_div_succ hb.slot.toNat EthCLSpecs.Heze.Const.slotsPerEpochPos
          have h2 : slotsPerEpoch * (hb.slot.toNat / slotsPerEpoch + 1) ≤
              slotsPerEpoch * e.toNat := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_comm e.toNat]
          omega
        rw [getCheckpointBlock_run_self st root hb hlook e hfit hle u] at hrun
        injection hrun with hrun
        injection hrun with hc
        subst hc
        exact ⟨hb, hlook, hrb⟩
      · exfalso
        simp only [getCheckpointBlock] at hrun
        obtain ⟨m, s1, hm, -⟩ := run_bind_eq_ok _ _ _ _ hrun
        cases hx : (EthCLSpecs.Heze.computeStartSlotAtEpoch e :
            Except StateTransitionError EthCLSpecs.Heze.Slot) with
        | error err =>
          rw [hx] at hm
          cases hm
        | ok y => exact computeStartSlotAtEpoch_not_ok_of_ge (by omega) hx
  · cases h

end Transfer

/-! ## Head runs in one pass -/

section Pass
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The run of a trace in groups: the arrivals and the store after each group. One fold runs
every event once. -/
def passFrom : List (SignedInclusionList × UInt64) × Store map →
    List (List (TraceEvent × Nat)) →
    Option (List (List (SignedInclusionList × UInt64) × Store map))
  | _, [] => some []
  | acc, g :: gs =>
    match (g.map Prod.fst).foldlM traceStep acc with
    | .ok acc' => (passFrom acc' gs).map (acc' :: ·)
    | .error _ => none

omit [Config] [CryptoBackend] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability] in
/-- A fold over two lists in a row. -/
theorem foldlM_traceStep_append {α : Type} (f : α → TraceEvent → Except StoreTransitionError α)
    (l₁ l₂ : List TraceEvent) (acc : α) :
    (l₁ ++ l₂).foldlM f acc = (l₁.foldlM f acc) >>= fun x => l₂.foldlM f x :=
  List.foldlM_append

/-- **Record `i` of the pass is the run of the first `i + 1` groups.** -/
theorem passFrom_get :
    ∀ {groups : List (List (TraceEvent × Nat))}
      {acc : List (SignedInclusionList × UInt64) × Store map}
      {R : List (List (SignedInclusionList × UInt64) × Store map)},
      passFrom acc groups = some R → ∀ i r, R[i]? = some r →
        (((groups.take (i + 1)).flatten).map Prod.fst).foldlM traceStep acc = .ok r
  | [], acc, R, h, i, r, hr => by
    cases h
    simp at hr
  | g :: gs, acc, R, h, i, r, hr => by
    simp only [passFrom] at h
    split at h
    · rename_i acc' hg
      obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.mp h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
        subst hr
        simpa using hg
      | succ i =>
        simp only [List.getElem?_cons_succ] at hr
        have := passFrom_get hR' i r hr
        simp only [List.take_succ_cons, List.flatten_cons, List.map_append]
        rw [List.foldlM_append, hg]
        exact this
    · cases h

/-- Record `i` of the pass from the seed is the `runTrace` of the first `i + 1` groups. -/
theorem passFrom_runTrace {s0 : Store map} {groups : List (List (TraceEvent × Nat))}
    {R : List (List (SignedInclusionList × UInt64) × Store map)}
    (h : passFrom ([], s0) groups = some R) {i : Nat}
    {r : List (SignedInclusionList × UInt64) × Store map} (hr : R[i]? = some r) :
    runTrace s0 (((groups.take (i + 1)).flatten).map Prod.fst) = .ok r :=
  passFrom_get h i r hr

end Pass

/-! ## Head runs with any head -/

section Heads
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

open EthCLSpecs.Heze (ForkChoiceNode getHead getCurrentSlot)

/-- The node `x` is a member of `l`. The check compares the root and the payload status.
`node_eq_of_root_status` turns a match into equality. -/
def nodeIn (l : List ForkChoiceNode) (x : ForkChoiceNode) : Bool :=
  l.any fun m => decide (m.root = x.root) && decide (m.payloadStatus = x.payloadStatus)

omit [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- `nodeIn` is membership. -/
theorem nodeIn_iff {l : List ForkChoiceNode} {x : ForkChoiceNode} : nodeIn l x = true ↔ x ∈ l := by
  unfold nodeIn
  rw [List.any_eq_true]
  constructor
  · rintro ⟨m, hm, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [← node_eq_of_root_status m x h.1 h.2]
    exact hm
  · intro hx
    exact ⟨x, hx, by simp⟩

/-- The fields of `HeadRun.Base` that a computation decides, for any head: the wall time of the
prefix, the store time, the current slot, the `getHead` run, the walk from the head through
`pending r` within `fuel` steps, and the block at `r`. -/
def baseB (q : HeadRun map) (r : Root) (rb : BeaconBlock) (t fuel : Nat) : Bool :=
  q.events.all (fun y => decide (y.2 ≤ q.wall)) &&
  q.store.time.toNat == q.wall / 1000 &&
  (match (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      q.store).run q.store with
    | .ok (cs, _) => cs.toNat == t
    | .error _ => false) &&
  (match (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) q.store).run q.store with
    | .ok (h, _) => nodeIn [q.head] h
    | .error _ => false) &&
  nodeIn (ancestorsB q.store fuel q.head) (.pending r) &&
  !nodeIn [q.head] (.pending r) &&
  decide (FcMap.lookup q.store.blocks r = some rb)

/-- **`baseB` and the run of the prefix give `HeadRun.Base`.** The walk lists `pending r`, so
`pending r` is an ancestor of the head (`below_of_mem_ancestorsB`). -/
theorem HeadRun.Base.of_check {n : NodeRun map} {q : HeadRun map} {r : Root} {rb : BeaconBlock}
    {t fuel : Nat} (hpre : ∃ rest, n.events = q.events ++ rest)
    (hrun : runTrace n.seed (q.events.map Prod.fst) = .ok (q.arrivals, q.store))
    (h : baseB q r rb t fuel = true) : q.Base n r rb t := by
  simp only [baseB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hwall, htime⟩, hslot⟩, hhd⟩, hanc⟩, hne⟩, hblock⟩ := h
  refine ⟨hpre, NodeTrace.of_runTrace hrun, hwall, htime, ?_, ?_,
    ⟨below_of_mem_ancestorsB fuel q.head (nodeIn_iff.mp hanc), fun he => ?_⟩, hblock⟩
  · split at hslot
    · rename_i cs s' hcs
      have := getCurrentSlot_run_self _ _ _ _ hcs
      subst this
      exact ⟨cs, beq_iff_eq.mp hslot, hcs⟩
    · cases hslot
  · split at hhd
    · rename_i hd s' hh
      have hm := List.mem_singleton.mp (nodeIn_iff.mp hhd)
      exact ⟨s', hm ▸ hh⟩
    · cases hhd
  · have : nodeIn [q.head] (.pending r) = true :=
      nodeIn_iff.mpr (List.mem_singleton.mpr he.symm)
    rw [this] at hne
    cases hne

/-- The walk from `head` ends within `fuel` steps and does not list `x`. -/
def notBelowB (store : Store map) (fuel : Nat) (x head : ForkChoiceNode) : Bool :=
  walkDone store fuel head && !nodeIn (ancestorsB store fuel head) x

omit [CryptoBackend] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability] in
/-- **`notBelowB` rules out `x` below `head`.** A complete walk lists every ancestor
(`mem_ancestorsB_of_below`). -/
theorem not_below_of_check {store : Store map} {fuel : Nat} {x head : ForkChoiceNode}
    (h : notBelowB store fuel x head = true) : ¬ NodeBelow store x head := by
  simp only [notBelowB, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro hb
  have := nodeIn_iff.mpr (mem_ancestorsB_of_below hb fuel h.1)
  rw [this] at h
  cases h.2

end Heads

/-! ## Checks over the states of a chain -/

section ChainChecks
variable [Preset] [HasherTag] [Config] [CryptoBackend]

open EthCLSpecs.Heze (ValidatorIndex Epoch getAttestingIndices getBlockRoot computeEpochAtSlot
  IndexedAttestation getCheckpointBlock)
open EthCLSpecs.Heze.Const (slotsPerEpoch validatorRegistryLimit)

omit [Config] [CryptoBackend] in
/-- `RunTotals` compares numbers, so it is decidable. -/
instance (u : BeaconState) : Decidable (RunTotals u) := by
  unfold RunTotals
  infer_instance

/-- The adversarial stake of `u` over the registry indices of `u`. `advStake` sums over
`regVals`, a list of `2 ^ 40` indices, so a computation needs this form. -/
def advStakeB (u : BeaconState) (honestOf : ValidatorIndex → Bool) : Nat :=
  ((((List.range u.validators.val.size).map UInt64.ofNat).filter fun i => !honestOf i).map
    (linkStake u)).sum

omit [HasherTag] [Config] [CryptoBackend] in
/-- **A sum over `regVals` is a sum over the first `n` indices** when the weight is zero from
`n` on. -/
theorem stakeSum_regVals_filter (w : ValidatorIndex → Nat) (p : ValidatorIndex → Bool)
    {n : Nat} (h : n ≤ min validatorRegistryLimit (2 ^ 64))
    (hw : ∀ k, n ≤ k → k < 2 ^ 64 → w (UInt64.ofNat k) = 0) :
    EthCLLib.Proofs.FFG.stakeSum w (regVals.filter p) =
      ((((List.range n).map UInt64.ofNat).filter p).map w).sum := by
  unfold EthCLLib.Proofs.FFG.stakeSum regVals
  obtain ⟨m, hm⟩ : ∃ m, min validatorRegistryLimit (2 ^ 64) = n + m :=
    ⟨_, (Nat.add_sub_cancel' h).symm⟩
  rw [hm, List.range_add, List.map_append, List.filter_append, List.map_append, List.sum_append]
  have htail : (List.map w ((((List.range m).map (n + ·)).map UInt64.ofNat).filter p)).sum
      = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hi, -⟩ := List.mem_filter.mp hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    have hk' := List.mem_range.mp hk
    have := Nat.min_le_right validatorRegistryLimit (2 ^ 64)
    exact hw (n + k) (Nat.le_add_right _ _) (by omega)
  rw [htail, Nat.add_zero]

omit [Config] [CryptoBackend] in
/-- **`advStake` is `advStakeB`.** An index past the registry has no link stake. -/
theorem advStake_eq_advStakeB (u : BeaconState) (honestOf : ValidatorIndex → Bool)
    (h : u.validators.val.size ≤ min validatorRegistryLimit (2 ^ 64)) :
    advStake u honestOf = advStakeB u honestOf := by
  unfold advStake advStakeB
  refine stakeSum_regVals_filter _ _ h fun k hk hk64 => ?_
  have hnone : u.validators.val[k]? = none := Array.getElem?_eq_none hk
  unfold linkStake
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hk64, hnone]

omit [Config] [CryptoBackend] in
/-- The registry fits in `regVals`, as a decidable bound. -/
abbrev RegFits (u : BeaconState) : Prop :=
  u.validators.val.size ≤ min validatorRegistryLimit (2 ^ 64)

/-- **`StoreTotals` from the states of the chain.** -/
theorem StoreTotals.of_chain {map : MapKind} [FcMap map] {A : BeaconState} {a : BeaconBlock}
    {W : List ChainStep} {L : List BeaconState} {s : Store map} (hc : ChainStore A a W L s)
    (h : ∀ u ∈ L, RunTotals u) : StoreTotals A a s :=
  fun _ _ _ hsr hp => h _ (hc.state_mem hsr hp)

/-- **The stake bound of `allChains` from the states of the chain.** -/
theorem advStake_lt_of_chain {map : MapKind} [FcMap map] {A : BeaconState} {a : BeaconBlock}
    {W : List ChainStep} {L : List BeaconState} {s : Store map} (hc : ChainStore A a W L s)
    {honestOf : ValidatorIndex → Bool}
    (h : ∀ u ∈ L, RegFits u ∧ 3 * advStakeB u honestOf <
      2 * (totBal u).toNat)
    {p q : List ChainStep} (hsr : StoreRun A a s (p ++ q)) {u : BeaconState}
    (hp : ChainRun (2 ^ 64 - 1) p A u) :
    3 * advStake u honestOf < 2 * (totBal u).toNat := by
  obtain ⟨hfit, hlt⟩ := h u (hc.state_mem hsr hp)
  rw [advStake_eq_advStakeB u honestOf hfit]
  exact hlt

/-- **A vote placed on a store run is a vote of a block of the chain.** -/
theorem RunVote.data_mem {map : MapKind} [FcMap map] {A : BeaconState} {a : BeaconBlock}
    {W : List ChainStep} {L : List BeaconState} {s : Store map} (hc : ChainStore A a W L s)
    {steps : List ChainStep} (hsr : StoreRun A a s steps) {hi : Nat} {i : ValidatorIndex}
    {d : EthCLSpecs.Heze.AttestationData} (hv : RunVote hi A steps i d) :
    ∃ b ∈ blocksOf W, ∃ att ∈ b.body.attestations.toArray, att.data = d := by
  obtain ⟨j, hj⟩ := hc.blocks_take hsr
  obtain ⟨s₁, s₂, sb, v, -, -, -, att, hs, -, hatt, hd, -⟩ := hv
  have hm : sb.message ∈ blocksOf steps := by
    rw [hs, blocksOf_append]
    exact List.mem_append_right _ List.mem_cons_self
  rw [hj] at hm
  exact ⟨sb.message, List.mem_of_mem_take hm, att, hatt, hd⟩

/-- Every block step of `W` validates its result and names a nonzero state root. -/
def validatedB (W : List ChainStep) : Bool :=
  W.all fun x => match x with
    | .block sb v => v && decide (sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    | .slot => true

omit [HasherTag] [Config] [CryptoBackend] in
/-- `validatedB` gives `ValidatedSteps`. -/
theorem ValidatedSteps.of_check {W : List ChainStep} (h : validatedB W = true) :
    ValidatedSteps W := by
  intro sb v hm
  have := List.all_eq_true.mp h _ hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The root that `get_block_root` returns at `u`, when it succeeds. -/
def blockRootOf (u : BeaconState) (e : Epoch) : Option Root :=
  match runPure (getBlockRoot (StateTransition := HezeRun) (pureState u) e) u with
  | .ok (r, _) => some r
  | .error _ => none

omit [Config] [CryptoBackend] in
/-- `blockRootOf` names a run that keeps the state. -/
theorem blockRootOf_run {u : BeaconState} {e : Epoch} {r : Root} (h : blockRootOf u e = some r) :
    runPure (getBlockRoot (StateTransition := HezeRun) (pureState u) e) u = .ok (r, u) := by
  unfold blockRootOf at h
  split at h
  · rename_i r' u' hrun
    cases h
    have hk : u' = u := (getBlockRootAtSlot_run_ok (getBlockRoot_runPure_ok hrun)).2.2.2
    rw [hrun, hk]
  · cases h

/-- The validator `x` has a vote for epoch `e` in block `n` of `W`, with the pre-state `L[n]`:
the vote of a placed vote (`PlacedVote`). -/
def placedAtB (W : List ChainStep) (L : List BeaconState) (x : ValidatorIndex) (e : Epoch)
    (n : Nat) : Bool :=
  match W[n]?, L[n]? with
  | some (.block sb _), some u =>
    sb.message.body.attestations.toArray.any fun att =>
      att.data.target.epoch == e && computeEpochAtSlot att.data.slot == e &&
      (match getAttestingIndices (pureState u) att with
        | .ok idx => idx.contains x
        | .error _ => false) &&
      blockRootOf u e == some att.data.target.root &&
      decide (CommitteeWindow e (pureState u)) && decide (x.toNat < u.validators.val.size)
  | _, _ => false

/-- The validator `x` has a placed vote for epoch `e` in some block of `W`. -/
def placedB (W : List ChainStep) (L : List BeaconState) (x : ValidatorIndex) (e : Epoch) :
    Bool :=
  (List.range W.length).any (placedAtB W L x e)

/-- `placedB` gives `PlacedVote`. -/
theorem PlacedVote.of_check {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    (hL : runStates (2 ^ 64 - 1) W A = some L) {x : ValidatorIndex} {e : Epoch}
    (h : placedB W L x e = true) : PlacedVote (2 ^ 64 - 1) A W x e := by
  obtain ⟨n, hn, hat⟩ := List.any_eq_true.mp h
  have hn' := List.mem_range.mp hn
  unfold placedAtB at hat
  split at hat
  · rename_i sb v u hW hu
    obtain ⟨att, hatt, hcheck⟩ := Array.any_eq_true'.mp hat
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨⟨⟨he1, he2⟩, hidx⟩, hroot⟩, hcw⟩, hx⟩ := hcheck
    obtain ⟨u', hu', hrun⟩ := runStates_take hL n (Nat.le_of_lt hn')
    rw [hu] at hu'
    cases hu'
    split at hidx
    · rename_i idx hidx'
      have hsplit : W = W.take n ++ .block sb v :: W.drop (n + 1) := by
        conv => lhs; rw [← List.take_append_drop n W]
        rw [List.drop_eq_getElem_cons hn', show W[n] = .block sb v from
          Option.some.inj ((List.getElem?_eq_getElem hn').symm.trans hW)]
      exact ⟨W.take n, W.drop (n + 1), sb, v, u, att, idx, hsplit, hrun, hatt, he1, he2,
        hidx', Array.contains_iff_mem.mp hidx, blockRootOf_run hroot, hcw, hx⟩
    · cases hidx
  · cases hat

/-- A state that weighs one of the three epochs after `E₁`: the last slot of `E₁ + 1`,
`E₁ + 2`, or `E₁ + 3`. -/
def weighs (u : BeaconState) (E₁ : Nat) : Bool :=
  decide ((u.slot.toNat + 1) % slotsPerEpoch = 0) &&
    decide (E₁ + 1 ≤ u.slot.toNat / slotsPerEpoch) && decide (u.slot.toNat / slotsPerEpoch ≤ E₁ + 3)

/-- At each weigh state, each validator of `honestList` has a placed vote for the previous
epoch, and these validators hold two thirds of the total. -/
def honestChainB (W : List ChainStep) (L : List BeaconState) (honestOf : ValidatorIndex → Bool)
    (E₁ : Nat) : Bool :=
  L.all fun u => !weighs u E₁ ||
    (((honestList u honestOf (EthCLSpecs.Heze.previousEpochOf (pureState u))).all fun x =>
        placedB W L x (EthCLSpecs.Heze.previousEpochOf (pureState u))) &&
      decide (3 * honestStake u honestOf (EthCLSpecs.Heze.previousEpochOf (pureState u)) ≥
        2 * (totBal u).toNat))

/-- **`HonestChain` from checks over the states of `W`.** The run of `W` from `A` has the
states `L`. Each weigh state of the window passes `honestChainB`. Every state meets
`RunTotals`. The last state is in epoch `E₁ + 4`. -/
theorem HonestChain.of_check
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    {honestOf : ValidatorIndex → Bool} {E₁ : Nat} (hL : runStates (2 ^ 64 - 1) W A = some L)
    (hval : validatedB W = true) (hroots : AnchorRoots A) (hcps : AnchorCps A)
    (hord : StateCkptOrd A)
    (hsphr : 2 * slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot)
    (htot : ∀ u ∈ L, RunTotals u) (hlow : 1 ≤ E₁) (hstart : epochOf A ≤ E₁)
    (hend : (L[W.length]?).any (fun w => epochOf w == E₁ + 4) = true)
    (hchk : honestChainB W L honestOf E₁ = true) :
    ∃ st, HonestChain (2 ^ 64 - 1) W A st regVals honestOf E₁ := by
  obtain ⟨st, hst, hrun⟩ := runStates_take hL W.length (Nat.le_refl _)
  rw [List.take_length] at hrun
  rw [hst] at hend
  simp only [Option.any_some, beq_iff_eq] at hend
  -- A weigh state of the window is a state of `L`, and it passes the check.
  have hweigh : ∀ k, k < 3 → ∀ u, WeighAt (2 ^ 64 - 1) W A (E₁ + k + 1) u →
      weighs u E₁ = true ∧ u ∈ L := by
    intro k hk u ⟨s₁, s₂, hs, hu, hlast, hep⟩
    refine ⟨?_, runStates_mem hL hs hu⟩
    simp only [weighs, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hpass : ∀ k, k < 3 → ∀ u, WeighAt (2 ^ 64 - 1) W A (E₁ + k + 1) u →
      (honestList u honestOf (EthCLSpecs.Heze.previousEpochOf (pureState u))).all
          (fun x => placedB W L x (EthCLSpecs.Heze.previousEpochOf (pureState u))) = true ∧
        3 * honestStake u honestOf (EthCLSpecs.Heze.previousEpochOf (pureState u)) ≥
          2 * (totBal u).toNat := by
    intro k hk u hu
    obtain ⟨hw', hm⟩ := hweigh k hk u hu
    have := List.all_eq_true.mp hchk u hm
    rw [hw', Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  refine ⟨st, ⟨⟨hw, Nat.le_refl _, hrun, ValidatedSteps.of_check hval, hroots, hcps, hord, hsphr,
      fun s₁ s₂ u hs hu => htot u (runStates_mem hL hs hu), regVals_nodup,
      fun _ _ u _ _ i hi => mem_regVals u hi⟩, hlow, hstart, hend, ?_, ?_⟩⟩
  · intro k hk u hu x hx
    exact PlacedVote.of_check hL (List.all_eq_true.mp (hpass k hk u hu).1 x hx)
  · intro k hk u hu
    exact (hpass k hk u hu).2

/-- Each vote of a block of `W` with a slot in `[lo, hi)` targets the checkpoint block of the
head run of its slot. `runAt` gives the head run of a slot at the node of the voter. -/
def honestVotesB {map : MapKind} [FcMap map] (W : List ChainStep) (runAt : Nat → HeadRun map)
    (lo hi : Nat) : Bool :=
  (blocksOf W).all fun b => b.body.attestations.toArray.all fun att =>
    !(decide (lo ≤ att.data.slot.toNat) && decide (att.data.slot.toNat < hi)) ||
      match (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
          (runAt att.data.slot.toNat).store (runAt att.data.slot.toNat).head.root
          att.data.target.epoch).run (runAt att.data.slot.toNat).store with
      | .ok (c, _) => c == att.data.target.root
      | .error _ => false

/-- **`honestVotesB` gives the conclusion of `FinalitySetting.honestVotes`.** A vote placed on
a store run is a vote of a block of `W` (`RunVote.data_mem`), and the check covers it. -/
theorem honestVotes_of_check {map : MapKind} [FcMap map] {A : BeaconState} {a : BeaconBlock}
    {W : List ChainStep} {L : List BeaconState} {s : Store map} (hc : ChainStore A a W L s)
    {runAt : Nat → HeadRun map} {lo hi : Nat} (h : honestVotesB W runAt lo hi = true)
    {steps : List ChainStep} (hsr : StoreRun A a s steps) {hi' : Nat} {i : ValidatorIndex}
    {d : EthCLSpecs.Heze.AttestationData} (hv : RunVote hi' A steps i d)
    (hlo : lo ≤ d.slot.toNat) (hhi : d.slot.toNat < hi) :
    ∃ u u', (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      (runAt d.slot.toNat).store (runAt d.slot.toNat).head.root d.target.epoch).run u
        = .ok (d.target.root, u') := by
  obtain ⟨b, hb, att, hatt, rfl⟩ := RunVote.data_mem hc hsr hv
  have hchk := Array.all_eq_true'.mp (List.all_eq_true.mp h b hb) att hatt
  simp only [hlo, hhi, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at hchk
  split at hchk
  · rename_i c s' hrun
    rw [beq_iff_eq] at hchk
    exact ⟨_, _, hrun.trans (by rw [hchk])⟩
  · cases hchk

/-- The list of `runStates` has one state more than the steps. -/
theorem runStates_length {hi : Nat} :
    ∀ {W : List ChainStep} {A : BeaconState} {L : List BeaconState},
      runStates hi W A = some L → L.length = W.length + 1
  | [], A, L, h => by
    cases h
    rfl
  | x :: rest, A, L, h => by
    simp only [runStates] at h
    split at h
    · obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [runStates_length hL']
    · cases h

/-- A state of `runStates` is a state on the run. -/
theorem OnRun.of_mem {hi : Nat} {W : List ChainStep} {A : BeaconState} {L : List BeaconState}
    (hL : runStates hi W A = some L) {u : BeaconState} (hu : u ∈ L) : OnRun hi A W u := by
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hu
  have hlen := runStates_length hL
  obtain ⟨u', hu', hrun⟩ := runStates_take hL n (by omega)
  rw [List.getElem?_eq_getElem hn] at hu'
  obtain rfl := Option.some.inj hu'
  exact ⟨W.take n, W.drop n, (List.take_append_drop n W).symm, hrun⟩

/-- The indexed attestation is valid on a state of `L`. A validity read that faults counts as
not valid. -/
def validOnB (L : List BeaconState) (ia : IndexedAttestation) : Bool :=
  L.any fun u => match EthCLSpecs.Heze.isValidIndexedAttestation (pureState u) ia with
    | .ok b => b
    | .error _ => false

/-- `validOnB` over the states of a run gives `ValidOn` on the run. -/
theorem ValidOn.of_check {hi : Nat} {W : List ChainStep} {A : BeaconState}
    {L : List BeaconState} (hL : runStates hi W A = some L) {ia : IndexedAttestation}
    (h : validOnB L ia = true) : ValidOn (OnRun hi A W) ia := by
  obtain ⟨u, hu, hv⟩ := List.any_eq_true.mp h
  refine ⟨u, OnRun.of_mem hL hu, ?_⟩
  revert hv
  cases EthCLSpecs.Heze.isValidIndexedAttestation (pureState u) ia with
  | ok b => intro hv; cases hv; rfl
  | error e => intro hv; cases hv

/-- The stake of `st₀` of the validators in both attestations of a pair, over the registry
indices of `st₀`. `commonOf` filters `regVals`, so a computation needs this form. -/
def commonStakeB (st₀ : BeaconState) (pairs : List (IndexedAttestation × IndexedAttestation)) :
    Nat :=
  ((((List.range st₀.validators.val.size).map UInt64.ofNat).filter fun v => pairs.any fun p =>
    p.1.attestingIndices.toArray.contains v && p.2.attestingIndices.toArray.contains v).map
      (activeOf st₀)).sum

omit [Config] [CryptoBackend] in
/-- **`activeStake` of `commonOf` is `commonStakeB`.** An index past the registry is not
active. -/
theorem activeStake_commonOf (st₀ : BeaconState)
    (pairs : List (IndexedAttestation × IndexedAttestation)) (h : RegFits st₀) :
    activeStake st₀ (commonOf pairs) = commonStakeB st₀ pairs := by
  unfold activeStake commonOf commonStakeB
  refine stakeSum_regVals_filter _ _ h fun k hk hk64 => ?_
  have hnone : st₀.validators.val[k]? = none := Array.getElem?_eq_none hk
  simp [activeOf, acB, Nat.mod_eq_of_lt hk64, hnone]

/-- The check of `SlashingEvidence` over the states `L₁` and `L₂` of two runs. -/
def slashingB (st₀ : BeaconState) (L₁ L₂ : List BeaconState) (d₁ d₂ : Nat)
    (pairs : List (IndexedAttestation × IndexedAttestation)) : Bool :=
  decide (RegFits st₀) &&
  pairs.all (fun p => EthCLSpecs.Heze.isSlashableAttestationData p.1.data p.2.data) &&
  pairs.all (fun p => (validOnB L₁ p.1 && validOnB L₂ p.2) ||
    (validOnB L₂ p.1 && validOnB L₁ p.2)) &&
  decide (3 * commonStakeB st₀ pairs + 5 * (d₁ + d₂) ≥ totalOf st₀)

/-- **`SlashingEvidence` from a check over the states of two runs.** -/
theorem SlashingEvidence.of_check {hi : Nat} {A st₀ : BeaconState} {W₁ W₂ : List ChainStep}
    {L₁ L₂ : List BeaconState} (h₁ : runStates hi W₁ A = some L₁)
    (h₂ : runStates hi W₂ A = some L₂) {d₁ d₂ : Nat}
    {pairs : List (IndexedAttestation × IndexedAttestation)}
    (h : slashingB st₀ L₁ L₂ d₁ d₂ pairs = true) :
    SlashingEvidence st₀ (OnRun hi A W₁) (OnRun hi A W₂) d₁ d₂ pairs := by
  simp only [slashingB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hfit, hs⟩, hv⟩, hst⟩ := h
  refine ⟨fun p hp => List.all_eq_true.mp hs p hp, fun p hp => ?_, ?_⟩
  · have hp' := List.all_eq_true.mp hv p hp
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hp'
    rcases hp' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact .inl ⟨ValidOn.of_check h₁ ha, ValidOn.of_check h₂ hb⟩
    · exact .inr ⟨ValidOn.of_check h₂ ha, ValidOn.of_check h₁ hb⟩
  · rw [activeStake_commonOf st₀ pairs hfit]
    exact hst

end ChainChecks

end EthCLSpecs.Proofs.Heze
