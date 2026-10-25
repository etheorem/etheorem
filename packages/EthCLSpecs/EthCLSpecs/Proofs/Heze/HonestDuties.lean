import EthCLSpecs.Proofs.Heze.HonestHead
import EthCLSpecs.Proofs.Heze.ParentPayloadEmpty

/-!
# `EthCLSpecs.Proofs.Heze.HonestDuties`: honest duties in slot `n + 1` avoid a failed payload

`HonestHead.lean` proves that the head of an honest node in slot `n + 1` is not the FULL
node of the block root `r` of slot `n`, and not below it. This module follows the head into
the two duties of slot `n + 1` (`consensus-specs/specs/gloas/validator.md`).

## The attester

An attester votes for `data.beacon_block_root = head.root`, and it signals the payload
status of that block in `data.index` (`validator.md:104-111`). The index is `0` for a block
of the current slot. Otherwise it is `1` for a FULL head and `0` for an EMPTY head.
`honestAttestationIndex` states the rule. The spec has no Python function for it.
`honestAttestation_ne_full` proves that no honest vote is `(r, 1)`.

## The proposer

The proposer builds on its head (`validator.md:186-217, 240-251`). The spec lets a proposer
with proposer re-orgs enabled build on `get_proposer_head(store, head, slot)` instead
(`validator.md:186-188`). `HonestProposal` covers only a proposer that builds on the
`getHead` head. It states the three rules that matter here:

- The parent root of the block is the root of the head.
- When `should_build_on_full` holds, the bid's `parentBlockHash` is the `blockHash` of the
  latest bid of the proposer's state. Otherwise it is the `parentBlockHash` of that bid.
- When `should_build_on_full` holds, the `parentExecutionRequests` are those of the head's
  payload. Otherwise they are empty.

`shouldBuildOnFull` is the fork-body port of `should_build_on_full`. It rejects a pending
head (`shouldBuildOnFull_run_ne_pending`) and answers `false` at an EMPTY head
(`shouldBuildOnFull_run_empty`). So when the head root is `r`, the head is the EMPTY node of
`r`, and the block takes the EMPTY edge. `honestProposal_empty_of_root` proves two facts
about such a block:

- `processParentExecutionPayload` leaves the proposer's state as it was. So the block
  settles no builder payment (`processParentExecutionPayload_run_of_empty_parent`).
- Fork choice puts the block on the EMPTY edge of `r` in any store that holds the block at
  `r` with the same bid (`getParentPayloadStatus_run_eq_empty_iff`).

Both facts need the latest bid of the state to have different block and parent hashes. The
second also needs the bid of the block at `r` to be the latest bid of the state. Both are
hypotheses. `process_execution_payload_bid` writes the block's bid into the state, so a
proof of the second runs through the state transition of `onBlock`.

When the head root is not `r`, the block's parent root is not `r`, and the block does not
extend `r` at all.

## The network

`honestNodes_duties_avoid_full` states the result for every honest node of a network,
with the hypotheses of `honestNode_head_avoids_full` at each one.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind run_pure run_bind_eq_ok run_pure_eq_ok
  run_assert_bind_eq_ok LawfulFcMap LawfulInclusionList pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState Root Slot ForkChoiceNode BeaconBlock
  InclusionList SignedInclusionList SignedExecutionPayloadEnvelope ExecutionPayload
  ExecutionRequests Transaction ValidatorIndex getHead getParentPayloadStatus
  processParentExecutionPayload shouldBuildOnFull)
open EthCLSpecs.Heze.Const (payloadStatusPending payloadStatusEmpty payloadStatusFull)

section Build
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- A successful `shouldBuildOnFull` run passed its opening assert: the head is not a
pending node. -/
theorem shouldBuildOnFull_run_ne_pending (store s s' : Store map) (head : ForkChoiceNode)
    (b : Bool)
    (h : (shouldBuildOnFull (StoreTransition := ForkChoiceStoreRun (Store map)) store head).run s
      = .ok (b, s')) :
    head.payloadStatus ≠ payloadStatusPending := by
  unfold shouldBuildOnFull at h
  obtain ⟨hne, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  simpa using hne

/-- `shouldBuildOnFull` answers `false` at an EMPTY head. A head from an earlier slot
follows its own status, which is not FULL. A head from the previous slot takes the EMPTY
branch. -/
theorem shouldBuildOnFull_run_empty (store s s' : Store map) (head : ForkChoiceNode)
    (b : Bool) (hempty : head.payloadStatus = payloadStatusEmpty)
    (h : (shouldBuildOnFull (StoreTransition := ForkChoiceStoreRun (Store map)) store head).run s
      = .ok (b, s')) :
    b = false := by
  unfold shouldBuildOnFull at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  rw [hempty] at h
  split at h
  · have hb := run_pure_eq_ok _ _ _ _ h
    rw [hb]
    decide
  · simp only [beq_self_eq_true, ite_true] at h
    exact run_pure_eq_ok _ _ _ _ h

end Build

section Duties
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- The index of an honest attestation (`validator.md:104-111`). `headSlot` is the slot of
the head block, and `currentSlot` the slot of the attestation. A head block of the current
slot gets `0`. Otherwise a FULL head gets `1`, and an EMPTY head `0`. The spec defines no
index for a pending head. The rule gives it `0`. -/
def honestAttestationIndex (head : ForkChoiceNode) (headSlot currentSlot : Slot) : UInt64 :=
  if headSlot == currentSlot then 0
  else if head.payloadStatus == payloadStatusFull then 1 else 0

omit [Config] in
/-- An honest vote is never `(r, 1)` when the head avoids the FULL node of `r`. The index
`1` needs a FULL head, and a FULL head at `r` is the FULL node of `r`. -/
theorem honestAttestation_ne_full (store : Store map) (r : Root) (head : ForkChoiceNode)
    (havoid : ¬ NodeBelow store (.full r) head) (headSlot currentSlot : Slot) :
    ¬ (head.root = r ∧ honestAttestationIndex head headSlot currentSlot = 1) := by
  rintro ⟨hroot, hindex⟩
  unfold honestAttestationIndex at hindex
  split at hindex
  · exact absurd hindex (by decide)
  · split at hindex
    · rename_i hfull
      have : head = .full r := node_eq_of_root_status _ _ hroot (beq_iff_eq.mp hfull)
      exact havoid (this ▸ NodeBelow.refl)
    · exact absurd hindex (by decide)

/-- The duty of an honest proposer that builds `block` on `head`, from the state `state`
(`validator.md:186-217, 240-251`). The parent root is the head root. A successful
`shouldBuildOnFull` run decides the bid's `parentBlockHash` and the
`parentExecutionRequests`. A proposer that builds on `get_proposer_head` after a re-org
(`validator.md:186-188`) is outside this structure. -/
structure HonestProposal (store : Store map) (head : ForkChoiceNode) (state : BeaconState)
    (block : BeaconBlock) : Prop where
  /-- The block builds on the head root. -/
  parent : block.parentRoot = head.root
  /-- `should_build_on_full` decides the parent hash and the parent requests. -/
  build : ∃ (full : Bool) (s s' : Store map),
    (shouldBuildOnFull (StoreTransition := ForkChoiceStoreRun (Store map)) store head).run s
      = .ok (full, s') ∧
    block.body.signedExecutionPayloadBid.message.parentBlockHash
      = (if full then state.latestExecutionPayloadBid.blockHash
          else state.latestExecutionPayloadBid.parentBlockHash) ∧
    (full = true → ∃ env : EthCLSpecs.Heze.ExecutionPayloadEnvelope,
      FcMap.lookup store.payloads head.root = some env ∧
      block.body.parentExecutionRequests = env.executionRequests) ∧
    (full = false → block.body.parentExecutionRequests = default)

variable [CryptoBackend]

/-- An honest block on a head at root `r` that avoids the FULL node of `r` takes the EMPTY
edge of `r`. The head has one of the three statuses (`getHead_run_status`).
`shouldBuildOnFull` rejects a pending head, and the head is not the FULL node of `r`. So
it is the EMPTY node, and `shouldBuildOnFull` answers `false`. Then:

- `processParentExecutionPayload` returns the proposer's state unchanged. So the block
  settles no builder payment.
- Take a store that holds the block `rb` at `r`, with the latest bid of the state as its
  bid. Fork choice puts the block on the EMPTY edge of `r` in that store.

The theorem assumes that the latest bid of the state has different block and parent
hashes. -/
theorem honestProposal_empty_of_root (store : Store map) (r : Root) (head : ForkChoiceNode)
    (havoid : ¬ NodeBelow store (.full r) head) (hstatus : ValidStatus head)
    (hroot : head.root = r) (state : BeaconState) (block : BeaconBlock)
    (hprop : HonestProposal store head state block)
    (hdistinct : state.latestExecutionPayloadBid.parentBlockHash
      ≠ state.latestExecutionPayloadBid.blockHash) :
    head = .empty r ∧
    (processParentExecutionPayload (StateTransition := HezeRun) block).run (pureState state)
      = .ok ((), pureState state) ∧
    ∀ (store' : Store map) (rb : BeaconBlock), FcMap.lookup store'.blocks r = some rb →
      rb.body.signedExecutionPayloadBid.message = state.latestExecutionPayloadBid →
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
          store' block).run store'
        = .ok (payloadStatusEmpty, store') := by
  obtain ⟨full, s, s', hbuild, hhash, -, hempty⟩ := hprop.build
  -- The head is the EMPTY node of `r`.
  have hnp := shouldBuildOnFull_run_ne_pending store s s' head full hbuild
  have hnf : head.payloadStatus ≠ payloadStatusFull := by
    intro hf
    exact havoid (node_eq_of_root_status head (.full r) hroot hf ▸ NodeBelow.refl)
  have he : head.payloadStatus = payloadStatusEmpty := by
    rcases hstatus with h | h | h
    · exact absurd h hnp
    · exact h
    · exact absurd h hnf
  have hhead : head = .empty r := node_eq_of_root_status head (.empty r) hroot he
  -- `shouldBuildOnFull` answers `false`, so the block takes the parent hash of the bid.
  have hfalse := shouldBuildOnFull_run_empty store s s' head full he hbuild
  subst hfalse
  simp only [Bool.false_eq_true, ite_false] at hhash
  have hne : block.body.signedExecutionPayloadBid.message.parentBlockHash
      ≠ state.latestExecutionPayloadBid.blockHash := hhash ▸ hdistinct
  refine ⟨hhead, ?_, ?_⟩
  · exact processParentExecutionPayload_run_of_empty_parent state block hne
      (congrArg htr (hempty rfl))
  · intro store' rb hrb hbid
    have hparent : FcMap.lookup store'.blocks block.parentRoot = some rb := by
      rw [hprop.parent, hroot]
      exact hrb
    exact (getParentPayloadStatus_run_eq_empty_iff store' block rb hparent).mpr (hbid ▸ hne)

/-- An honest block on a head that avoids the FULL node of `r` does not extend the payload
of `r`. Either its parent root is not `r`, or its head is the EMPTY node of `r` and
`processParentExecutionPayload` returns the state unchanged, as in
`honestProposal_empty_of_root`. -/
theorem honestProposal_avoids_full (store : Store map) (r : Root) (head : ForkChoiceNode)
    (havoid : ¬ NodeBelow store (.full r) head) (hstatus : ValidStatus head)
    (state : BeaconState) (block : BeaconBlock) (hprop : HonestProposal store head state block)
    (hdistinct : state.latestExecutionPayloadBid.parentBlockHash
      ≠ state.latestExecutionPayloadBid.blockHash) :
    block.parentRoot ≠ r ∨
      (head = .empty r ∧
        (processParentExecutionPayload (StateTransition := HezeRun) block).run (pureState state)
          = .ok ((), pureState state)) := by
  by_cases hroot : head.root = r
  · have h := honestProposal_empty_of_root store r head havoid hstatus hroot state block hprop
      hdistinct
    exact Or.inr ⟨h.1, h.2.1⟩
  · exact Or.inl (hprop.parent ▸ hroot)

end Duties

section Network
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability]

open EthCLSpecs.Heze.Const (slotDurationMs)

/-- The hypotheses of `honestNode_head_avoids_full` at one node, other than the ones that
all nodes share. The node runs the clocked trace `tevs` from the seed `s0`, with the anchor
block `a`. -/
structure HonestView (s0 s : Store map) (tevs : List (TraceEvent × Nat))
    (arrivals : List (SignedInclusionList × UInt64)) (r : Root) (n : Slot)
    (committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize)
    (il : InclusionList) (tSend Δ : Nat) (txs : ExecutionPayload → Array Transaction)
    (isValidOmission : ExecutionPayload → Transaction → Prop) (tx : Transaction)
    (a : BeaconBlock) : Prop where
  /-- The node ticks to its wall clock before each message. -/
  clocked : ClockedTrace s0 tevs arrivals s
  /-- The seed has the empty IL store. -/
  seedIl : s0.inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty
  /-- The stores agree on the block at `r` and on the committee. -/
  root : RootFacts s0 tevs r n committee
  /-- The seed holds no answer at `r`. -/
  answer0 : FcMap.lookup s0.payloadInclusionListSatisfaction r = none
  /-- The seed holds no payload at `r`. -/
  payload0 : FcMap.lookup s0.payloads r = none
  /-- The honest list reaches the node. -/
  list : HonestList tevs il tSend Δ
  /-- Every envelope for `r` at the node omits `tx`, with no valid omission. -/
  omits : ∀ (signedEnv : SignedExecutionPayloadEnvelope) (w : Nat),
    (.handler (.envelope signedEnv), w) ∈ tevs → signedEnv.message.beaconBlockRoot = r →
    tx ∉ txs signedEnv.message.payload ∧ ¬ isValidOmission signedEnv.message.payload tx
  /-- The seed meets the slot invariant for the anchor block. -/
  slotInv0 : SlotInv a s0
  /-- No event is a block at the parent root of the anchor. -/
  noAnchorParent : ∀ (e : HandlerEvent) (w : Nat), (.handler e, w) ∈ tevs →
    e.NotAtAnchorParent a

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- The network form. Each node `v` has a clocked trace `tevs v` from the seed `s0 v`, and
the honest nodes share the genesis time `g`. At every honest node, `HonestView` holds. Take
a store `m` of an honest trace in slot `n + 1`, with a justified block of slot at most `n`,
and the head that `getHead` returns on it. Then a root collision exists, or:

- The head avoids the FULL node of `r` and every node below it.
- No honest vote on the head is `(r, 1)`.
- Take an honest block on the head, from a state whose latest bid has different block and
  parent hashes. Its parent root is not `r`. Or the head is the EMPTY node of `r`, and
  `processParentExecutionPayload` leaves the state unchanged, so the block settles no
  builder payment.

The theorem assumes nothing about the other nodes. -/
theorem honestNodes_duties_avoid_full {Node : Type} (honest : Node → Prop)
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    (s0 s : Node → Store map) (tevs : Node → List (TraceEvent × Nat))
    (arrivals : Node → List (SignedInclusionList × UInt64)) (anchor : Node → BeaconBlock)
    {g : UInt64} (hgenesis : ∀ v, honest v → (s0 v).genesisTime = g)
    {r : Root} {n : Slot}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {il : InclusionList} {tSend Δ : Nat} {tx : Transaction}
    (hview : ∀ v, honest v → HonestView (s0 v) (s v) (tevs v) (arrivals v) r n committee il
      tSend Δ txs isValidOmission tx (anchor v))
    (hkey : il.inclusionListCommitteeRoot = htr committee)
    (hlo : slotStartMs g (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs g (n - 1).toNat + ilDueMs.toNat)
    (hsec : (tSend + Δ) / 1000 ≤ maxMsSeconds)
    (hDdiv : 1000 ∣ slotDurationMs.toNat)
    (hdue : ilDueMs.toNat ≤ slotDurationMs.toNat)
    (htx : tx ∈ il.transactions.toArray) (hnext : n.toNat + 1 < 2 ^ 64) :
    ∀ v, honest v →
      ∀ (pre rest : List (TraceEvent × Nat)), tevs v = pre ++ rest →
      ∀ (arr : List (SignedInclusionList × UInt64)) (m : Store map),
        NodeTrace (s0 v) (pre.map Prod.fst) arr m →
      ∀ w : Nat, m.time.toNat = w / 1000 → slotStartMs g (n.toNat + 1) ≤ w →
        w < slotStartMs g (n.toNat + 1 + 1) → w / 1000 ≤ maxMsSeconds →
      ∀ jb : BeaconBlock, FcMap.lookup m.blocks m.justifiedCheckpoint.root = some jb →
        jb.slot ≤ n →
      ∀ (runnerStore s' : Store map) (head : ForkChoiceNode),
        (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) m).run runnerStore
          = .ok (head, s') →
      RootCollision ∨
        (¬ NodeBelow m (.full r) head ∧
          (∀ headSlot currentSlot : Slot,
            ¬ (head.root = r ∧ honestAttestationIndex head headSlot currentSlot = 1)) ∧
          ∀ (state : BeaconState) (block : BeaconBlock), HonestProposal m head state block →
            state.latestExecutionPayloadBid.parentBlockHash
              ≠ state.latestExecutionPayloadBid.blockHash →
            block.parentRoot ≠ r ∨
              (head = .empty r ∧
                (processParentExecutionPayload (StateTransition := HezeRun) block).run
                    (pureState state)
                  = .ok ((), pureState state))) := by
  intro v hv pre rest hsplit arr m hm w htime hwlo hwhi hwsec jb hj hjslot runnerStore s' head
    hrun
  have hvw := hview v hv
  have hg := hgenesis v hv
  rcases honestNode_head_avoids_full hw hel hvw.clocked hvw.seedIl hvw.root hvw.answer0
      hvw.payload0 hvw.list hkey (hg ▸ hlo) (hg ▸ hhi) hsec hDdiv hdue htx hvw.omits
      hvw.slotInv0 hvw.noAnchorParent pre rest hsplit hm htime (hg ▸ hwlo) (hg ▸ hwhi) hwsec
      hnext hj hjslot runnerStore s' head hrun with havoid | hcol
  · have hstatus := getHead_run_status m runnerStore s' head hrun
    refine Or.inr ⟨havoid, fun hs cs => honestAttestation_ne_full m r head havoid hs cs, ?_⟩
    intro state block hprop hdistinct
    exact honestProposal_avoids_full m r head havoid hstatus state block hprop hdistinct
  · exact Or.inl hcol

end Network

end EthCLSpecs.Proofs.Heze
