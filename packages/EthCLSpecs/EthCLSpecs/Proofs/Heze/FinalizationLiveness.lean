import EthCLSpecs.Proofs.Heze.StoreFinality
import EthCLSpecs.Proofs.Heze.HonestVoter
import EthCLSpecs.Proofs.Heze.EmptyTarget
import EthCLSpecs.Proofs.Heze.RaceLong
import EthCLSpecs.Proofs.Heze.StoreClock
import EthCLSpecs.Proofs.Heze.FinLag

/-!
# `EthCLSpecs.Proofs.Heze.FinalizationLiveness`: the censored payload stays off the honest heads

Take the block `rb` at `r`, of slot `N`, whose payload the adversary wants. The window runs
from `N + 1` to the first slot of epoch `E₁ + 4`.

## The window

The heads of the first slot avoid `full r` (`FirstSlotAvoids`). The theorems here take that as a
premise. `FinalitySetting.first_of_decision` (`ViableHonest.lean`) proves it from the honest
inclusion list and the envelopes that omit its transaction. Each honest head run of a later slot
takes one of two cases.

- The justified block of the store is no later than `rb`. The race step of
  `race_empty_persists_long` applies at that slot.
- The justified block is past `rb`. The justified checkpoint is justified on the chain of a
  run from the anchor. It is past the base, so a link reaches it. The link voters hold two
  thirds of the stake. The adversary holds less than two thirds (`FinalitySetting.allChains`),
  so an honest validator voted for the checkpoint. The target of an honest vote is the
  checkpoint block of the voter's head at an earlier slot (`FinalitySetting.honestVotes`).
  That head is below `empty r`, and the target is past `rb`, so the target is below
  `empty r` too. The head of the store is below its justified block.

## The end of the window

At the first slot of `E₁ + 4`, every honest store has finalized `E₁` or later
(`honestStore_finalizes`), from the honest chain of `FinalityChain`. The finalized checkpoint is
justified on a chain, so the argument of the window puts it on the EMPTY side. Its root is not
`r` (`FinRootNe`), so as an honest target of an epoch from `E₁` it is past `rb`
(`EarlyTargets`). Later heads of the node take the finality lock
(`honestNode_finality_lock`). The conflict case of the lock gives slashing evidence
(`honestNodes_accountable`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure LawfulFcMap)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex SignedBeaconBlock SignedInclusionList AttestationData IndexedAttestation
  ExecutionPayload Transaction ExecutionRequests getHead getCheckpointBlock Epoch State Slot
  Attestation LatestMessage Gwei getBeaconCommittee storeTargetCheckpointState
  getCommitteeIndices committeeCountOf computeEpochAtSlot activeValidatorIndicesOf
  currentEpochOf getSupportedNode)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotDurationMs)
open EthCLSpecs.Proofs.Heze.PayloadRace (votedIn honestVoted advVoted votedIn_iff)

/-! ## The setting -/

section Setting
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The first slot of epoch `E₁ + 4`: the end of the window. -/
def finSlot (E₁ : Nat) : Nat := (E₁ + 4) * slotsPerEpoch

/-- The first slot from which a message can support the node `y`: the slot of its block for a
pending node, the slot after it for a payload node (`get_supported_node`,
`gloas/fork-choice.md:436`). A node with no block at its root gives `0`. -/
def supSlot (store : Store map) (y : ForkChoiceNode) : Nat :=
  match FcMap.lookup store.blocks y.root with
  | some b => b.slot.toNat +
      (if y.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending then 0 else 1)
  | none => 0

/-- The supported node of an honest message of slot `t` on the head `h`, whose block has the
slot `hs`. A block from `t` gives the pending node of the head root. An older block gives the
FULL node of a FULL head, and the EMPTY node of any other head: `honestAttestationIndex` sets the
payload flag only on a FULL head (`get_supported_node`, `gloas/validator.md:100-111`). -/
def honestSupported (h : ForkChoiceNode) (hs t : Nat) : ForkChoiceNode :=
  if hs < t then
    (if h.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusFull then .full h.root
      else .empty h.root)
  else .pending h.root

/-- The count at a fork of the path, at slot `s`. The honest balance with a vote in `[hlo, s)` is
more than the adversarial balance with a vote in `[alo, s)`, plus the proposer score of `jst`.
`RaceCount` is the case `hlo = alo`. -/
noncomputable abbrev ForkCount (jst : BeaconState) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) (hlo alo s : Nat) : Prop :=
  advVoted (raceVs jst honestOf committees) alo s + proposerScoreOf (pureState jst)
    < honestVoted (raceVs jst honestOf committees) hlo s

/-- The duties of `RaceSetting.Fields` for the votes of the slots `[lo, raceLo rb)` before the
window. They hold on the head runs of the window from its first slot. The duties are the
committees of the target states, honest data, delivery, and no slashing of an honest
validator. -/
structure EarlyDuties {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (rb : BeaconBlock) (lo hi : Nat)
    (nodeOf : ValidatorIndex → Node) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) : Prop where
  /-- `RaceSetting.Fields.committee` for the votes of `[lo, raceLo rb)`. -/
  committee : ∀ v, honest v → ∀ s, raceLo rb ≤ s → s ≤ hi → ∀ att mid,
    AttEventAt (node v).seed ((run v s).events.map Prod.fst) att mid →
    lo ≤ att.data.slot.toNat → att.data.slot.toNat < raceLo rb →
    ∀ (cps : map Checkpoint State) (s2 : Store map) (ts : BeaconState),
      (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map))
        mid att.data.target).run mid = .ok ({ mid with checkpointStates := cps }, s2) →
      FcMap.lookup cps att.data.target = some (pureState ts) →
      (∀ ci ∈ getCommitteeIndices att.committeeBits,
        ci < committeeCountOf (pureState ts) (computeEpochAtSlot att.data.slot)) ∧
      ∀ ci, if ci < committeeCountOf (pureState ts) (computeEpochAtSlot att.data.slot)
        then getBeaconCommittee (pureState ts) att.data.slot ci
          = .ok (committees att.data.slot.toNat ci)
        else committees att.data.slot.toNat ci = #[]
  /-- `RaceSetting.Fields.attester` for the votes of `[lo, raceLo rb)`. -/
  attester : ∀ v, honest v → ∀ s, raceLo rb ≤ s → s ≤ hi → ∀ i, honestOf i = true →
    ∀ att mid, AttEventAt (node v).seed ((run v s).events.map Prod.fst) att mid →
    (∃ A, AttIndices mid att A ∧ i ∈ A) →
    lo ≤ att.data.slot.toNat → att.data.slot.toNat < raceLo rb →
    HonestData (run (nodeOf i) att.data.slot.toNat).store
      (run (nodeOf i) att.data.slot.toNat).head att
  /-- `RaceSetting.Fields.deliver` for the votes of `[lo, raceLo rb)`. -/
  deliver : ∀ v, honest v → ∀ s, raceLo rb ≤ s → s ≤ hi → ∀ i, honestOf i = true →
    ∀ t, lo ≤ t → t < raceLo rb → t < s → committeeVotes committees i t = true →
    ∃ (es1 es2 : List TraceEvent) (att : Attestation) (fb : Bool),
      (run v s).events.map Prod.fst = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧
      att.data.slot.toNat = t ∧
      ∀ arr mid, NodeTrace (node v).seed es1 arr mid → ∀ A, AttIndices mid att A → i ∈ A
  /-- `RaceSetting.Fields.signer` at the first slot of the window. -/
  signer : ∀ v, honest v → ∀ i, honestOf i = true →
    HonestSigner (node v).seed ((run v (raceLo rb)).events.map Prod.fst) i

/-- The premises of the composed theorem, for the block `rb` at `r`, the anchor state `A`, the
anchor block `a`, and the epoch `E₁`.

- `fields`: the race premises over the window, without a justified state and without the first
  slot. `preDuties`: the same duties for the votes from the slot of the anchor block on.
- `core`, `block`: the head runs from the slot of the anchor block on, and the block `rb` at `r`
  in the stores of the window. The head runs name no head position. The theorems derive that
  every honest head of the window lies below `empty r`.
- `pathBefore`: the scenario, in which `r` extends the honest chain. Take an honest head of a
  slot `t` before the window, from the slot of the anchor block on. Every honest store of the
  window holds its block. In that store, the supported node of an honest message of `t` on that
  head lies at or above `pending r`. It also lies below every node of the path that a message of
  slot `t` can support (`supSlot`).
- `cases`: each honest head run of the window has one of two justified blocks. A justified
  block no later than `rb` comes with a justified state, the count of the race, and the count
  at every fork of the path from the justified block to `pending r` (`ForkCount`). The other
  case is a justified block past `rb`.
- The anchor premises of `honestNodes_accountable`, and the anchor premises of
  `honestStore_finalizes`. The header of the anchor state is no later than the first slot of
  its epoch (`aligned`), as at genesis and at a checkpoint-sync anchor. So the chain root of
  an epoch from the anchor epoch on is the anchor block or a block of the run.
- `totals`: each honest store of the window meets the totals premise of
  `honestNodes_accountable` (`StoreTotals`).
- `honestReg`: every honest index is an index of the anchor registry. The registry only
  appends and no step writes a public key, so such an index names one key on every run from
  `A` (`ChainRun.pubkey_eq`). So `honestOf` labels keys. Two runs can fill one registry position
  with different validators, and the label does not depend on that. An honest validator that
  joins after `A` counts as adversarial.
- `allChains`: on every prefix of a store run of an honest store of the window, up to epoch
  `E₁ + 5`, the adversary holds less than two thirds of the total active balance.
- `honestVotes`: take an honest vote from the slot of the anchor block on, on a store run of an
  honest store of the window. It targets the checkpoint block of the voter's head at the vote
  slot.

The premises on the carrier chain are in `CarrierWindow` (`ViableHonest.lean`).

`totals`, `allChains` and `honestVotes` read only the runs whose blocks an honest store
holds. A store run ends at a stored block. So no state of the run is later than the last
block of the store. -/
structure FinalitySetting {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (A : BeaconState)
    (a : BeaconBlock) (E₁ : Nat) (nodeOf : ValidatorIndex → Node)
    (honestOf : ValidatorIndex → Bool) (committees : Nat → Nat → Array ValidatorIndex) : Prop
    where
  fields : RaceSetting.Fields honest node run r rb (finSlot E₁) nodeOf honestOf committees
  preDuties : EarlyDuties honest node run rb a.slot.toNat (finSlot E₁) nodeOf honestOf committees
  core : ∀ v, honest v → ∀ t, a.slot.toNat ≤ t → t ≤ finSlot E₁ → (run v t).Core (node v) t
  block : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
    FcMap.lookup (run v t).store.blocks r = some rb
  pathBefore : ∀ u, honest u → ∀ t, a.slot.toNat ≤ t → t < raceLo rb → ∀ hb : BeaconBlock,
    FcMap.lookup (run u t).store.blocks (run u t).head.root = some hb →
    ∀ v, honest v → ∀ s, raceLo rb ≤ s → s ≤ finSlot E₁ →
    FcMap.lookup (run v s).store.blocks (run u t).head.root = some hb ∧
    NodeBelow (run v s).store (honestSupported (run u t).head hb.slot.toNat t) (.pending r) ∧
      ∀ y, NodeBelow (run v s).store y (.pending r) → supSlot (run v s).store y ≤ t →
        NodeBelow (run v s).store y (honestSupported (run u t).head hb.slot.toNat t)
  cases : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
    (∃ jst, (∃ jb, FcMap.lookup (run v t).store.blocks
          (run v t).store.justifiedCheckpoint.root = some jb ∧ jb.slot ≤ rb.slot) ∧
      FcMap.lookup (run v t).store.checkpointStates (run v t).store.justifiedCheckpoint
        = some (pureState jst) ∧
      (raceLo rb < t → RaceCount jst honestOf committees (raceLo rb) t) ∧
      ∀ x y xb, NodeBelow (run v t).store (.pending (run v t).store.justifiedCheckpoint.root) x →
        NodeEdge (run v t).store x y → NodeBelow (run v t).store y (.pending r) →
        FcMap.lookup (run v t).store.blocks x.root = some xb →
        ForkCount jst honestOf committees (supSlot (run v t).store y) (xb.slot.toNat + 1) t) ∨
    ∃ jb, FcMap.lookup (run v t).store.blocks (run v t).store.justifiedCheckpoint.root = some jb ∧
      rb.slot < jb.slot
  anchorState : ∀ v, honest v → (node v).anchorState = A
  anchorBlock : ∀ v, honest v → (node v).anchor = a
  stateRoots : ∀ v, honest v → ∀ (sb : SignedBeaconBlock) (w : Nat),
    (TraceEvent.handler (.block sb), w) ∈ (node v).events →
    sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot
  anchorRoot : htr (filledHeader A) = htr a
  anchorHeader : filledHeader A = headerOf a
  anchorFilled : HdrFilled A
  aligned : A.latestBlockHeader.slot.toNat ≤ epochOf A * slotsPerEpoch
  ord : StateCkptOrd A
  roots : AnchorRoots A
  cps : AnchorCps A
  sphr : 2 * slotsPerEpoch ≤ EthCLSpecs.Heze.Const.slotsPerHistoricalRoot
  totals : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ → StoreTotals A a (run v t).store
  late : max (epochOf A + 2) 3 * slotsPerEpoch ≤ rb.slot.toNat
  before : rb.slot.toNat < E₁ * slotsPerEpoch
  delay : 0 < EthCLSpecs.Heze.Const.minAttestationInclusionDelay.toNat
  slotPos : 0 < slotDurationMs.toNat
  honestReg : ∀ i, honestOf i = true → i.toNat < A.validators.val.size
  allChains : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ → ∀ p q u,
    StoreRun A a (run v t).store (p ++ q) → ChainRun (2 ^ 64 - 1) p A u → epochOf u ≤ E₁ + 5 →
    3 * advStake u honestOf < 2 * (totBal u).toNat
  honestVotes : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
    ∀ steps i (d : AttestationData), StoreRun A a (run v t).store steps → honestOf i = true →
    RunVote (2 ^ 64 - 1) A steps i d → a.slot.toNat ≤ d.slot.toNat → d.slot.toNat < finSlot E₁ →
    ∃ u u', (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      (run (nodeOf i) d.slot.toNat).store (run (nodeOf i) d.slot.toNat).head.root
      d.target.epoch).run u = .ok (d.target.root, u')

/-- The heads of the first slot of the window avoid `full r`. -/
def FirstSlotAvoids {Node : Type} (honest : Node → Prop) (run : Node → Nat → HeadRun map)
    (r : Root) (rb : BeaconBlock) : Prop :=
  ∀ v, honest v → ¬ NodeBelow (run v (raceLo rb)).store (.full r) (run v (raceLo rb)).head

/-- From the first slot of `E₁`, a checkpoint block other than `r` of an honest head below
EMPTY `r`, at an epoch from `E₁` to `E₁ + 4`, is past `rb`. `FinalitySetting.early` proves it:
the checkpoint walk from such a head stops at `r` or at a block below `r`. -/
def EarlyTargets {Node : Type} (honest : Node → Prop) (run : Node → Nat → HeadRun map)
    (r : Root) (rb : BeaconBlock) (E₁ : Nat) : Prop :=
  ∀ v, honest v → ∀ t, E₁ * slotsPerEpoch ≤ t → t < finSlot E₁ →
    NodeBelow (run v t).store (.empty r) (run v t).head →
    ∀ (e : Epoch) (c : Root) (u u' : Store map), E₁ ≤ e.toNat → e.toNat ≤ E₁ + 4 → c ≠ r →
    (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
      (run v t).store (run v t).head.root e).run u = .ok (c, u') →
    ∃ cb, FcMap.lookup (run v t).store.blocks c = some cb ∧ rb.slot < cb.slot

/-- The finalized root of an honest store at the end of the window is not `r` once its epoch
is `E₁` or later. `CarrierWindow.finRoot_ne` proves it from a block of the carrier chain after
`rb`, no later than the first slot of `E₁`. -/
def FinRootNe {Node : Type} (honest : Node → Prop) (run : Node → Nat → HeadRun map)
    (r : Root) (E₁ : Nat) : Prop :=
  ∀ v, honest v → E₁ ≤ (run v (finSlot E₁)).store.finalizedCheckpoint.epoch.toNat →
    (run v (finSlot E₁)).store.finalizedCheckpoint.root ≠ r

/-- **An honest vote of the window.** The attestation data `d` is a vote of the validator `i`
that the window reads: the data of an attestation event that an honest node accepted, with `i`
among its attesting indices (`AttWrite`), or a placed vote of `i` on a store run of an honest
store. -/
def HonestVoteOf {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (rb : BeaconBlock) (A : BeaconState) (a : BeaconBlock)
    (E₁ : Nat) (i : ValidatorIndex) (d : AttestationData) : Prop :=
  ∃ v, honest v ∧ ∃ s, raceLo rb ≤ s ∧ s ≤ finSlot E₁ ∧
    ((∃ (att : Attestation) (mid : Store map), att.data = d ∧
        AttEventAt (node v).seed ((run v s).events.map Prod.fst) att mid ∧ AttWrite mid att i) ∨
      ∃ steps, StoreRun A a (run v s).store steps ∧ RunVote (2 ^ 64 - 1) A steps i d)

/-- **The honest votes before slot `s` are on the EMPTY side.** For each honest vote of the
window from a slot of `[raceLo rb, s)`, the head of the voter's node at the vote slot lies below
`empty r` or is `pending r`. Each such head supports `empty r` or a node below it. The window
induction carries this fact about votes, because a fact about all honest heads can fail: an
honest node with no validators can hold a head off `r` in the epoch of `rb`. -/
def VotesEmpty {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (A : BeaconState)
    (a : BeaconBlock) (E₁ : Nat) (nodeOf : ValidatorIndex → Node)
    (honestOf : ValidatorIndex → Bool) (s : Nat) : Prop :=
  ∀ i, honestOf i = true → ∀ d, HonestVoteOf honest node run rb A a E₁ i d →
    raceLo rb ≤ d.slot.toNat → d.slot.toNat < s →
    NodeBelow (run (nodeOf i) d.slot.toNat).store (.empty r) (run (nodeOf i) d.slot.toNat).head ∨
      (run (nodeOf i) d.slot.toNat).head = .pending r

/-- **No honest head before slot `s` is FULL `r` or below it.** -/
def NoFull {Node : Type} (honest : Node → Prop) (run : Node → Nat → HeadRun map) (r : Root)
    (rb : BeaconBlock) (s : Nat) : Prop :=
  ∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
    ¬ NodeBelow (run u t).store (.full r) (run u t).head

/-- The honest chain of `HonestChain`, and the block of its last slot of `E₁ + 3`. Each honest
node receives that block before `E₁ + 4`, at an event whose store does not hold it yet.
`on_block` returns early on a known block, so this names the first receipt.
`CarrierWindow.chain` proves it from the carrier chain and `LastDelivered`. -/
def FinalityChain {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (A : BeaconState) (honestOf : ValidatorIndex → Bool)
    (E₁ : Nat) : Prop :=
  ∃ (hi : Nat) (steps : List ChainStep) (st : BeaconState)
    (vals : List ValidatorIndex), HonestChain hi steps A st vals honestOf E₁ ∧
    ∃ (p q : List ChainStep) (sb : SignedBeaconBlock) (vb : Bool) (u w : BeaconState),
      steps = p ++ .block sb vb :: .slot :: q ∧ ChainRun hi p A u ∧ BlockStep sb vb u w ∧
      (u.slot.toNat + 1) % slotsPerEpoch = 0 ∧ u.slot.toNat / slotsPerEpoch = E₁ + 3 ∧
      ∀ v, honest v → ∃ (es1 es2 : List TraceEvent),
        (run v (finSlot E₁)).events.map Prod.fst = es1 ++ TraceEvent.handler (.block sb) :: es2 ∧
        ∀ arr mid, NodeTrace (node v).seed es1 arr mid →
          storeSlot mid < finSlot E₁ ∧ FcMap.contains mid.blocks (htr sb.message) = false

end Setting

/-! ## The chain root of a justified checkpoint -/

section Root
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root]

/-- **The chain root of an epoch is the anchor block or a stored block of the run.** Take a run
whose blocks form an ancestor path of `s`, and an epoch `e` from the anchor epoch on, after
epoch 0. The anchor header is no later than the first slot of the anchor epoch. Then the chain
root of `e` is the root of `a`, or the root of a stored block no later than the first slot of
`e` (`rootAtSlot_eq_lastRootOf`). -/
theorem chainRoot_block {A : BeaconState} {a : BeaconBlock} {s : Store map}
    {steps : List ChainStep} {k : Root} (hpath : AncestorPath a s k (blocksOf steps))
    (hslot : SlotInv a s) (hanc : htr (filledHeader A) = htr a)
    (hal : A.latestBlockHeader.slot.toNat ≤ epochOf A * slotsPerEpoch) {e : Nat}
    (he1 : 1 ≤ e) (he : epochOf A ≤ e) :
    chainRoot A steps e = htr a ∨ ∃ b, FcMap.lookup s.blocks (chainRoot A steps e) = some b ∧
      b.slot.toNat ≤ e * slotsPerEpoch := by
  have hT : A.latestBlockHeader.slot.toNat ≤ e * slotsPerEpoch :=
    Nat.le_trans hal (Nat.mul_le_mul_right _ he)
  rw [chainRoot_pos _ _ he1, rootAtSlot_eq_lastRootOf hanc steps hT]
  unfold lastRootOf
  cases hl : ((blocksOf steps).filter (fun b => b.slot.toNat ≤ e * slotsPerEpoch)).getLast? with
  | none => exact .inl rfl
  | some b =>
    right
    have hm := List.mem_filter.mp (List.mem_of_getLast? hl)
    obtain ⟨k', hk'⟩ := hpath.mem_lookup hm.1
    have hr : htr b = k' := hslot.atRoot _ _ hk'
    refine ⟨b, ?_, by simpa using hm.2⟩
    show FcMap.lookup s.blocks (htr b) = some b
    rw [hr]
    exact hk'

end Root

/-! ## The stores of the window -/

section Facts
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}

/-- The anchor store of an honest node, at `A` and `a`. -/
theorem FinalitySetting.anchorStore
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    {v : Node} (hv : honest v) :
    EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok (node v).seed := by
  rw [← hset.anchorState v hv, ← hset.anchorBlock v hv]
  exact (hset.fields.nodeOk v hv).anchorStore

/-- The anchor block is no later than `rb`, so before the window. -/
theorem FinalitySetting.anchor_lt
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    {v : Node} (hv : honest v) : a.slot.toNat < raceLo rb := by
  have h := (hset.fields.nodeOk v hv).anchorSlot
  rw [hset.anchorBlock v hv] at h
  have := UInt64.le_iff_toNat_le.mp h
  unfold raceLo
  omega

/-- A head run of the window holds `rb` at `r`: `core` and `block`. -/
theorem FinalitySetting.held
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (v : Node) (hv : honest v) (t : Nat) (ht : raceLo rb ≤ t) (ht' : t ≤ finSlot E₁) :
    (run v t).Held (node v) r rb t :=
  { toCore := hset.core v hv t (by have := hset.anchor_lt hv; omega) ht'
    block := hset.block v hv t ht ht' }

/-- The events of the prefix of a head run are events of the node. -/
theorem FinalitySetting.mem_events
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t) (ht' : t ≤ finSlot E₁)
    {x : TraceEvent} (hx : x ∈ (run v t).events.map Prod.fst) :
    ∃ w, (x, w) ∈ (node v).events := by
  obtain ⟨y, hy, hy1⟩ := List.mem_map.mp hx
  obtain ⟨rest, hsplit⟩ := (hset.held v hv t ht ht').isPrefix
  exact ⟨y.2, by rw [hsplit, ← hy1]; exact List.mem_append_left _ hy⟩

include hw in
/-- A store on the prefix of an honest head run meets `CkptInv`, unless a root collision
exists. -/
theorem FinalitySetting.prefixInv
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) {es1 es2 : List TraceEvent}
    (hes : (run v t).events.map Prod.fst = es1 ++ es2)
    {arr : List (SignedInclusionList × Bool)} {mid : Store map}
    (h : NodeTrace (node v).seed es1 arr mid) : CkptInv A a mid := by
  have hn := hset.fields.nodeOk v hv
  have ha := hset.anchorBlock v hv
  have hmem : ∀ x, x ∈ es1 → ∃ w, (x, w) ∈ (node v).events := fun x hx =>
    hset.mem_events hv ht ht' (by rw [hes]; exact List.mem_append_left _ hx)
  have hself : a.parentRoot ≠ htr a := ha ▸ hn.anchorSelf
  rcases NodeTrace.ckptInv hw h (CkptInv.anchor A a _ (hset.anchorStore hv) hself) hset.ord
      (fun e he => by
        obtain ⟨w, hw'⟩ := hmem _ he
        exact ha ▸ hn.noAnchorParent e w hw')
      (fun sb he => by
        obtain ⟨w, hw'⟩ := hmem _ he
        exact hset.stateRoots v hv sb w hw') with hi | hc
  · exact hi
  · exact absurd hc hcol

/-- The anchor epoch is before the slots of the window. -/
theorem FinalitySetting.anchor_le
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees) {t : Nat}
    (ht : raceLo rb ≤ t) : epochOf A ≤ t / slotsPerEpoch := by
  have hlate := hset.late
  have hp := slotsPerEpochPos
  unfold raceLo at ht
  rw [Nat.le_div_iff_mul_le hp]
  have : epochOf A * slotsPerEpoch ≤ max (epochOf A + 2) 3 * slotsPerEpoch :=
    Nat.mul_le_mul_right _ (by omega)
  omega

include hw in
/-- **The store of an honest head run of the window.** It meets `CkptInv` and `CkptAbove`. It
holds the anchor block at its root. Its justified and finalized epochs are at most the epoch of
the slot of the run. -/
theorem FinalitySetting.storeFacts
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) :
    CkptInv A a (run v t).store ∧ CkptAbove A a (run v t).store ∧
      FcMap.lookup (run v t).store.blocks (htr a) = some a ∧
      (run v t).store.justifiedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch ∧
      (run v t).store.finalizedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch := by
  have hn := hset.fields.nodeOk v hv
  have hq := hset.held v hv t ht ht'
  have hI : CkptInv A a (run v t).store :=
    hset.prefixInv hw hcol hv ht ht' (es2 := []) (by simp) hq.trace
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hAbove : CkptAbove A a (run v t).store :=
    hq.trace.ckptAbove (SlotInv.anchor A a _ (hset.anchorStore hv)
        ((hset.anchorBlock v hv) ▸ hn.anchorSelf)).statesPure
      (CkptAbove.anchor A a _ (hset.anchorStore hv))
  -- The store holds the anchor block at its root.
  have ha : FcMap.lookup (run v t).store.blocks (htr a) = some a := by
    obtain ⟨b', hb'⟩ := NodeTrace.blocks_persist hq.trace _ _
      (getForkchoiceStore_anchor A a _ (hset.anchorStore hv))
    have he := hI.slot.atRoot _ _ hb'
    have : b' = a := Classical.byContradiction fun hne => hcb ⟨b', a, hne, he⟩
    rw [this] at hb'
    exact hb'
  -- Each checkpoint epoch has a witness: the anchor epoch, or a block event of the prefix.
  have h0 : CkptWit A [] (node v).seed := by
    obtain ⟨e1, e2, e3, e4⟩ := getForkchoiceStore_ckpts A a _ (hset.anchorStore hv)
    exact ⟨.inl (Nat.le_of_eq e1), .inl (Nat.le_of_eq e2), .inl (Nat.le_of_eq e3),
      .inl (Nat.le_of_eq e4)⟩
  obtain ⟨wj, wf, -, -⟩ := hq.trace.ckptWit hset.ord
    (fun es1 es2 arr1 mid hes h1 => hset.prefixInv hw hcol hv ht ht' hes h1) h0
  have hlt : rb.slot.toNat < t := by unfold raceLo at ht; omega
  have hwit : ∀ x, EpochWit A ((run v t).events.map Prod.fst) x → x ≤ t / slotsPerEpoch := by
    intro x hx
    rcases hx with hx | ⟨sb, hm, hx⟩
    · exact Nat.le_trans hx (hset.anchor_le ht)
    · exact Nat.le_trans hx (Nat.div_le_div_right
        ((hq.event_slot_le hw hn (hn.anchor_le_of_lt hlt) hcol hm)))
  exact ⟨hI, hAbove, ha, hwit _ wj, hwit _ wf⟩

include hw in
/-- **The finalized epoch of an honest head run of the window lags its slot by two epochs.** It
is at most the anchor epoch, or at most the epoch of `t` less two. The node's events form a
clocked trace from the anchor store (`ClockedTrace.tickLag`), whose two finalized epochs are the
anchor epoch, and the prefix of the run meets `CkptInv` at each store (`NodeTrace.storeLag`). -/
theorem FinalitySetting.finLag
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) :
    (run v t).store.finalizedCheckpoint.epoch.toNat ≤ epochOf A ∨
      (run v t).store.finalizedCheckpoint.epoch.toNat + 2 ≤ t / slotsPerEpoch := by
  have hn := hset.fields.nodeOk v hv
  have hq := hset.held v hv t ht ht'
  obtain ⟨-, e2, -, e4⟩ := getForkchoiceStore_ckpts A a _ (hset.anchorStore hv)
  have h0 : (node v).seed.finalizedCheckpoint.epoch.toNat ≤ epochOf A ∧
      (node v).seed.unrealizedFinalizedCheckpoint.epoch.toNat ≤ epochOf A :=
    ⟨Nat.le_of_eq e2, Nat.le_of_eq e4⟩
  obtain ⟨rest, hsplit⟩ := hq.isPrefix
  -- A tick of the prefix is a tick of the node's events.
  have htick := hn.clocked.tickLag hset.slotPos h0
  have hlag := hq.trace.storeLag hset.slotPos hset.ord
    (fun es1 es2 arr1 mid hes h1 => hset.prefixInv hw hcol hv ht ht' hes h1) ⟨.inl h0.1, .inl h0.2⟩
    (fun es1 es2 arr1 mid time hes h1 => htick es1 (es2 ++ rest.map Prod.fst) arr1 mid time
      (by rw [hsplit, List.map_append, hes]; simp) h1)
  obtain ⟨cs, hcsn, hcur⟩ := hq.slot
  have hS : storeSlot (run v t).store = t := by
    rw [← getCurrentSlot_storeSlot hcur, hcsn]
  have hf := hlag.1
  rw [hS] at hf
  exact hf

include hw in
/-- **A checkpoint justified on a chain of the store is on the EMPTY side.** Take an honest head
run of slot `t` and a store run of its store. The chain of the run
justifies `x`, past the base and before epoch `E₁ + 5`. Every honest head before `t` lies below
`empty r`. Then:

- An honest validator voted for `x` on the run (`justified_honest_voter`).
- The vote is from a slot before its block, and so before `t`. It is in the window, since `x`
  starts after `rb` (`RunVote.slot_lt_block`).
- The target is the checkpoint block of the voter's head (`honestVotes`). That head is below
  `empty r`. The target block is past `rb` (`hpast`), so the target is on the EMPTY side of the
  voter's store (`checkpointBlock_emptySide`).
- `NodeBelow.transfer` moves the EMPTY side to the store of the run. -/
theorem FinalitySetting.target_empty
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) {steps : List ChainStep} {k : Root} {v' : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v')
    (hpath : AncestorPath a (run v t).store k (blocksOf steps))
    (hsr : StoreRun A a (run v t).store steps) {x : Cp}
    (hj : EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps A regVals) x)
    (hxK : anchorK A < x.epoch) (hxB : x.epoch + 1 ≤ E₁ + 5)
    (hlo : rb.slot.toNat < x.epoch * slotsPerEpoch)
    (hblk : ∃ xb, FcMap.lookup (run v t).store.blocks x.root = some xb) (hxr : x.root ≠ r)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf t)
    (hpast : ∀ u, honest u → ∀ t', raceLo rb ≤ t' → t' < t → t' / slotsPerEpoch = x.epoch →
      NodeBelow (run u t').store (.empty r) (run u t').head →
      ∀ (e : Epoch) (uu uu' : Store map), e.toNat = x.epoch →
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map))
        (run u t').store (run u t').head.root e).run uu = .ok (x.root, uu') →
      ∀ cb, FcMap.lookup (run u t').store.blocks x.root = some cb → rb.slot < cb.slot) :
    OnEmptySide (run v t).store r x.root := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hn := hset.fields.nodeOk v hv
  have hq := hset.held v hv t ht ht'
  have hinvs : SlotInv a (run v t).store := (hset.storeFacts hw hcol hv ht ht').1.slot
  obtain ⟨i, d, hhon, hvote, htg⟩ :=
    justified_honest_voter hrun hset.cps hset.ord honestOf
      (fun p q u he hu hB => hset.allChains v hv t ht ht' p q u (he ▸ hsr) hu hB) hj hxK hxB
  subst htg
  -- The vote is from a slot of the window, before `t`.
  obtain ⟨hep, b, hbmem, hbs⟩ := RunVote.slot_lt_block hvote hrun
  obtain ⟨k', hk'⟩ := hpath.mem_lookup hbmem
  have hlt : rb.slot.toNat < t := by unfold raceLo at ht; omega
  have hbt := hq.block_slot_le hn (hn.anchor_le_of_lt hlt) hk'
  have hdel := hset.delay
  have hdt : d.slot.toNat < t := by omega
  have hdlo : raceLo rb ≤ d.slot.toNat := by
    have := Nat.div_mul_le_self d.slot.toNat slotsPerEpoch
    simp only [toCp] at hlo hep
    unfold raceLo
    rw [← hep] at this
    omega
  -- The target is the checkpoint block of the voter's head, below `empty r`.
  obtain ⟨uu, uu', hck⟩ := hset.honestVotes v hv t ht ht' steps i d hsr hhon hvote
    (by have := hset.anchor_lt hv; omega) (by omega)
  have hu := hset.fields.honestNode i hhon
  have hqu := hset.held (nodeOf i) hu d.slot.toNat hdlo (by omega)
  have hinvu : SlotInv a (run (nodeOf i) d.slot.toNat).store :=
    hset.anchorBlock _ hu ▸ hqu.slotInv hw (hset.fields.nodeOk _ hu) hcol
  have hbelow : NodeBelow (run (nodeOf i) d.slot.toNat).store (.empty r)
      (run (nodeOf i) d.slot.toNat).head := by
    rcases hV i hhon d ⟨v, hv, t, ht, ht', .inr ⟨steps, hsr, hvote⟩⟩ hdlo hdt with h | hpend
    · exact h
    -- A head at `pending r` reads `r` itself, as the target epoch starts after `rb`.
    exfalso
    have hfit : d.target.epoch.toNat * slotsPerEpoch < 2 ^ 64 := by
      have h2 := Nat.div_mul_le_self d.slot.toNat slotsPerEpoch
      rw [← hep] at h2
      have := d.slot.toNat_lt
      omega
    have hS := computeStartSlotAtEpoch_ok_of_lt hfit
    have hSv : (d.target.epoch * UInt64.ofNat slotsPerEpoch).toNat =
        d.target.epoch.toNat * slotsPerEpoch := by
      have hn' : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
        UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
      rw [UInt64.toNat_mul, hn', Nat.mod_eq_of_lt hfit]
    have hrS : ¬ rb.slot > d.target.epoch * UInt64.ofNat slotsPerEpoch := fun h => by
      have := UInt64.lt_iff_toNat_lt.mp h
      simp only [toCp] at hlo
      omega
    rw [hpend, show (ForkChoiceNode.pending r).root = r from rfl] at hck
    have hstop := getCheckpointBlock_run_stop _ r rb hqu.block d.target.epoch _ hS hrS uu
    rw [hck] at hstop
    injection hstop with hstop
    injection hstop with hxr'
    exact hxr (by simpa only [toCp] using hxr')
  obtain ⟨cb, hcbk⟩ := checkpointBlock_block _ hinvu.slots r rb hqu.block _ hbelow _ _ _ _ hck
  have hgt := hpast (nodeOf i) hu d.slot.toNat hdlo hdt (by simp only [toCp]; exact hep.symm)
    hbelow d.target.epoch uu uu' rfl hck cb hcbk
  have hE := checkpointBlock_emptySide _ hinvu.slots r rb hqu.block _ hbelow _ _ _ _ hck cb hcbk
    hgt
  -- Move the EMPTY side to the store of the run.
  exact NodeBelow.transfer _ _ hinvu.slots r rb hqu.block a
    (fun _ _ _ hx hy => SlotInv.block_eq hinvu hinvs hcb hx hy)
    (fun k x hx => hinvs.parentIn k x hx) (hset.anchorBlock v hv ▸ hn.anchorSlot) _ hE
    (Or.inr hblk)

include hw in
/-- **A justified block past `rb` is on the EMPTY side.** The justified checkpoint `j` of an
honest store of the window has a block past `rb`. Every honest head before the slot of the run
lies below `empty r`. Then:

- `j` is not the anchor checkpoint, whose block is the anchor (`CkptAbove`).
- `j` is justified on the chain of a run from `A` along an ancestor path of the store
  (`justified_source`). Its root is a stored block no later than the first slot of its epoch
  (`chainRoot_block`). That block is the block past `rb`, so `j` is past the base.
- `FinalitySetting.target_empty` applies. A block of a voter's store at the root of `j` is the
  block past `rb`. -/
theorem FinalitySetting.justified_empty
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb ≤ t)
    (ht' : t ≤ finSlot E₁) {jb : BeaconBlock}
    (hjb : FcMap.lookup (run v t).store.blocks (run v t).store.justifiedCheckpoint.root = some jb)
    (hjlt : rb.slot < jb.slot)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf t) :
    OnEmptySide (run v t).store r (run v t).store.justifiedCheckpoint.root := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  obtain ⟨hI, hAbove, ha, hjt, -⟩ := hset.storeFacts hw hcol hv ht ht'
  have hjlt' := UInt64.lt_iff_toNat_lt.mp hjlt
  have haslot : a.slot ≤ rb.slot := hset.anchorBlock v hv ▸ (hset.fields.nodeOk v hv).anchorSlot
  -- The root of `j` is not the anchor root: the anchor block is no later than `rb`.
  have hnota : (run v t).store.justifiedCheckpoint.root ≠ htr a := fun he => by
    rw [he, ha] at hjb
    cases hjb
    exact absurd haslot (UInt64.not_le.mpr hjlt)
  generalize hj : (run v t).store.justifiedCheckpoint = j at hjb hjt hnota ⊢
  have hjA : epochOf A < j.epoch.toNat := by
    rcases (hj ▸ hAbove.1 : Above A a j) with rfl | h
    · exact absurd rfl hnota
    · exact h
  obtain ⟨k, steps, v', hrun, hpath, -, -, hjus, hsr⟩ := justified_source hw (hj ▸ hI.jSource)
    (by rw [currentEpochOf_epochOf]; exact hjA) hset.roots hset.cps hset.ord hset.sphr
    (hset.totals v hv t ht ht')
  have hm := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hset.cps hset.ord
    (hrun.blocks_slot_ge (Nat.le_refl _))
  have hon : chainRoot A steps j.epoch.toNat = j.root :=
    Option.some.inj (hjus.onChain fun x hx => (hm.base x hx).2)
  -- The block at the root of `j` is no later than the first slot of its epoch.
  have hjS : jb.slot.toNat ≤ j.epoch.toNat * slotsPerEpoch := by
    rcases chainRoot_block hpath hI.slot hset.anchorRoot hset.aligned (e := j.epoch.toNat)
        (by omega) (Nat.le_of_lt hjA) with h | ⟨b, hb, hbs⟩
    · exact absurd (hon ▸ h) hnota
    · rw [hon, hjb] at hb
      cases hb
      exact hbs
  have hlate := hset.late
  have hK : anchorK A < j.epoch.toNat := by
    unfold anchorK
    have h1 : max (epochOf A + 2) 3 * slotsPerEpoch < j.epoch.toNat * slotsPerEpoch := by omega
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    omega
  have hjE : j.epoch.toNat ≤ E₁ + 4 := by
    have : t / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right ht'
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    omega
  -- The root of `j` is not `r`: its block is past `rb`.
  have hjr : j.root ≠ r := fun he => by
    rw [he, (hset.held v hv t ht ht').block] at hjb
    cases hjb
    exact UInt64.lt_irrefl _ hjlt
  exact hset.target_empty hw hcol hv ht ht' hrun hpath hsr (x := toCp j) hjus hK (by
    simp only [toCp]; omega) (by simp only [toCp]; omega) ⟨jb, hjb⟩ hjr hV
    (fun u hu t' hlo' hlt' _ _ e uu uu' _ _ cb hcb' => by
      have hqu := hset.held u hu t' hlo' (by omega)
      have hinvu : SlotInv a (run u t').store :=
        hset.anchorBlock _ hu ▸ hqu.slotInv hw (hset.fields.nodeOk _ hu) hcol
      have : cb = jb := SlotInv.block_eq hinvu hI.slot hcb hcb' hjb
      rw [this]
      exact hjlt)

end Facts

/-! ## The theorems -/

section Main
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

/-- The viability step. Take an honest head run after the first slot, whose justified block is no
later than `rb`. The honest votes before its slot are on the EMPTY side, and no honest head
before it is at or below `full r`. Then `empty r` is viable beside `full r` at that run. -/
def ViableStep {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (A : BeaconState)
    (a : BeaconBlock) (E₁ : Nat) (nodeOf : ValidatorIndex → Node)
    (honestOf : ValidatorIndex → Bool) (hi : Nat) : Prop :=
  ∀ s, raceLo rb < s → s ≤ hi →
    VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s → NoFull honest run r rb s →
    ∀ v, honest v →
      (∃ jb, FcMap.lookup (run v s).store.blocks (run v s).store.justifiedCheckpoint.root = some jb ∧
        jb.slot ≤ rb.slot) →
      EmptyViableWithFull (run v s).store r

/-- The vote step. Take a slot `s` of the window, with no root collision. The honest votes before
`s` come from heads below `empty r` or at `pending r`, and no honest head up to `s` is at or
below `full r`. Then each honest vote of `s` comes from such a head. `FinalitySetting.voteStep`
proves it from `FinalitySetting` and the carrier chain. The carrier chain places the vote, so
the target of the vote is the checkpoint of the carrier chain. -/
def VoteStep {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (A : BeaconState)
    (a : BeaconBlock) (E₁ : Nat) (nodeOf : ValidatorIndex → Node)
    (honestOf : ValidatorIndex → Bool) (hi : Nat) : Prop :=
  ¬ RootCollision → ∀ s, raceLo rb ≤ s → s < hi →
    VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s →
    NoFull honest run r rb (s + 1) →
    ∀ i, honestOf i = true → ∀ d, HonestVoteOf honest node run rb A a E₁ i d →
      d.slot.toNat = s →
      NodeBelow (run (nodeOf i) s).store (.empty r) (run (nodeOf i) s).head ∨
        (run (nodeOf i) s).head = .pending r

/-- The race step. Take an honest head run after the first slot, whose justified block is no
later than `rb`, with no root collision. The honest votes before its slot are on the EMPTY side,
and no honest head before it is at or below `full r`. Then EMPTY is ahead of FULL on weight at
`r`. `FinalitySetting.raceAhead` (`ForkSides.lean`) proves it. -/
def RaceAhead {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (A : BeaconState)
    (a : BeaconBlock) (E₁ : Nat) (nodeOf : ValidatorIndex → Node)
    (honestOf : ValidatorIndex → Bool) (hi : Nat) : Prop :=
  ¬ RootCollision → ∀ s, raceLo rb < s → s ≤ hi →
    VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s → NoFull honest run r rb s →
    ∀ v, honest v →
      (∃ jb, FcMap.lookup (run v s).store.blocks (run v s).store.justifiedCheckpoint.root = some jb ∧
        jb.slot ≤ rb.slot) →
      WeightAhead (run v s).store r

include hw in
/-- **Up to a slot of the window.** A root collision exists, or two facts hold. No honest head
from the first slot to `hi` is at or below `full r`. Every honest vote up to `hi` comes from a
head on the EMPTY side (`VotesEmpty`).

The heads of the first slot avoid `full r` (`hfirst`). At a later slot with a justified block no
later than `rb`, `empty r` stays viable beside `full r` (`hviable`) and is ahead on weight
(`hahead`). So the head avoids `full r` (`getHead_run_below_empty`). A justified block past `rb`
keeps the head on the EMPTY side (`justified_empty`). The honest votes of each slot then come
from heads on the EMPTY side (`hvote`). -/
theorem heads_avoid_full_upto {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hfirst : FirstSlotAvoids honest run r rb) {hi : Nat} (hhi : hi ≤ finSlot E₁)
    (hviable : ViableStep honest node run r rb A a E₁ nodeOf honestOf hi)
    (hvote : VoteStep honest node run r rb A a E₁ nodeOf honestOf hi)
    (hahead : RaceAhead honest node run r rb A a E₁ nodeOf honestOf hi) :
    RootCollision ∨ (NoFull honest run r rb (hi + 1) ∧
      VotesEmpty honest node run r rb A a E₁ nodeOf honestOf hi) := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  right
  -- One slot: no honest head of `s` is at or below `full r`.
  have hstep : ∀ s, raceLo rb ≤ s → s ≤ hi →
      VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s → NoFull honest run r rb s →
      ∀ v, honest v → ¬ NodeBelow (run v s).store (.full r) (run v s).head := by
    intro s hlo hs' hV hN v hv
    have hs : s ≤ finSlot E₁ := Nat.le_trans hs' hhi
    have hQ := hset.held v hv s hlo hs
    have hinv := hQ.slotInv hw (hset.fields.nodeOk v hv) hcol
    by_cases hfirst' : s = raceLo rb
    · subst hfirst'
      exact hfirst v hv
    have hlos : raceLo rb < s := by omega
    obtain ⟨s', hrun⟩ := hQ.headRun
    rcases hset.cases v hv s hlo hs with ⟨jst, ⟨jb, hjb, hjle⟩, -, -, -⟩ | ⟨jb, hjb, hjlt⟩
    · -- The justified block is no later than `rb`: the race step.
      exact (getHead_run_below_empty _ r (hahead hcol s hlos hs' hV hN v hv ⟨jb, hjb, hjle⟩)
        (hviable s hlos hs' hV hN v hv ⟨jb, hjb, hjle⟩)
        (hinv.justified_not_below hQ.block hjb hjle) _ s' _ hrun).1
    · -- The justified block is past `rb`: it is on the EMPTY side.
      have hj := hset.justified_empty hw hcol hv hlo hs hjb hjlt hV
      have hhead := getHead_run_below_justified _ _ _ _ hrun
      exact below_emptySide_not_full _ hinv.slots r rb hQ.block _ _ hj hhead
  -- The induction over the slots of the window.
  have hall : ∀ s, s ≤ hi + 1 → NoFull honest run r rb s ∧
      VotesEmpty honest node run r rb A a E₁ nodeOf honestOf (min s hi) := by
    intro s
    induction s with
    | zero => exact fun _ => ⟨fun _ _ t _ ht => absurd ht (Nat.not_lt_zero _),
        fun _ _ d _ _ hd => absurd hd (Nat.not_lt_zero _)⟩
    | succ s ih =>
      intro hs
      obtain ⟨hN, hV⟩ := ih (by omega)
      have hVs : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s := by
        rw [Nat.min_eq_left (by omega)] at hV
        exact hV
      by_cases hlo : raceLo rb ≤ s
      · have hN' : NoFull honest run r rb (s + 1) := fun u hu t hlo' ht => by
          by_cases hts : t < s
          · exact hN u hu t hlo' hts
          · have hts' : t = s := by omega
            subst hts'
            exact hstep t hlo (by omega) hVs hN u hu
        refine ⟨hN', fun i hhon d hd hdlo hdt => ?_⟩
        by_cases hds : d.slot.toNat < s
        · exact hVs i hhon d hd hdlo hds
        · have hds' : d.slot.toNat = s := by omega
          rw [hds']
          exact hvote hcol s hlo (by omega) hVs hN' i hhon d hd hds'
      · exact ⟨fun _ _ t hlo' ht => absurd hlo' (by omega),
          fun _ _ d _ hdlo hdt => absurd hdlo (by omega)⟩
  have h := hall (hi + 1) (Nat.le_refl _)
  rw [Nat.min_eq_right (by omega)] at h
  exact h

include hw in
/-- **The window.** `heads_avoid_full_upto` at the last slot of the window. -/
theorem heads_avoid_full_window {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hfirst : FirstSlotAvoids honest run r rb)
    (hviable : ViableStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁))
    (hvote : VoteStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁))
    (hahead : RaceAhead honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁)) :
    RootCollision ∨ (NoFull honest run r rb (finSlot E₁ + 1) ∧
      VotesEmpty honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁)) :=
  heads_avoid_full_upto hw hset hfirst (Nat.le_refl _) hviable hvote hahead

include hw in
/-- **Finalization on the EMPTY side.** At the end of the window, every honest store has
finalized `E₁` or later, on the EMPTY side of `r`, or a root collision exists. -/
theorem honestNodes_finalize_empty {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hfirst : FirstSlotAvoids honest run r rb) (hearly : EarlyTargets honest run r rb E₁)
    (hnotR : FinRootNe honest run r E₁) (hchain : FinalityChain honest node run A honestOf E₁)
    (hviable : ViableStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁))
    (hvote : VoteStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁))
    (hahead : RaceAhead honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁)) :
    RootCollision ∨ ∀ v, honest v →
      E₁ ≤ (run v (finSlot E₁)).store.finalizedCheckpoint.epoch.toNat ∧
      OnEmptySide (run v (finSlot E₁)).store r
        (run v (finSlot E₁)).store.finalizedCheckpoint.root := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  right
  intro v hv
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hlate := hset.late
  have hbefore := hset.before
  have hwin : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁) :=
    ((heads_avoid_full_window hw hset hfirst hviable hvote hahead).resolve_left hcol).2
  have ht : raceLo rb ≤ finSlot E₁ := by
    unfold raceLo finSlot
    have : E₁ * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch := Nat.mul_le_mul_right _ (by omega)
    omega
  have ht' : finSlot E₁ ≤ finSlot E₁ := Nat.le_refl _
  have hq := hset.held v hv _ ht ht'
  obtain ⟨hI, -, ha, -, hft⟩ := hset.storeFacts hw hcol hv ht ht'
  -- The anchor epoch and `anchorK` are before `E₁`.
  have hKE : anchorK A < E₁ := by
    unfold anchorK
    have h1 : max (epochOf A + 2) 3 * slotsPerEpoch < E₁ * slotsPerEpoch := by omega
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    omega
  -- The finalized epoch: the store received the last block of `E₁ + 3` in time.
  obtain ⟨hi, steps, st, vals, H, p, q, sb, vb, u, w, hs, hu, hstep, hlast, hep, hrecv⟩ :=
    hchain
  obtain ⟨es1, es2, hes, hslotA⟩ := hrecv v hv
  obtain ⟨sA, arr1, arr2, h1, h2, -⟩ := hq.trace.split hes
  obtain ⟨sB, a1, a2, hsingle, hrest, -⟩ :=
    h2.split (es1 := [TraceEvent.handler (.block sb)]) (es2 := es2) rfl
  have hinvA := hset.prefixInv hw hcol hv ht ht' hes h1
  obtain ⟨cs, hcs, hcur⟩ := hq.slot
  have hS : finSlot E₁ ≤ storeSlot (run v (finSlot E₁)).store := by
    rw [← getCurrentSlot_storeSlot hcur, hcs]
    exact Nat.le_refl _
  obtain ⟨hslotA', hnewA⟩ := hslotA arr1 sA h1
  have hfE := honestStore_finalizes hset.slotPos hcb H hset.anchorFilled
    hset.anchorHeader hs hu hstep hlast hep hinvA hnewA hsingle.single_handler hslotA'
    hrest hS
  refine ⟨hfE, ?_⟩
  -- The finalized checkpoint is justified on a chain of the store, past the base.
  have hnr := hnotR v hv hfE
  generalize hf : (run v (finSlot E₁)).store.finalizedCheckpoint = f at hfE hft hnr ⊢
  obtain ⟨k, steps', v', hrun, hpath, -, -, hfin, hsr⟩ := finalized_source hw (hf ▸ hI.fSource)
    (by rw [currentEpochOf_epochOf]; unfold anchorK at hKE; omega) hset.roots hset.cps hset.ord
    hset.sphr (hset.totals v hv _ ht ht')
  have hm := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hset.cps hset.ord
    (hrun.blocks_slot_ge (Nat.le_refl _))
  have hjus :
      EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps' A regVals) (toCp f) := by
    rcases hfin with h | h
    · exact match h with
      | .one h _ _ _ => h
      | .two h _ _ _ _ _ => h
    · have := (hm.base _ h).1
      simp only [toCp] at this
      omega
  have hon : chainRoot A steps' f.epoch.toNat = f.root :=
    Option.some.inj (hjus.onChain fun x hx => (hm.base x hx).2)
  have hblk : ∃ xb, FcMap.lookup (run v (finSlot E₁)).store.blocks f.root = some xb := by
    rcases chainRoot_block hpath hI.slot hset.anchorRoot hset.aligned (e := f.epoch.toNat)
        (by unfold anchorK at hKE; omega) (by unfold anchorK at hKE; omega) with h | ⟨b, hb, -⟩
    · exact ⟨a, by rw [← hon, h]; exact ha⟩
    · exact ⟨b, hon ▸ hb⟩
  have hfE4 : f.epoch.toNat ≤ E₁ + 4 := by
    rw [finSlot, Nat.mul_div_cancel _ hp] at hft
    exact hft
  refine hset.target_empty hw hcol hv ht ht' hrun hpath hsr (x := toCp f) hjus
    (by simp only [toCp]; omega) (by simp only [toCp]; omega) (by
      simp only [toCp]
      have : E₁ * slotsPerEpoch ≤ f.epoch.toNat * slotsPerEpoch := Nat.mul_le_mul_right _ hfE
      omega) hblk hnr hwin ?_
  intro u hu t' hlo' hlt' hdiv hbel e uu uu' he hck cb hcb'
  simp only [toCp] at hdiv he hck hcb'
  have hE1 : E₁ * slotsPerEpoch ≤ t' := by
    rw [← Nat.le_div_iff_mul_le hp, hdiv]
    exact hfE
  obtain ⟨cb', hcb'', hgt⟩ := hearly u hu t' hE1 hlt' hbel e f.root
    uu uu' (by omega) (by omega) hnr hck
  rw [hcb'] at hcb''
  cases hcb''
  exact hgt

include hw in
/-- **The censored payload is final.** Every honest head of the window avoids `full r`. A later
store of an honest node extends the store of the end of the window, and it meets the totals
premise (`StoreTotals`). Its head avoids `full r`, or there is slashing evidence, or two
blocks or headers share a root.

The theorem takes the first slot (`hfirst`), the early targets (`hearly`), the finalized root
(`hnotR`), the finality chain (`hchain`), the viability step (`hviable`), the vote step
(`hvote`) and the race weight (`hahead`) as premises. `censored_payload_final_carrier` proves
them from the honest inclusion list, the carrier chain and the delivery of its last block of
`E₁ + 3`. -/
theorem censored_payload_final {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hfirst : FirstSlotAvoids honest run r rb) (hearly : EarlyTargets honest run r rb E₁)
    (hnotR : FinRootNe honest run r E₁) (hchain : FinalityChain honest node run A honestOf E₁)
    (hviable : ViableStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁))
    (hvote : VoteStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁))
    (hahead : RaceAhead honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁)) :
    RootCollision ∨
      ((∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
          ¬ NodeBelow (run v t).store (.full r) (run v t).head) ∧
        ∀ v, honest v → ∀ (es : List TraceEvent) (arr : List (SignedInclusionList × Bool))
          (s' : Store map), NodeTrace (run v (finSlot E₁)).store es arr s' →
          (∀ e, TraceEvent.handler e ∈ es → e.NotAtAnchorParent a) →
          (∀ sb, TraceEvent.handler (.block sb) ∈ es →
            sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot) →
          (∀ k₁ bs₁ k₂ bs₂, AncestorPath a (run v (finSlot E₁)).store k₁ bs₁ →
            AncestorPath a s' k₂ bs₂ →
            bs₁.filter (fun b => b.slot.toNat < max (epochOf A + 2) 3 * slotsPerEpoch) =
              bs₂.filter (fun b => b.slot.toNat < max (epochOf A + 2) 3 * slotsPerEpoch)) →
          StoreTotals A a s' →
          ∀ (runner t : Store map) (head : ForkChoiceNode),
          (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) s').run runner
            = .ok (head, t) →
          ¬ NodeBelow s' (.full r) head ∨
          ∃ (st₀ : BeaconState) (p₁ r₁ p₂ r₂ : List ChainStep)
            (pairs : List (IndexedAttestation × IndexedAttestation)),
            ChainRun (2 ^ 64 - 1) p₁ A st₀ ∧ ChainRun (2 ^ 64 - 1) p₂ A st₀ ∧
            SlashingEvidence st₀ (OnRun (2 ^ 64 - 1) A (p₁ ++ r₁))
              (OnRun (2 ^ 64 - 1) A (p₂ ++ r₂))
              (runDrift (2 ^ 64 - 1) st₀ r₁) (runDrift (2 ^ 64 - 1) st₀ r₂) pairs) := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  refine Or.inr ⟨fun v hv t h1 h2 =>
    ((heads_avoid_full_window hw hset hfirst hviable hvote hahead).resolve_left hcol).1
      v hv t h1 (by omega), ?_⟩
  intro v hv es arr s' h2 hev hsr hbase htot' runner t head hhead
  have hp := slotsPerEpochPos
  have hlate := hset.late
  have hbefore := hset.before
  have ht : raceLo rb ≤ finSlot E₁ := by
    unfold raceLo finSlot
    have : E₁ * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch := Nat.mul_le_mul_right _ (by omega)
    omega
  have ht' : finSlot E₁ ≤ finSlot E₁ := Nat.le_refl _
  have hn := hset.fields.nodeOk v hv
  have hq := hset.held v hv _ ht ht'
  have ha := hset.anchorBlock v hv
  have hself : a.parentRoot ≠ htr a := ha ▸ hn.anchorSelf
  have haslot : a.slot ≤ rb.slot := ha ▸ hn.anchorSlot
  obtain ⟨hI, -, -, -, -⟩ := hset.storeFacts hw hcol hv ht ht'
  obtain ⟨hfE, hside⟩ :=
    (honestNodes_finalize_empty hw hset hfirst hearly hnotR hchain hviable hvote
      hahead).resolve_left hcol v hv
  -- The events of the prefix and of the later trace.
  have hevP : ∀ e, TraceEvent.handler e ∈ (run v (finSlot E₁)).events.map Prod.fst →
      e.NotAtAnchorParent a := fun e he => by
    obtain ⟨w, hw'⟩ := hset.mem_events hv ht ht' he
    exact ha ▸ hn.noAnchorParent e w hw'
  have hsrP : ∀ sb, TraceEvent.handler (.block sb) ∈ (run v (finSlot E₁)).events.map Prod.fst →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot := fun sb he => by
    obtain ⟨w, hw'⟩ := hset.mem_events hv ht ht' he
    exact hset.stateRoots v hv sb w hw'
  have hevAll : ∀ e, TraceEvent.handler e ∈ (run v (finSlot E₁)).events.map Prod.fst ++ es →
      e.NotAtAnchorParent a := fun e he => by
    rcases List.mem_append.mp he with he | he
    · exact hevP e he
    · exact hev e he
  have hsrAll : ∀ sb, TraceEvent.handler (.block sb) ∈
      (run v (finSlot E₁)).events.map Prod.fst ++ es →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot := fun sb he => by
    rcases List.mem_append.mp he with he | he
    · exact hsrP sb he
    · exact hsr sb he
  -- The finality lock.
  rcases honestNode_finality_lock hw (hset.anchorStore hv) hself hq.trace h2 hevAll r rb hq.block
      haslot hside runner t head hhead with hrc | hconf | hnot
  · exact absurd hrc hcol
  · right
    have hW := hq.trace.append h2
    have hI' := (NodeTrace.ckptInv hw hW (CkptInv.anchor A a _ (hset.anchorStore hv) hself)
      hset.ord hevAll hsrAll).resolve_right hcol
    have hgrow := h2.ckptGrows hI.slot.statesPure
    have hep : (run v (finSlot E₁)).store.finalizedCheckpoint.epoch ≤
        s'.justifiedCheckpoint.epoch :=
      UInt64.le_trans hgrow.2.1 hI'.ord
    have hfX : max (epochOf A + 2) 3 ≤
        (run v (finSlot E₁)).store.finalizedCheckpoint.epoch.toNat := by
      have h1 : max (epochOf A + 2) 3 * slotsPerEpoch < E₁ * slotsPerEpoch := by omega
      have h2 := Nat.lt_of_mul_lt_mul_right h1
      omega
    rcases honestNodes_accountable hw hset.fields.sort (hset.anchorStore hv) hself hW hq.trace
        hevAll hevP hsrAll hsrP hset.anchorRoot hset.ord hset.roots hset.cps hset.sphr
        htot' (hset.totals v hv _ ht ht') hconf hep hfX hbase with hrc | hev'
    · exact absurd hrc hcol
    · exact hev'
  · exact Or.inl hnot

end Main

end EthCLSpecs.Proofs.Heze
