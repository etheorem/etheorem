import EthCLSpecs.Proofs.Heze.PayloadRaceCount
import EthCLSpecs.Proofs.Heze.HonestHead

/-!
# `EthCLSpecs.Proofs.Heze.PayloadRaceDecision`: the decision slot opens the race

`race_empty_persists_exec` (`PayloadRaceExec.lean`) takes the first slot of the window as a
premise: the honest heads of slot `N + 1` avoid `full r` (`RaceSetting.first`). Tier T1
proves that fact at one honest node (`honestNode_head_avoids_full`, `HonestHead.lean`). This
module joins the two.

`DecisionSetting` holds the premises of tier T1 that `RaceSetting.Core` does not give:

- the EL rule
- the honest inclusion list and its send window
- the facts of each node at the root `r`
- the envelopes that omit the transaction

The head run of slot `N + 1` gives the rest: the trace prefix, the store, the wall time, the
`getHead` run, and the justified block. The current slot of the run puts the wall time in
slot `N + 1` (`slot_window_of_getCurrentSlot`, `ClockedTrace.lean`).

`RaceSetting.Core.first_of_decision` proves `RaceSetting.first`, or a root collision.
`race_empty_persists_composed` states tier T2 under `RaceSetting.Core`, `DecisionSetting`,
and `RaceCommittees` (`PayloadRaceCount.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap LawfulInclusionList)
open EthCLSpecs.Heze (Preset Config State BeaconState Root Checkpoint BeaconBlock ValidatorIndex
  InclusionList
  SignedExecutionPayloadEnvelope ExecutionPayload ExecutionRequests Transaction)
open EthCLSpecs.Heze.Const (slotDurationMs)

section Decision
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The premises of tier T1 at the honest nodes of slot `N + 1`, for the block `rb` at `r`.
The honest member of the IL committee `committee` sends the list `il` at `tSend`. The list
reaches every honest node within `Δ`, before the IL due time of slot `N - 1`. Every envelope
for `r` at an honest node omits `tx`, with no valid omission under the EL rule. -/
structure DecisionSetting {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (g : UInt64)
    (committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize)
    (il : InclusionList) (tSend Δ : Nat) (txs : ExecutionPayload → Array Transaction)
    (isValidOmission : ExecutionPayload → Transaction → Prop) (tx : Transaction) : Prop where
  /-- The EL answers by the inclusion-list rule. -/
  el : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs isValidOmission
  /-- The honest nodes share the genesis time `g`. -/
  genesis : ∀ v, honest v → (node v).seed.genesisTime = g
  /-- The stores of each honest node agree on the block at `r` and on the committee. -/
  root : ∀ v, honest v → RootFacts (node v).seed (node v).events r rb.slot committee
  /-- The seed of each honest node holds no answer at `r`. -/
  answer0 : ∀ v, honest v → FcMap.lookup (node v).seed.payloadInclusionListSatisfaction r = none
  /-- The seed of each honest node holds no payload at `r`. -/
  payload0 : ∀ v, honest v → FcMap.lookup (node v).seed.payloads r = none
  /-- The honest list reaches each honest node. -/
  list : ∀ v, honest v → HonestList (node v).events il tSend Δ
  /-- Every envelope for `r` at an honest node omits `tx`, with no valid omission. -/
  omits : ∀ v, honest v → ∀ (signedEnv : SignedExecutionPayloadEnvelope) (w : Nat),
    (.handler (.envelope signedEnv), w) ∈ (node v).events →
    signedEnv.message.beaconBlockRoot = r →
    tx ∉ txs signedEnv.message.payload ∧ ¬ isValidOmission signedEnv.message.payload tx
  /-- The list carries the key of the committee. -/
  key : il.inclusionListCommitteeRoot = htr committee
  /-- The send time is in slot `N - 1`. -/
  sendLo : slotStartMs g (rb.slot - 1).toNat ≤ tSend
  /-- The list arrives before the IL due time of slot `N - 1`. -/
  sendHi : tSend + Δ < slotStartMs g (rb.slot - 1).toNat + ilDueMs.toNat
  /-- The arrival time is in the range of `secondsToMilliseconds`. -/
  sendSec : (tSend + Δ) / 1000 ≤ maxMsSeconds
  /-- The slot length is a whole number of seconds. -/
  slotSec : 1000 ∣ slotDurationMs.toNat
  /-- The IL due time is inside the slot. -/
  due : ilDueMs.toNat ≤ slotDurationMs.toNat
  /-- The list holds `tx`. -/
  listed : tx ∈ il.transactions.toArray
  /-- The wall time of each first-slot run is in the range of `secondsToMilliseconds`. -/
  wallSec : ∀ v, honest v → (run v (raceLo rb)).wall / 1000 ≤ maxMsSeconds

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] in
include hw in
/-- The honest heads of slot `N + 1` avoid `full r`, or a root collision exists. This is
`RaceSetting.first`.

The head run of slot `raceLo rb` gives the prefix, the store, and the `getHead` run. Its
current slot puts the wall time in slot `N + 1` (`slot_window_of_getCurrentSlot`). The anchor
store gives the empty IL store and `SlotInv`. Then `honestNode_head_avoids_full` applies. -/
theorem RaceSetting.Core.first_of_decision {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {hi : Nat} {jst : BeaconState} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {g : UInt64} {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {il : InclusionList} {tSend Δ : Nat} {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hset : RaceSetting.Core honest node run r rb hi jst nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g committee il tSend Δ txs isValidOmission tx)
    (hlohi : raceLo rb ≤ hi) :
    RootCollision ∨ ∀ v, honest v →
      ¬ NodeBelow (run v (raceLo rb)).store (.full r) (run v (raceLo rb)).head := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  refine Or.inr fun v hv => ?_
  have hN := hset.nodeOk v hv
  have hQ := hset.runOk v hv (raceLo rb) (Nat.le_refl _) hlohi
  obtain ⟨rest, hsplit⟩ := hQ.isPrefix
  obtain ⟨cs, hcs, hcur⟩ := hQ.slot
  obtain ⟨jb, hj, hjslot⟩ := hQ.justified
  obtain ⟨s', hrun⟩ := hQ.headRun
  have hgs : (node v).seed.genesisTime = g := hdec.genesis v hv
  have hg : (run v (raceLo rb)).store.genesisTime = (node v).seed.genesisTime :=
    hQ.trace.genesisTime
  -- The current slot `N + 1` is a `Slot`, so the slot after `rb` does not wrap.
  have hnext : rb.slot.toNat + 1 < 2 ^ 64 := by
    have := cs.toNat_lt
    unfold raceLo at hcs
    omega
  -- The wall time of the run lies in slot `N + 1`.
  have hDpos : 0 < slotDurationMs.toNat := pos_of_window _ _ _ _ _ hdec.sendLo hdec.sendHi hdec.due
  obtain ⟨hwlo, hwhi⟩ := slot_window_of_getCurrentSlot _ _ _ cs _ hcur hQ.time hdec.slotSec hDpos
  rw [hcs, hg] at hwlo hwhi
  unfold raceLo at hwlo hwhi
  rcases honestNode_head_avoids_full hw hdec.el hN.clocked
      (getForkchoiceStore_ilStore _ _ _ hN.anchorStore) (hdec.root v hv) (hdec.answer0 v hv)
      (hdec.payload0 v hv) (hdec.list v hv) hdec.key (by rw [hgs]; exact hdec.sendLo)
      (by rw [hgs]; exact hdec.sendHi) hdec.sendSec hdec.slotSec hdec.due hdec.listed
      (hdec.omits v hv) (SlotInv.anchor _ _ _ hN.anchorStore hN.anchorSelf) hN.noAnchorParent
      (run v (raceLo rb)).events rest hsplit hQ.trace hQ.time hwlo hwhi (hdec.wallSec v hv)
      hnext hj hjslot _ s' _ hrun with h | h
  · exact h
  · exact absurd h hcol

include hw in
/-- Tier T2 on the executable spec, with the decision slot and the count discharged. Take the
block `rb` at `r`, of slot `N`, and the window of slots `N + 1 .. hi`. Assume
`RaceSetting.Core`, the premises of tier T1 (`DecisionSetting`), and the committee conditions
(`RaceCommittees`). Then every honest head of the window lies below `empty r` and not below
`full r`, or a root collision exists.

`first_of_decision` gives `RaceSetting.first`, and `RaceCommittees.count` gives the counting
inequality. Then `race_empty_persists_exec` applies. An empty window needs neither. -/
theorem race_empty_persists_composed {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {hi : Nat} {jst : BeaconState} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {g : UInt64} {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {il : InclusionList} {tSend Δ : Nat} {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hset : RaceSetting.Core honest node run r rb hi jst nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g committee il tSend Δ txs isValidOmission tx)
    (hcomm : RaceCommittees jst honestOf committees (raceLo rb) hi) :
    RootCollision ∨ ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi →
      NodeBelow (run v t).store (.empty r) (run v t).head ∧
        ¬ NodeBelow (run v t).store (.full r) (run v t).head := by
  by_cases hlohi : raceLo rb ≤ hi
  · rcases hset.first_of_decision hw hdec hlohi with hcol | hfirst
    · exact Or.inl hcol
    · exact race_empty_persists_exec hw { toCore := hset, first := hfirst } hcomm.count
  · exact Or.inr fun _ _ t hlo hhi => absurd (Nat.le_trans hlo hhi) hlohi

end Decision

end EthCLSpecs.Proofs.Heze
