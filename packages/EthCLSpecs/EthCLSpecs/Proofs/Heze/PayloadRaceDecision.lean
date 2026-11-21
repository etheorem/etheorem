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
  [LawfulFcMap map (EthCLSpecs.Heze.Slot × Root)]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The premises of tier T1 at the honest nodes of slot `N + 1`, for the block `rb` at `r`.
An honest member of the IL committee of slot `N - 1` under the dependent root `dr` sends the
list `il` at `tSend`. The list reaches every honest node within `Δ`, before the IL due time
`due` of slot `N - 1`. Every envelope for `r` at an honest node omits `tx`, with no valid
omission under the EL rule. -/
structure DecisionSetting {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (g : UInt64) (dr : Root)
    (il : InclusionList) (tSend Δ : Nat) (due : UInt64)
    (txs : ExecutionPayload → Array Transaction)
    (isValidOmission : ExecutionPayload → Transaction → Prop) (tx : Transaction) : Prop where
  /-- The EL answers by the inclusion-list rule. -/
  el : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs isValidOmission
  /-- The honest nodes share the genesis time `g`. -/
  genesis : ∀ v, honest v → (node v).seed.genesisTimeMs = g
  /-- The stores of each honest node agree on the block at `r` and on the dependent root. -/
  root : ∀ v, honest v → RootFacts (node v).seed (node v).events r rb.slot dr
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
  /-- The list is for slot `N - 1` under the dependent root `dr`. -/
  key : ilKey il = (rb.slot - 1, dr)
  /-- The send time is in slot `N - 1`. -/
  sendLo : slotStartMs g (rb.slot - 1).toNat ≤ tSend
  /-- The list arrives before the IL due time of slot `N - 1`. -/
  sendHi : tSend + Δ < slotStartMs g (rb.slot - 1).toNat + due.toNat
  /-- The slot length is positive. -/
  slotPos : 0 < slotDurationMs.toNat
  /-- `due` is the IL due time. -/
  dueOk : EthCLSpecs.Heze.getInclusionListDueMs = .ok due
  /-- The IL due time is inside the slot. -/
  dueLe : due.toNat ≤ slotDurationMs.toNat
  /-- The list holds `tx`. -/
  listed : tx ∈ il.transactions.toArray

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

omit [LawfulFcMap map Checkpoint] in
include hw in
/-- **The head of one honest node at slot `N + 1` avoids `full r`**, or a root collision exists.
The head run of slot `raceLo rb` has a justified block no later than `rb`, and `empty r` is
viable beside `full r` there.

The head run gives the prefix, the store, and the `getHead` run. Its current slot puts the wall
time in slot `N + 1` (`slot_window_of_getCurrentSlot`). The anchor store gives the empty IL
store and `SlotInv`. Then `honestNode_head_avoids_full` applies. -/
theorem DecisionSetting.head_avoids_full {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {g : UInt64} {dr : Root} {il : InclusionList} {tSend Δ : Nat} {due : UInt64}
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hdec : DecisionSetting honest node run r rb g dr il tSend Δ due txs isValidOmission tx)
    {v : Node} (hv : honest v) (hN : (node v).Honest rb)
    (hQ : (run v (raceLo rb)).Core (node v) (raceLo rb)) {jb : BeaconBlock}
    (hj : FcMap.lookup (run v (raceLo rb)).store.blocks
      (run v (raceLo rb)).store.justifiedCheckpoint.root = some jb)
    (hjslot : jb.slot ≤ rb.slot)
    (hviable0 : EmptyViableWithFull (run v (raceLo rb)).store r) :
    RootCollision ∨
      ¬ NodeBelow (run v (raceLo rb)).store (.full r) (run v (raceLo rb)).head := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  refine Or.inr ?_
  obtain ⟨rest, hsplit⟩ := hQ.isPrefix
  obtain ⟨cs, hcs, hcur⟩ := hQ.slot
  obtain ⟨s', hrun⟩ := hQ.headRun
  have hgs : (node v).seed.genesisTimeMs = g := hdec.genesis v hv
  have hg : (run v (raceLo rb)).store.genesisTimeMs = (node v).seed.genesisTimeMs :=
    hQ.trace.genesisTime
  -- The current slot `N + 1` is a `Slot`, so the slot after `rb` does not wrap.
  have hnext : rb.slot.toNat + 1 < 2 ^ 64 := by
    have := cs.toNat_lt
    unfold raceLo at hcs
    omega
  -- The wall time of the run lies in slot `N + 1`.
  obtain ⟨hwlo, hwhi⟩ := slot_window_of_getCurrentSlot _ _ _ cs _ hcur hQ.time hdec.slotPos
  rw [hcs, hg] at hwlo hwhi
  unfold raceLo at hwlo hwhi
  rcases honestNode_head_avoids_full hw hdec.el hN.clocked
      (getForkchoiceStore_ilStore _ _ _ hN.anchorStore) (hdec.root v hv) (hdec.answer0 v hv)
      (hdec.payload0 v hv) (hdec.list v hv) hdec.key (by rw [hgs]; exact hdec.sendLo)
      (by rw [hgs]; exact hdec.sendHi) hdec.slotPos hdec.dueOk hdec.dueLe hdec.listed
      (hdec.omits v hv) (SlotInv.anchor _ _ _ hN.anchorStore hN.anchorSelf) hN.noAnchorParent
      (run v (raceLo rb)).events rest hsplit hQ.trace hQ.time hwlo hwhi
      hnext hj hjslot hviable0 _ s' _ hrun with h | h
  · exact h
  · exact absurd h hcol

omit [LawfulFcMap map Checkpoint] in
include hw in
/-- The honest heads of slot `N + 1` avoid `full r`, or a root collision exists. This is
`RaceSetting.first`: `DecisionSetting.head_avoids_full` at each honest node. -/
theorem RaceSetting.Core.first_of_decision {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {hi : Nat} {jst : BeaconState} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {g : UInt64} {dr : Root} {il : InclusionList} {tSend Δ : Nat} {due : UInt64}
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hset : RaceSetting.Core honest node run r rb hi jst nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g dr il tSend Δ due txs isValidOmission tx)
    (hlohi : raceLo rb ≤ hi)
    (hviable0 : ∀ v, honest v → EmptyViableWithFull (run v (raceLo rb)).store r) :
    RootCollision ∨ ∀ v, honest v →
      ¬ NodeBelow (run v (raceLo rb)).store (.full r) (run v (raceLo rb)).head := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  refine Or.inr fun v hv => ?_
  have hQ := hset.runOk v hv (raceLo rb) (Nat.le_refl _) hlohi
  obtain ⟨jb, hj, hjslot⟩ := hQ.justified
  exact (hdec.head_avoids_full hw hv (hset.nodeOk v hv) hQ.toCore hj hjslot
    (hviable0 v hv)).resolve_left hcol

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
    {g : UInt64} {dr : Root} {il : InclusionList} {tSend Δ : Nat} {due : UInt64}
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hset : RaceSetting.Core honest node run r rb hi jst nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g dr il tSend Δ due txs isValidOmission tx)
    (hcomm : RaceCommittees jst honestOf committees (raceLo rb) hi)
    (hviable0 : ∀ v, honest v → EmptyViableWithFull (run v (raceLo rb)).store r)
    (hviable : ∀ s, raceLo rb < s → s ≤ hi →
      (∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
        NodeBelow (run u t).store (.empty r) (run u t).head) →
      ∀ v, honest v → EmptyViableWithFull (run v s).store r) :
    RootCollision ∨ ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi →
      NodeBelow (run v t).store (.empty r) (run v t).head ∧
        ¬ NodeBelow (run v t).store (.full r) (run v t).head := by
  by_cases hlohi : raceLo rb ≤ hi
  · rcases hset.first_of_decision hw hdec hlohi hviable0 with hcol | hfirst
    · exact Or.inl hcol
    · exact race_empty_persists_exec hw { toCore := hset, first := hfirst } hcomm.count hviable
  · exact Or.inr fun _ _ t hlo hhi => absurd (Nat.le_trans hlo hhi) hlohi

end Decision

end EthCLSpecs.Proofs.Heze
