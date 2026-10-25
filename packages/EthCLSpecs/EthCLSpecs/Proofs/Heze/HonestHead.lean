import EthCLSpecs.Proofs.Heze.NodeViews

/-!
# `EthCLSpecs.Proofs.Heze.HonestHead`: the head of an honest node in slot `n + 1`

`NodeViews.lean` proves that an honest node never holds the answer `true` at the block
root `r` of slot `n`, when every envelope for `r` omits a transaction of the honest list.
This module turns that answer into a fact about the head. Take a store of the honest
trace in slot `n + 1`. A `getHead` run on it returns a head that is not the FULL node of
`r` and not below it (`honestNode_head_avoids_full`).

## Two cases

- **The node holds the block at `r`.** `getHead_run_avoids_full` (`HeadAvoidsFull.lean`)
  needs four facts at the store. The block at `r` comes from `RootFacts`. The current slot
  is `n + 1` by the wall clock (`getCurrentSlot_run_eq_of_window`, `ClockedTrace.lean`). A
  verified payload at `r` has an answer (`NodeTrace.answer_isSome_of_payload`), and the
  answer is not `true` (`honestNode_answer_ne_true`), so it is `false`. The justified block
  has a slot no greater than `n`, so its pending node is not below the FULL node of `r`
  (`SlotInv.justified_not_below`).
- **The node lacks the block at `r`.** Every edge into the pending node of `r` comes from
  the block at `r`, and the walk starts at the justified block, which the store holds. So
  the walk never reaches the pending node of `r`, and so never the FULL node
  (`getHead_run_avoids_full_of_no_block`, `HeadAvoidsFull.lean`). This case needs no
  hypothesis that the block reaches the node.

`SlotInv` along the trace (`NodeTrace.slotInv`, `SlotsIncrease.lean`) can fail only on a
root collision. So the theorem concludes the head fact or `RootCollision`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap LawfulInclusionList)
open EthCLSpecs.Heze (Preset Config Store State Root Slot ForkChoiceNode BeaconBlock
  InclusionList SignedInclusionList SignedExecutionPayloadEnvelope ExecutionPayload
  ExecutionRequests Transaction ValidatorIndex getHead isPayloadVerified)

/-- The slot after `n`, in `UInt64` and in `Nat`, when it does not wrap. -/
theorem slot_succ_toNat (n : UInt64) (hnext : n.toNat + 1 < 2 ^ 64) :
    (n + 1).toNat = n.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hnext]

section Trace
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability]

/-- A payload at `r` comes with an answer at `r`, along a trace from a seed where it does.
Only the envelope handler writes either map at `r`, and it writes both. -/
theorem NodeTrace.answer_isSome_of_payload {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (r : Root)
    (h0 : (FcMap.lookup s0.payloads r).isSome →
      (FcMap.lookup s0.payloadInclusionListSatisfaction r).isSome) :
    (FcMap.lookup s.payloads r).isSome →
      (FcMap.lookup s.payloadInclusionListSatisfaction r).isSome := by
  induction h with
  | nil => exact h0
  | @handler events arrs prev post e _ hrun ih =>
    by_cases hr : ∃ signedEnv, e = .envelope signedEnv ∧ signedEnv.message.beaconBlockRoot = r
    · obtain ⟨signedEnv, rfl, hroot⟩ := hr
      obtain ⟨ilTxs, hans⟩ := onExecutionPayloadEnvelope_run_recorded signedEnv prev post hrun
      rw [hroot] at hans
      intro _
      rw [hans]
      rfl
    · have hnot : e.NotEnvelopeAt r := by
        cases e with
        | envelope signedEnv => exact fun h => hr ⟨signedEnv, rfl, h⟩
        | _ => trivial
      have hkeep := HandlerEvent.run_keeps_payloadAnswer r e hnot hrun
      injection hkeep with hp ha
      rw [hp, ha]
      exact ih
  | @inclusionList events arrs prev post signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

variable (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

open EthCLSpecs.Heze.Const (slotDurationMs)

include hw in
/-- The head of an honest node in slot `n + 1` avoids the FULL node of `r` and every node
below it, or a root collision exists.

The node and the honest list `il` meet the hypotheses of `honestNode_answer_ne_true`, and
every envelope for `r` at the node omits `tx` with no valid omission. The seed holds no
payload at `r`, and it meets `SlotInv` for the anchor block `a`. No event is a block at
the parent root of `a`. The combine-width law `hw` gives the block-root lemma of
`SlotInv`. The send window of `il` has a positive length, so the slot length is positive
(`pos_of_window`).

The query store `m` follows the prefix `pre` of the trace. Its time is the wall time `w`
in whole seconds, and `w` lies in slot `n + 1`. The store holds the justified block `jb`,
with a slot no greater than `n`. -/
theorem honestNode_head_avoids_full
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × UInt64)} (hct : ClockedTrace s0 tevs arrivals s)
    (hseed : s0.inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty)
    {r : Root} {n : Slot}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    (hroot : RootFacts s0 tevs r n committee)
    (hanswer0 : FcMap.lookup s0.payloadInclusionListSatisfaction r = none)
    (hpayload0 : FcMap.lookup s0.payloads r = none)
    {il : InclusionList} {tSend Δ : Nat} (hil : HonestList tevs il tSend Δ)
    (hkey : il.inclusionListCommitteeRoot = htr committee)
    (hlo : slotStartMs s0.genesisTime (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs s0.genesisTime (n - 1).toNat + ilDueMs.toNat)
    (hsec : (tSend + Δ) / 1000 ≤ maxMsSeconds)
    (hDdiv : 1000 ∣ slotDurationMs.toNat)
    (hdue : ilDueMs.toNat ≤ slotDurationMs.toNat)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (homits : ∀ (signedEnv : SignedExecutionPayloadEnvelope) (w : Nat),
      (.handler (.envelope signedEnv), w) ∈ tevs → signedEnv.message.beaconBlockRoot = r →
      tx ∉ txs signedEnv.message.payload ∧ ¬ isValidOmission signedEnv.message.payload tx)
    {a : BeaconBlock} (hinv0 : SlotInv a s0)
    (hev : ∀ (e : HandlerEvent) (w : Nat), (.handler e, w) ∈ tevs → e.NotAtAnchorParent a)
    (pre rest : List (TraceEvent × Nat)) (hsplit : tevs = pre ++ rest)
    {arr : List (SignedInclusionList × UInt64)} {m : Store map}
    (hm : NodeTrace s0 (pre.map Prod.fst) arr m)
    {w : Nat} (htime : m.time.toNat = w / 1000)
    (hwlo : slotStartMs s0.genesisTime (n.toNat + 1) ≤ w)
    (hwhi : w < slotStartMs s0.genesisTime (n.toNat + 1 + 1))
    (hwsec : w / 1000 ≤ maxMsSeconds) (hnext : n.toNat + 1 < 2 ^ 64)
    {jb : BeaconBlock}
    (hj : FcMap.lookup m.blocks m.justifiedCheckpoint.root = some jb) (hjslot : jb.slot ≤ n)
    (runnerStore s' : Store map) (head : ForkChoiceNode)
    (hrun : (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) m).run runnerStore
      = .ok (head, s')) :
    ¬ NodeBelow m (.full r) head ∨ RootCollision := by
  have hDpos : 0 < slotDurationMs.toNat := pos_of_window _ _ _ _ _ hlo hhi hdue
  cases hb : FcMap.lookup m.blocks r with
  | none => exact Or.inl (getHead_run_avoids_full_of_no_block m r hb jb hj runnerStore s' head hrun)
  | some rb =>
    have hslot : rb.slot = n := hroot.block pre rest arr m rb hsplit hm hb
    -- The current slot is `n + 1`, by the wall clock.
    have hg : m.genesisTime = s0.genesisTime := hm.genesisTime
    obtain ⟨cs, hcs, hcur⟩ := getCurrentSlot_run_eq_of_window m m w (n.toNat + 1) htime
      hDdiv (hg ▸ hwlo) (hg ▸ hwhi) hwsec
    have hn1 := slot_succ_toNat n hnext
    have hcs' : cs = rb.slot + 1 := by
      rw [hslot]
      exact UInt64.toNat_inj.mp (hcs.trans hn1.symm)
    have hnoov : ¬ (rb.slot + 1 < rb.slot) := by
      rw [hslot, UInt64.lt_iff_toNat_lt, hn1]
      omega
    -- A verified payload has an answer, and the answer is not `true`.
    have hfull : isPayloadVerified m r = true →
        FcMap.lookup m.payloadInclusionListSatisfaction r = some false := by
      intro hv
      have hp : (FcMap.lookup m.payloads r).isSome := by
        rw [← LawfulFcMap.contains_eq_isSome_lookup]
        exact hv
      have ha := hm.answer_isSome_of_payload r (by rw [hpayload0]; simp) hp
      have hne := honestNode_answer_ne_true hel hct hseed hroot hanswer0 hil hkey hlo hhi hsec
        hDpos hDdiv hdue htx homits pre rest hsplit hm
      obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp ha
      rw [hb'] at hne ⊢
      cases b
      · rfl
      · exact absurd rfl hne
    -- `SlotInv` along the prefix, or a root collision.
    have hevpre : ∀ e, TraceEvent.handler e ∈ pre.map Prod.fst → e.NotAtAnchorParent a := by
      intro e he
      obtain ⟨x, hx, hx1⟩ := List.mem_map.mp he
      refine hev e x.2 ?_
      rw [hsplit, ← hx1]
      exact List.mem_append_left _ hx
    rcases hm.slotInv hw hinv0 hevpre with hinv | hcol
    · refine Or.inl (getHead_run_avoids_full m r rb hb (hcs' ▸ hcur) hnoov hfull ?_ runnerStore
        s' head hrun)
      exact hinv.justified_not_below hb hj (hslot ▸ hjslot)
    · exact Or.inr hcol

end Trace

end EthCLSpecs.Proofs.Heze
