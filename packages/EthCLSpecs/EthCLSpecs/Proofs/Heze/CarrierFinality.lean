import EthCLSpecs.Proofs.Heze.VoteStep

/-!
# `EthCLSpecs.Proofs.Heze.CarrierFinality`: the censored payload is final, from a carrier chain

This module holds the two composed results of the window. They have three sets of premises:

- the window setting (`FinalitySetting`)
- the inclusion-list decision (`DecisionSetting`)
- a vote carrier chain on the EMPTY side (`CarrierWindow`)

The window induction (`heads_avoid_full_upto`) takes three steps. These premises give each one:

- EMPTY `r` stays viable beside FULL `r` (`viableStep_of_carrier`).
- The honest votes of each slot are on the EMPTY side (`CarrierWindow.voteStep`).
- EMPTY `r` is ahead of FULL `r` on weight (`FinalitySetting.raceAhead`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun LawfulFcMap)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex ExecutionPayload Transaction ExecutionRequests Slot AttestationData
  SignedBeaconBlock)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

section Final
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- **The censored payload is final.** Take the block `rb` at `r`, of slot `N`, and an honest
inclusion list of slot `N - 1` whose transaction `tx` every envelope for `r` at an honest node
leaves out (`DecisionSetting`). Take the window premises (`FinalitySetting`) and a vote carrier
chain `H` on the EMPTY side (`CarrierWindow`). `H` has a block after `rb` no later than the first
slot of `E₁`. Every honest node receives the last block of `H` in `E₁ + 3` (`LastDelivered`).
Then every honest head of the window avoids FULL `r`.

Take a later store of an honest node. It ends a trace from the store at the end of the window,
with no block at the parent root of the anchor and no zero state root. Before the first slot
of epoch `max (e₀ + 2) 3`, where `e₀` is the anchor epoch, its ancestor paths agree with those
of the end store. The checkpoints justified from the anchor lie on that prefix. The accountable
form needs both chains to share them (`honestNodes_accountable`). The store meets the totals
premise. Then its head avoids FULL `r`, or there is slashing evidence, or two blocks or
headers share a root.

The honest heads need not follow the carrier chain. The block of `H` after `rb` keeps the
finalized root off `r` (`CarrierWindow.finRoot_ne`). `live` gives that block when `E₁` is two
epochs past `rb` (`CarrierWindow.early_block`). At `E₁ = epoch(rb) + 1` the conclusion fails
without it, because `included` lets `H` place the votes of each epoch only in the next epoch.
At the end of `E₁ + 3` only the rule `all(bits[1:4])` fires (`phase0/beacon-chain.md:1992`).
That rule finalizes `E₁`. The block root of `E₁` is `r` when `H` has no block in
`(rb.slot, E₁ * SLOTS_PER_EPOCH]`.

Proof: `censored_payload_final` applies, with its premises from these lemmas:

- the first slot: `FinalitySetting.first_of_decision`
- the honest targets from `E₁`: `FinalitySetting.early`
- the finalizing chain: `CarrierWindow.chain`
- the viability of EMPTY `r`: `viableStep_of_carrier`
- the honest votes: `CarrierWindow.voteStep`
- the weight: `FinalitySetting.raceAhead` -/
theorem censored_payload_final_carrier [LawfulFcMap map (Slot × Root)] {Node : Type}
    {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
    {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}
    {g : UInt64} {dr : Root} {il : EthCLSpecs.Heze.InclusionList} {tSend Δ : Nat} {due : UInt64}
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g dr il tSend Δ due txs isValidOmission tx)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hb0 : ∃ b ∈ blocksOf stepsH, rb.slot.toNat < b.slot.toNat ∧
      b.slot.toNat ≤ E₁ * slotsPerEpoch)
    (hlast : LastDelivered honest node run A E₁ hi stepsH) :
    RootCollision ∨
      ((∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
          ¬ NodeBelow (run v t).store (.full r) (run v t).head) ∧
        ∀ v, honest v → ∀ (es : List TraceEvent)
          (arr : List (EthCLSpecs.Heze.SignedInclusionList × Bool))
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
          (EthCLSpecs.Heze.getHead (StoreTransition := ForkChoiceStoreRun (Store map)) s').run
            runner = .ok (head, t) →
          ¬ NodeBelow s' (.full r) head ∨
          ∃ (st₀ : BeaconState) (p₁ r₁ p₂ r₂ : List ChainStep)
            (pairs : List (EthCLSpecs.Heze.IndexedAttestation × EthCLSpecs.Heze.IndexedAttestation)),
            ChainRun (2 ^ 64 - 1) p₁ A st₀ ∧ ChainRun (2 ^ 64 - 1) p₂ A st₀ ∧
            SlashingEvidence st₀ (OnRun (2 ^ 64 - 1) A (p₁ ++ r₁))
              (OnRun (2 ^ 64 - 1) A (p₂ ++ r₂))
              (runDrift (2 ^ 64 - 1) st₀ r₁) (runDrift (2 ^ 64 - 1) st₀ r₂) pairs) := by
  by_cases hcol : RootCollision
  · exact .inl hcol
  rcases hset.first_of_decision hw hdec with h | hfirst
  · exact .inl h
  exact censored_payload_final hw hset hfirst (hset.early hw hcol)
    (hH.finRoot_ne hw hset hcol hb0) (hH.chain hw hset hlast) (viableStep_of_carrier hw hset hH hcol)
    (hH.voteStep hw hset) (hset.raceAhead hw)

include hw in
/-- **The censored payload stays off every honest head of the window.** The honest inclusion
list of slot `N - 1` carries `tx`, and every envelope for `r` leaves it out
(`DecisionSetting`). Under `FinalitySetting`, a vote carrier chain on the EMPTY side
(`CarrierWindow`) carries the honest votes of each epoch from the epoch before `rb`. Then a root
collision exists, or every honest head from slot `N + 1` to `finSlot E₁` lies below EMPTY `r`
and is not at or below FULL `r`.

Without the carrier chain the conclusion can fail. Take an epoch `e` whose honest votes target
`r`, and no block on the EMPTY side that carries them. Then the FULL side alone justifies
`(e, r)`. Two epochs later the viability filter drops the EMPTY leaves, and FULL `r` becomes
the head. The votes of the epoch two before `rb` on `H` matter too. Without them, a side branch
can leave no leaf viable in the epoch of `rb`. Then an honest node with no validators reaches
FULL `r`.

The honest heads need not follow the carrier chain. The theorem takes no premise on re-orgs. Its
only premises on the honest heads are those of the window setting.

Proof: the window induction (`heads_avoid_full_upto`) runs up to `finSlot E₁`. It shows that no
honest head is at or below FULL `r`, and that the honest votes are on the EMPTY side. Then each
honest head lies below EMPTY `r` (`CarrierWindow.head_window`). -/
theorem censored_payload_avoided [LawfulFcMap map (Slot × Root)] {Node : Type}
    {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
    {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}
    {g : UInt64} {dr : Root} {il : EthCLSpecs.Heze.InclusionList} {tSend Δ : Nat} {due : UInt64}
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g dr il tSend Δ due txs isValidOmission tx)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR) :
    RootCollision ∨ ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ →
      NodeBelow (run v t).store (.empty r) (run v t).head ∧
        ¬ NodeBelow (run v t).store (.full r) (run v t).head := by
  by_cases hcol : RootCollision
  · exact .inl hcol
  rcases hset.first_of_decision hw hdec with h | hfirst
  · exact .inl h
  rcases heads_avoid_full_upto hw hset hfirst (Nat.le_refl _)
      (viableStep_of_carrier hw hset hH hcol) (hH.voteStep hw hset) (hset.raceAhead hw) with
    h | ⟨hNF, hV⟩
  · exact .inl h
  refine .inr fun v hv t hlo ht => ?_
  have hN := hNF v hv t hlo (Nat.lt_succ_of_le ht)
  have hVt : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf t :=
    fun i hi d hd hdlo hdt => hV i hi d hd hdlo (by omega)
  exact ⟨hH.head_window hw hset hcol hv hlo ht hVt hN, hN⟩

end Final

end EthCLSpecs.Proofs.Heze
