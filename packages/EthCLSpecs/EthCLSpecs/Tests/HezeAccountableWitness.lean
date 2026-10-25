import EthCLSpecs.Tests.HezeFinalityWitness

/-!
# `EthCLSpecs.Tests.HezeAccountableWitness`: two finalized chains carry slashing evidence

`honestNodes_accountable` (`Proofs/Heze/Accountable.lean`) turns two conflicting finalized
checkpoints into `SlashingEvidence`. This module builds two chains at the minimal preset that
finalize conflicting checkpoints, and checks `SlashingEvidence` on them. So the conclusion of
the accountable form can hold on a real run of the spec.

## The scenario

- **Genesis and `r`.** The genesis state and block `r` of `HezeFinalityWitness.lean`: 32 active
  validators of `32 ETH`, and `r` at slot `24` with no votes.
- **The fork.** Chain 1 builds a block in each slot from `25` to `63` on the EMPTY edge of `r`.
  Chain 2 does the same on the FULL edge: the bid of its first block names the payload hash of
  `r`, and the block applies the payload of `r`.
- **The votes.** The validators `20` to `31` vote on both chains. The validators `0` to `9` vote
  on chain 1 only, and `10` to `19` on chain 2 only. Each chain has the votes of 22 of 32
  validators: `3 * 22 = 66 ≥ 64 = 2 * 32`.
- **Finality.** Each chain finalizes its own checkpoint of epoch `4` at slot `64`. The
  checkpoint of epoch `3` is `r` on both chains, so the first conflict is at epoch `4`.

## The evidence

Each pair comes from a slot of epoch `4` whose committee has a validator that votes on both
chains. The pair holds the indexed votes of that slot on chain 1 and on chain 2. The two votes have one
target epoch and two target roots, so they are slashable. The common validators hold
`12 / 32` of the stake at the state after `r`, above the third that the accountable form
promises. `process_attester_slashing` accepts each pair on the last state of chain 1.

The seams are those of `HezeNetworkWitness.lean`. Fires on `lake build EthCLSpecsTests`
(`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure)
open EthCLSpecs.Proofs.Heze

namespace EthCLSpecs.Tests.HezeAccountableWitness

open EthCLSpecs.Heze (Preset Config Store State Root BeaconState BeaconBlock BeaconBlockBody
  SignedBeaconBlock Attestation IndexedAttestation AttesterSlashing ValidatorIndex minimal
  minimalConfig getBeaconCommittee computeEpochAtSlot currentEpochOf getAttestingIndices)
open EthCLSpecs.Heze.Const (builderIndexSelfBuild g2PointAtInfinity)
open EthCLSpecs.Tests.HezeNetworkWitness (h2)
open EthCLSpecs.Tests.HezePaymentWitness (bidFor)
open EthCLSpecs.Tests.HezeFinalityWitness (genesisV attList)

local instance : Preset := minimal
local instance : HasherTag := pureHasherTag
local instance : Config := minimalConfig
local instance : CryptoBackend := CryptoBackend.verifyOff

/-- The validators `20` to `31` vote on both chains. -/
def adv (i : ValidatorIndex) : Bool := decide (20 ≤ i.toNat)

/-- The voters of chain `c`: the validators `0` to `9` on chain 1 (`false`), `10` to `19` on
chain 2 (`true`), and the validators of `adv` on both. -/
def onChain (c : Bool) (i : ValidatorIndex) : Bool :=
  adv i || (if c then decide (10 ≤ i.toNat) else decide (i.toNat < 10))

/-- Aggregation bits with a bit for each member of the committee `c` that passes `on`. -/
def bitsOn (on : ValidatorIndex → Bool) (c : Array ValidatorIndex) : SizzLean.Repr.Bitlist
    (EthCLSpecs.Heze.Const.maxValidatorsPerCommittee * EthCLSpecs.Heze.Const.maxCommitteesPerSlot) :=
  let a := c.map on
  if h : a.size ≤ _ then ⟨a, h⟩ else ⟨#[], by simp⟩

/-- The votes of `on` of the slot before `pre`, as `votesFor` of the finality witness. When
`getBeaconCommittee` fails, the committee is empty and the slot has no vote. -/
def votesOn (on : ValidatorIndex → Bool) (pre : State) : Array Attestation :=
  let t := sszGet pre slot - 1
  let c := (getBeaconCommittee pre t 0).toOption.getD #[]
  if !(c.any on) then #[] else
  let e := computeEpochAtSlot t
  let src := if e == currentEpochOf pre then sszGet pre currentJustifiedCheckpoint
    else sszGet pre previousJustifiedCheckpoint
  let tgt := match (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) pre e).run pre with
    | .ok (r, _) => r
    | .error _ => default
  #[{ aggregationBits := bitsOn on c
      data := { slot := t, index := 0, beaconBlockRoot := htr (sszGet pre latestBlockHeader),
                source := src, target := { epoch := e, root := tgt } }
      signature := default
      committeeBits := bitSet default 0 true }]

/-- The self-built block of slot `n` on `st` with the votes of `on`. When `full`, the bid names
the payload of the parent (`h2`), so the block builds on the FULL edge. -/
def blockOn (on : ValidatorIndex → Bool) (full : Bool) (st : BeaconState) (n : Nat) :
    Option (BeaconState × SignedBeaconBlock) :=
  match (EthCLSpecs.Heze.processSlots (StateTransition := HezeRun) (UInt64.ofNat n)).run
      (pureState st) with
  | .error _ => none
  | .ok ((), pre) =>
    let bid0 := { bidFor pre builderIndexSelfBuild 0 h2 with value := 0 }
    let bid := if full then { bid0 with parentBlockHash := h2 } else bid0
    let unsigned : BeaconBlock :=
      { (default : BeaconBlock) with
        slot := UInt64.ofNat n
        proposerIndex := EthCLSpecs.Heze.getBeaconProposerIndex pre
        parentRoot := htr (sszGet pre latestBlockHeader)
        body := { (default : BeaconBlockBody) with
          attestations := attList (votesOn on pre)
          signedExecutionPayloadBid := { message := bid, signature := g2PointAtInfinity } } }
    match (blockStep { message := unsigned, signature := default } false).run pre with
    | .error _ => none
    | .ok ((), post) =>
      some (post.view,
        { message := { unsigned with stateRoot := bytesToRoot (stateRoot post).1 },
          signature := default })

/-- The blocks at the slots `ns` on `st` with the votes of `on`. The first block builds on the
FULL edge when `full`. -/
def chainOn (on : ValidatorIndex → Bool) : Bool → List Nat → BeaconState →
    Option (BeaconState × List SignedBeaconBlock)
  | _, [], st => some (st, [])
  | full, n :: ns, st => do
    let (st1, b) ← blockOn on full st n
    let (st2, bs) ← chainOn on false ns st1
    pure (st2, b :: bs)

/-- Block `r` at slot `24` on genesis, with no votes, and the state after it. -/
def rPair : BeaconState × SignedBeaconBlock :=
  (blockOn (fun _ => false) false genesisV 24).getD (genesisV, default)

/-- The end state and the blocks of chain `c`, slots `25` to `63`. -/
def chainOf (c : Bool) : BeaconState × List SignedBeaconBlock :=
  (chainOn (onChain c) c ((List.range 39).map (· + 25)) rPair.1).getD (genesisV, [])

/-- Chain 1. A closed constant. -/
def chain1 : BeaconState × List SignedBeaconBlock := chainOf false

/-- Chain 2. -/
def chain2 : BeaconState × List SignedBeaconBlock := chainOf true

/-- The state of chain `c` at slot `64`, after the epoch transition. -/
def endOf (ch : BeaconState × List SignedBeaconBlock) : BeaconState :=
  match (EthCLSpecs.Heze.processSlots (StateTransition := HezeRun) 64).run (pureState ch.1) with
  | .ok ((), s) => s.view
  | .error _ => genesisV

/-- The indexed form of `att` on `st`: the sorted attesting indices, the data, the
signature. -/
def indexedOf (st : BeaconState) (att : Attestation) : Option IndexedAttestation :=
  match getAttestingIndices (pureState st) att with
  | .ok idx =>
    let s := idx.qsort (· < ·)
    if h : s.size ≤ EthCLSpecs.Heze.Const.maxValidatorsPerCommittee *
        EthCLSpecs.Heze.Const.maxCommitteesPerSlot then
      some
        { attestingIndices := ⟨s, h⟩
          data := att.data
          signature := att.signature }
    else none
  | .error _ => none

/-- The vote of slot `t` on chain `ch`: the first attestation of the block of slot `t + 1`. -/
def voteOf (ch : BeaconState × List SignedBeaconBlock) (t : Nat) : Option Attestation :=
  (ch.2[t + 1 - 25]?).bind fun sb => sb.message.body.attestations.toArray[0]?

/-- The pairs of epoch `4`: for each slot whose committee has a validator of `adv`, the indexed
votes of chain 1 and chain 2 of that slot. A closed constant. -/
def pairs : List (IndexedAttestation × IndexedAttestation) :=
  ((List.range 8).map (· + 32)).filterMap fun t => do
    let a1 ← voteOf chain1 t
    let a2 ← voteOf chain2 t
    let i1 ← indexedOf (endOf chain1) a1
    let i2 ← indexedOf (endOf chain2) a2
    if i1.attestingIndices.toArray.any (i2.attestingIndices.toArray.contains ·) then
      pure (i1, i2)
    else none

/-! ## The steps -/

/-- The steps to block `r`: slot steps to slot `24`, then block `r` with the result check. -/
def Wp : List ChainStep := List.replicate 23 .slot ++ [.slot, .block rPair.2 true]

/-- The steps of chain `ch` after `r`: the block of each slot from `25` to `63`, and a slot step
to slot `64`. -/
def restOf (ch : BeaconState × List SignedBeaconBlock) : List ChainStep :=
  ch.2.flatMap (fun b => [.slot, .block b true]) ++ [.slot]

/-- The steps of chain 1 after `r`. -/
def R1 : List ChainStep := restOf chain1

/-- The steps of chain 2 after `r`. -/
def R2 : List ChainStep := restOf chain2

/-- The states of chain 1 from genesis, or the empty list when the run fails. -/
def Ls1 : List BeaconState := (runStates (2 ^ 64 - 1) (Wp ++ R1) genesisV).getD []

/-- The states of chain 2 from genesis. -/
def Ls2 : List BeaconState := (runStates (2 ^ 64 - 1) (Wp ++ R2) genesisV).getD []

/-! ## The check -/

/-- The checks: both runs, `SlashingEvidence` at the state after `r` with no drift,
`process_attester_slashing` of each pair on the last state of chain 1, and the two finalized
checkpoints of epoch `4` with different roots. -/
def accChk : Bool :=
  Ls1.length == (Wp ++ R1).length + 1 &&
  Ls2.length == (Wp ++ R2).length + 1 &&
  (Ls1[Wp.length]?).any (fun st₀ => slashingB st₀ Ls1 Ls2 0 0 pairs) &&
  (Ls1[(Wp ++ R1).length]?).any (fun w₁ =>
    pairs.all (fun x => (runPure (EthCLSpecs.Heze.processAttesterSlashing
      (StateTransition := HezeRun) { attestation1 := x.1, attestation2 := x.2 }) w₁).toBool) &&
    decide (w₁.finalizedCheckpoint.epoch.toNat = 4) &&
    (Ls2[(Wp ++ R2).length]?).any (fun w₂ =>
      decide (w₂.finalizedCheckpoint.epoch.toNat = 4) &&
      decide (w₁.finalizedCheckpoint.root ≠ w₂.finalizedCheckpoint.root)))

set_option maxHeartbeats 0 in
/-- Every check passes. Lean counts the allocations of the compiled evaluation as heartbeats,
so this one declaration lifts the limit. -/
theorem accChk_ok : accChk = true := by native_decide

/-! ## The witness -/

/-- The states of a run, from a length check. -/
theorem runStates_of_length {W : List ChainStep} {L : List BeaconState}
    (hL : L = (runStates (2 ^ 64 - 1) W genesisV).getD []) (h : L.length = W.length + 1) :
    runStates (2 ^ 64 - 1) W genesisV = some L := by
  cases hr : runStates (2 ^ 64 - 1) W genesisV with
  | none =>
    rw [hr] at hL
    rw [hL] at h
    simp at h
  | some L' =>
    rw [hr] at hL
    rw [hL]
    rfl

/-- The state at `n` of a run, as a run of the first `n` steps. -/
theorem state_at {W : List ChainStep} {L : List BeaconState}
    (hL : runStates (2 ^ 64 - 1) W genesisV = some L) {n : Nat} (hn : n ≤ W.length)
    {u : BeaconState} (hu : L[n]? = some u) : ChainRun (2 ^ 64 - 1) (W.take n) genesisV u := by
  obtain ⟨u', hu', hrun⟩ := runStates_take hL n hn
  rw [hu] at hu'
  cases hu'
  exact hrun

/-- **The accountable witness.** Two chains share block `r` and fork after it: chain 1 on the
EMPTY edge of `r`, chain 2 on the FULL edge. Each finalizes its own checkpoint of epoch `4` at
slot `64`. The votes of epoch `4` give pairs of conflicting attestations, one from each chain.
The pairs meet `SlashingEvidence` at the state after `r`, with no drift. The 12 validators that
vote on both chains hold `12 / 32` of the stake, above a third. `process_attester_slashing`
accepts each pair on the last state of chain 1.

`native_decide` evaluates `accChk` (`accChk_ok`). The hasher is the pure-Lean one, so no FFI
equivalence axiom enters. -/
theorem accountableWitness :
    ∃ (st₀ w₁ w₂ : BeaconState) (p r₁ r₂ : List ChainStep)
      (prs : List (IndexedAttestation × IndexedAttestation)),
      ChainRun (2 ^ 64 - 1) p genesisV st₀ ∧
      ChainRun (2 ^ 64 - 1) (p ++ r₁) genesisV w₁ ∧ ChainRun (2 ^ 64 - 1) (p ++ r₂) genesisV w₂ ∧
      SlashingEvidence st₀ (OnRun (2 ^ 64 - 1) genesisV (p ++ r₁))
        (OnRun (2 ^ 64 - 1) genesisV (p ++ r₂)) 0 0 prs ∧
      (∀ x ∈ prs, ∃ st', runPure (EthCLSpecs.Heze.processAttesterSlashing
        (StateTransition := HezeRun) { attestation1 := x.1, attestation2 := x.2 }) w₁
          = .ok ((), st')) ∧
      w₁.finalizedCheckpoint.epoch.toNat = 4 ∧ w₂.finalizedCheckpoint.epoch.toNat = 4 ∧
      w₁.finalizedCheckpoint.root ≠ w₂.finalizedCheckpoint.root := by
  have h := accChk_ok
  simp only [accChk, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨hl1, hl2⟩, st₀, hst₀, hslash⟩, w₁, hw₁, ⟨hacc, hf1⟩, w₂, hw₂, hf2, hne⟩ := h
  have hL1 := runStates_of_length rfl hl1
  have hL2 := runStates_of_length rfl hl2
  have hp : ChainRun (2 ^ 64 - 1) Wp genesisV st₀ := by
    have := state_at hL1 (by simp) hst₀
    rwa [List.take_left] at this
  have hr1 : ChainRun (2 ^ 64 - 1) (Wp ++ R1) genesisV w₁ := by
    have := state_at hL1 (Nat.le_refl _) hw₁
    rwa [List.take_length] at this
  have hr2 : ChainRun (2 ^ 64 - 1) (Wp ++ R2) genesisV w₂ := by
    have := state_at hL2 (Nat.le_refl _) hw₂
    rwa [List.take_length] at this
  refine ⟨st₀, w₁, w₂, Wp, R1, R2, pairs, hp, hr1, hr2,
    SlashingEvidence.of_check hL1 hL2 hslash, fun x hx => ?_, hf1, hf2, hne⟩
  have := hacc x hx
  revert this
  cases runPure (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun)
    { attestation1 := x.1, attestation2 := x.2 }) w₁ with
  | ok q => exact fun _ => ⟨q.2, rfl⟩
  | error e => simp [Except.toBool]

end EthCLSpecs.Tests.HezeAccountableWitness
