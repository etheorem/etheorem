import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner
import SizzLeanBench.Fulu

/-!
# Scenario S7: Realistic Fulu BeaconState state-transition

The most production-shaped scenario in the bench. Targets the
local `SizzLeanBench.Fulu.BeaconState` reference fixture (mainnet
preset, ~1024 validators). Every per-iteration shot simulates a
short block-by-block state-transition sequence, touching most
field shapes the BeaconState container exposes:

* Basic scalars      : `slot`, `eth1DepositIndex`, etc.
* Sub-containers     : `latestBlockHeader`, checkpoints, `eth1Data`
* Fixed Vectors      : `blockRoots[k]`, `stateRoots[k]`,
                       `randaoMixes[k]`
* Composite SSZLists : `validators[i]`
* Basic-element SSZLists : `balances`, `inactivityScores` (whole-
                           list replacement; the cached macro
                           doesn't support packed-basic index
                           syntax)
* Whole-replacement  : `currentSyncCommittee` (every epoch)
* Bitvector         : `justificationBits` (every epoch)

The fixture is built **once outside the timed loop** and the
cached box is pre-warmed via one root walk so every timed
iteration starts from a fully-cached top. Each iteration runs
`SLOTS_PER_RUN` slots; every `SLOTS_PER_EPOCH = 32` slots triggers
an "epoch transition" with extra writes.

## Why this scenario differs from the synthetic ones

The S1–S6 scenarios use `ValidatorSet256` / `ValidatorSet16`
fixtures, a vector-of-containers shape. Those miss what makes a
real BeaconState heavy: 37 top-level fields of mixed shapes,
mainnet-preset constants (8K block-roots, 64K randao-mixes), and
a deep nested container surface. This row measures the cache's
behaviour on a top-level container an Ethereum consensus client
actually mutates.

## Why the bench-local copy of Fulu types

`SizzLeanBench.Fulu` holds a copy of the BeaconState shape; the
spec-accurate version lives in `LeanEthCS.Forks.Fulu`. The bench
copy keeps `SizzLeanBench` independent of LeanEthCS. `LeanEthCS`
already depends on `SizzLean`, and adding the reverse dependency
would close a cycle. The copy is a *reference fixture*, it
tracks the shape at the moment of writing and may drift; for
spec-accurate types use LeanEthCS.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SizzLeanBench.Scenarios.FuluStateTransition

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr
open SizzLeanBench.Runner
open SizzLeanBench.Fixtures (consume)
open SizzLeanBench.Fulu

private def NUM_VALIDATORS : Nat := 1024
private def SLOTS_PER_RUN  : Nat := 16

/-! ## Sub-container builders -/

private def saltRoot (s : UInt8) : Root := Vector.replicate 32 s
private def saltPubkey (s : UInt8) : BLSPubkey := Vector.replicate 48 (s + 0xa0)
private def saltCred (s : UInt8) : Bytes32 := Vector.replicate 32 (s + 0xc0)
private def zeroRoot : Root := Vector.replicate 32 0
private def zeroBytes32 : Bytes32 := Vector.replicate 32 0
private def zeroPubkey : BLSPubkey := Vector.replicate 48 0
private def zeroVersion : Version := Vector.replicate 4 0
private def zeroAddr : ExecutionAddress := Vector.replicate 20 0

private def mkValidator (i : Nat) : Validator :=
  { pubkey                     := saltPubkey (UInt8.ofNat (i &&& 0xff))
    withdrawalCredentials      := saltCred   (UInt8.ofNat ((i >>> 8) &&& 0xff))
    effectiveBalance           := 32000000000 + i.toUInt64
    slashed                    := false
    activationEligibilityEpoch := 0
    activationEpoch            := 0
    exitEpoch                  := 18446744073709551615
    withdrawableEpoch          := 18446744073709551615 }

private def mkCheckpoint (s : UInt8) : Checkpoint :=
  { epoch := s.toUInt64, root := saltRoot s }

private def mkFork : Fork :=
  { previousVersion := zeroVersion, currentVersion := zeroVersion, epoch := 0 }

private def mkBlockHeader (s : UInt8) : BeaconBlockHeader :=
  { slot          := s.toUInt64
    proposerIndex := 0
    parentRoot    := saltRoot s
    stateRoot     := saltRoot s
    bodyRoot      := saltRoot s }

private def mkEth1Data (s : UInt8) : Eth1Data :=
  { depositRoot := saltRoot s, depositCount := 0, blockHash := saltRoot s }

private def mkSyncCommittee (s : UInt8) : SyncCommittee :=
  { pubkeys         := Vector.ofFn fun (i : Fin 512) => saltPubkey (s + UInt8.ofNat i.val)
    aggregatePubkey := saltPubkey (s + 0x77) }

private def mkExecHeader : ExecutionPayloadHeader :=
  { parentHash       := zeroRoot
    feeRecipient     := zeroAddr
    stateRoot        := zeroBytes32
    receiptsRoot     := zeroBytes32
    logsBloom        := Vector.replicate 256 0
    prevRandao       := zeroBytes32
    blockNumber      := 0
    gasLimit         := 30000000
    gasUsed          := 0
    timestamp        := 1700000000
    extraData        := ⟨#[], by decide⟩
    baseFeePerGas    := BitVec.ofNat 256 1000000000
    blockHash        := zeroRoot
    transactionsRoot := zeroRoot
    withdrawalsRoot  := zeroRoot
    blobGasUsed      := 0
    excessBlobGas    := 0 }

private def mkSSZList {α : Type} {cap : Nat} (n : Nat) (h : n ≤ cap)
    (f : Nat → α) : SSZList α cap :=
  ⟨Array.ofFn (n := n) (fun (i : Fin n) => f i.val),
   by simp [Array.size_ofFn]; exact h⟩

/-! ## Fixture builder

A mainnet-preset Fulu `BeaconState` with `NUM_VALIDATORS`
validators, matching-sized balances / participation / inactivity
lists, and sane defaults for everything else. -/
private def mkBeaconState (salt : UInt8) : BeaconState :=
  let validators : SSZList Validator 1099511627776 :=
    mkSSZList NUM_VALIDATORS (by decide) (fun i => mkValidator (i + salt.toNat))
  let balances : SSZList Gwei 1099511627776 :=
    mkSSZList NUM_VALIDATORS (by decide) (fun i => 32000000000 + i.toUInt64)
  let participation : SSZList ParticipationFlags 1099511627776 :=
    mkSSZList NUM_VALIDATORS (by decide) (fun _ => 0)
  let inactivity : SSZList UInt64 1099511627776 :=
    mkSSZList NUM_VALIDATORS (by decide) (fun _ => 0)
  let emptyHistoricalRoots : SSZList Root 16777216 := ⟨#[], by decide⟩
  let emptyEth1DataVotes : SSZList Eth1Data 2048 := ⟨#[], by decide⟩
  let emptyHistoricalSummaries : SSZList HistoricalSummary 16777216 := ⟨#[], by decide⟩
  let emptyPendingDeposits : SSZList PendingDeposit 134217728 := ⟨#[], by decide⟩
  let emptyPendingPW : SSZList PendingPartialWithdrawal 134217728 := ⟨#[], by decide⟩
  let emptyPendingC : SSZList PendingConsolidation 262144 := ⟨#[], by decide⟩
  { genesisTime                   := 0
    genesisValidatorsRoot         := saltRoot salt
    slot                          := 0
    fork                          := mkFork
    latestBlockHeader             := mkBlockHeader salt
    blockRoots                    := Vector.replicate 8192 zeroRoot
    stateRoots                    := Vector.replicate 8192 zeroRoot
    historicalRoots               := emptyHistoricalRoots
    eth1Data                      := mkEth1Data salt
    eth1DataVotes                 := emptyEth1DataVotes
    eth1DepositIndex              := 0
    validators                    := validators
    balances                      := balances
    randaoMixes                   := Vector.replicate 65536 zeroBytes32
    slashings                     := Vector.replicate 8192 0
    previousEpochParticipation    := participation
    currentEpochParticipation     := participation
    justificationBits             := { data := BitVec.ofNat 4 0 }
    previousJustifiedCheckpoint   := mkCheckpoint salt
    currentJustifiedCheckpoint    := mkCheckpoint salt
    finalizedCheckpoint           := mkCheckpoint salt
    inactivityScores              := inactivity
    currentSyncCommittee          := mkSyncCommittee salt
    nextSyncCommittee             := mkSyncCommittee (salt + 1)
    latestExecutionPayloadHeader  := mkExecHeader
    nextWithdrawalIndex           := 0
    nextWithdrawalValidatorIndex  := 0
    historicalSummaries           := emptyHistoricalSummaries
    depositRequestsStartIndex     := 0
    depositBalanceToConsume       := 0
    exitBalanceToConsume          := 0
    earliestExitEpoch             := 0
    consolidationBalanceToConsume := 0
    earliestConsolidationEpoch    := 0
    pendingDeposits               := emptyPendingDeposits
    pendingPartialWithdrawals     := emptyPendingPW
    pendingConsolidations         := emptyPendingC
    proposerLookahead             := Vector.ofFn (fun (i : Fin 64) => i.val.toUInt64) }

/-! ## The per-iteration workload

Simulates `SLOTS_PER_RUN` consecutive slots, touching many fields
per slot. Every 32nd slot triggers epoch-boundary writes
(sync-committee rotation, justification bits, checkpoint). The
final root closes each iteration.

`box.serialize` is intentionally omitted from the per-slot loop:
the current `SSZ.serialize` runs around 1 MB/s on a ~3 MB mainnet
BeaconState, calling it 16 times per iteration would dominate
the timing and obscure the cache-vs-pure comparison. -/
private def runTransitions {H : Type} [Hasher H] [SSZRepr BeaconState]
    (sink : IO.Ref Nat) (initialBox : SSZ.Box H BeaconState) :
    IO Unit := do
  let mut box : SSZ.Box H BeaconState := initialBox
  for s in [:SLOTS_PER_RUN] do
    let slotMark : UInt64 := UInt64.ofNat s + 1
    let valIdx0 : Nat := s % NUM_VALIDATORS
    let valIdx1 : Nat := (s * 7 + 11) % NUM_VALIDATORS
    let valIdx2 : Nat := (s * 13 + 23) % NUM_VALIDATORS
    let oldV0 := box.view.validators.get! valIdx0
    let newV0 : Validator := { oldV0 with effectiveBalance := 32000000000 + slotMark }
    let oldV1 := box.view.validators.get! valIdx1
    let newV1 : Validator := { oldV1 with slashed := true, exitEpoch := slotMark }
    let oldV2 := box.view.validators.get! valIdx2
    let newV2 : Validator :=
      { oldV2 with withdrawableEpoch := slotMark + 256 }
    let newBalances     := box.view.balances.set! valIdx0 (32000000000 + slotMark)
                                            |>.set! valIdx1 0
    let newInactivity   := box.view.inactivityScores.set! valIdx0 (UInt64.ofNat s)
    let newLookahead    := box.view.proposerLookahead.set (s % 64) (UInt64.ofNat valIdx0)
      (Nat.mod_lt _ (by decide))
    box := sszUpdate box with
      slot                          := slotMark,
      latestBlockHeader.slot        := slotMark,
      latestBlockHeader.proposerIndex := UInt64.ofNat (s &&& 0xff),
      latestBlockHeader.stateRoot   := saltRoot (UInt8.ofNat (s &&& 0xff)),
      blockRoots[s % 8192]          := saltRoot (UInt8.ofNat (s &&& 0xff)),
      stateRoots[s % 8192]          := saltRoot (UInt8.ofNat (s &&& 0xff)),
      randaoMixes[s % 65536]        := saltRoot (UInt8.ofNat (s &&& 0xff)),
      eth1DepositIndex              := slotMark,
      depositBalanceToConsume       := slotMark * 1000,
      exitBalanceToConsume          := slotMark * 500,
      validators[valIdx0]           := newV0,
      validators[valIdx1]           := newV1,
      validators[valIdx2]           := newV2,
      balances                      := newBalances,
      inactivityScores              := newInactivity,
      proposerLookahead             := newLookahead
    if s % 32 == 31 then
      box := sszUpdate box with
        currentSyncCommittee       := box.view.nextSyncCommittee,
        nextSyncCommittee          := mkSyncCommittee slotMark.toUInt8,
        currentJustifiedCheckpoint := mkCheckpoint slotMark.toUInt8,
        finalizedCheckpoint        := box.view.currentJustifiedCheckpoint,
        justificationBits          := { data := BitVec.ofNat 4 ((s / 32) &&& 0xf) }
    let (root, b₁) := box.hashTreeRoot
    box := b₁
    sink.modify (· + consume root)
  -- Per-iteration `box.serialize` would dominate the bench, see
  -- docstring. One serialize *outside* the slot loop keeps the
  -- bytes path forced (sink stays non-zero) without affecting
  -- the cache-vs-pure delta inside the loop.
  sink.modify (· + consume box.serialize)

/-! ## Entry point: `runAll` -/

def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  let baseValue := mkBeaconState 1
  let pureBox   : SSZ.Box Sha256 BeaconState := SSZ.PureBox baseValue
  let cachedBox : SSZ.Box Sha256 BeaconState := SSZ.FastBox baseValue
  -- Pre-fire one root per box outside the timed region. Primes
  -- the cached box's cell-level cache slots (the first
  -- `hashTreeRoot` is a cold ~190 ms walk) and forces the
  -- Thunk-backed `view` so every iteration starts identically.
  let (r1, _) := cachedBox.hashTreeRoot
  let _ := r1.foldl (init := 0) (fun a b => a + b.toNat)
  let r2 := SSZ.hashTreeRoot Sha256 pureBox.view
  let _ := r2.foldl (init := 0) (fun a b => a + b.toNat)
  let iterations : Nat := 20
  runBench s!"S7 FuluStateTransition (mainnet, {NUM_VALIDATORS} val, {SLOTS_PER_RUN} slots) · BeaconState · pure"
    iterations (runTransitions sink pureBox)
  runBench s!"S7 FuluStateTransition (mainnet, {NUM_VALIDATORS} val, {SLOTS_PER_RUN} slots) · BeaconState · cached"
    iterations (runTransitions sink cachedBox)
  let total ← sink.get
  if total == 0 then IO.eprintln "S7 sink unexpectedly 0"

end SizzLeanBench.Scenarios.FuluStateTransition
