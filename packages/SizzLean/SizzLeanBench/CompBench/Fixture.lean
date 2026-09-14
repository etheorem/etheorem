import SizzLeanBench.Fulu

/-!
# `SizzLeanBench.CompBench.Fixture`: the shared cross-library fixture

The comparative benchmark runs one `BeaconState` through three SSZ
libraries: SizzLean, `ethereum/ssz-specs` (Python), and
`lambdaclass/libssz` (Rust). All three must root the *same* value,
so one side has to own the bytes. This module is that side. The
`ssz_compbench emit` subcommand serializes the state below, and the
other two harnesses decode those very bytes.

They therefore need no copy of this builder, only a copy of the
container set: `scripts/compbench/ssz_specs_harness.py` and
`scripts/compbench/libssz-harness/src/types.rs`. The one generator
they do repeat is `byte32`, which the thousand-write scenario calls
to build the roots it writes. The benchmark driver checks every
copy at once by comparing the roots the three harnesses print.

## Why every field carries distinct data

A zero-filled subtree is the cheap case. Zero chunks repeat, so a
merkleization that memoises repeated subtrees, or a hasher fed the
same two children twice, does less work than it would on a real
state. The `SizzLeanBench.Fulu` state-transition fixture leaves
`blockRoots`, `stateRoots`, `randaoMixes`, and `slashings` at zero,
which is fine for a cache-versus-pure delta inside one library and
misleading across libraries. This fixture fills every collection
with distinct values, so the comparison measures the work a real
state costs.

## Shape and size

Mainnet preset, Fulu `BeaconState`, 37 fields, 1024 validators.
The `randaoMixes` vector alone is 2 MiB of the roughly 2.9 MB total,
so the fixture is multi-megabyte without an unrealistic validator
count.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SizzLeanBench.CompBench.Fixture

open SizzLean
open SizzLean.Repr
open SizzLeanBench.Fulu

/-! ## Population counts

The bounded collections carry a fixed number of entries. Every
count below is repeated verbatim in the Rust and the Python copy. -/

/-- Validators, and the length of every registry-parallel list
(`balances`, the two participation lists, `inactivityScores`). -/
def numValidators : Nat := 1024

/-- Entries in `historicalRoots`. -/
def numHistoricalRoots : Nat := 64

/-- Entries in `eth1DataVotes`. -/
def numEth1DataVotes : Nat := 64

/-- Entries in `historicalSummaries`. -/
def numHistoricalSummaries : Nat := 64

/-- Entries in each of the three Electra pending-operation lists. -/
def numPendingOps : Nat := 16

/-- Bytes in the execution payload header's `extraData`. -/
def extraDataLen : Nat := 32

/-! ## Byte generators

Five formulas produce every byte in the fixture. Each takes a
seed and a byte position and returns one byte. They are plain
modular arithmetic on `Nat` so the Rust and the Python copies
reproduce them without caring about integer width.

The multipliers are arbitrary odd numbers. They only have to make
neighbouring seeds produce unrelated bytes, so that no two chunks
of the fixture coincide. -/

/-- One byte of a 32-byte root or credential, from a seed. -/
@[inline] def byte32 (seed pos : Nat) : UInt8 :=
  UInt8.ofNat ((seed * 31 + pos * 7 + 11) % 256)

/-- One byte of a 48-byte BLS public key, from a seed. -/
@[inline] def bytePubkey (seed pos : Nat) : UInt8 :=
  UInt8.ofNat ((seed * 17 + pos * 3 + 5) % 256)

/-- One byte of a 96-byte BLS signature, from a seed. -/
@[inline] def byteSignature (seed pos : Nat) : UInt8 :=
  UInt8.ofNat ((seed * 13 + pos * 5 + 7) % 256)

/-- One byte of a 20-byte execution address, from a seed. -/
@[inline] def byteAddress (seed pos : Nat) : UInt8 :=
  UInt8.ofNat ((seed * 19 + pos * 11 + 3) % 256)

/-- One byte of a 4-byte fork version, from a seed. -/
@[inline] def byteVersion (seed pos : Nat) : UInt8 :=
  UInt8.ofNat ((seed + pos) % 256)

/-! ## Fixed-width values

Each wraps one generator into the vector width the container
field declares. `Vector.ofFn` takes a `Fin n` lambda; the width
`n` comes from the expected type, so the position argument is
already bounded and needs no proof. -/

/-- A 32-byte root or `Bytes32`. -/
def mkRoot (seed : Nat) : Root :=
  Vector.ofFn fun (i : Fin 32) => byte32 seed i.val

/-- A 48-byte BLS public key. -/
def mkPubkey (seed : Nat) : BLSPubkey :=
  Vector.ofFn fun (i : Fin 48) => bytePubkey seed i.val

/-- A 96-byte BLS signature. -/
def mkSignature (seed : Nat) : BLSSignature :=
  Vector.ofFn fun (i : Fin 96) => byteSignature seed i.val

/-- A 20-byte execution address. -/
def mkAddress (seed : Nat) : ExecutionAddress :=
  Vector.ofFn fun (i : Fin 20) => byteAddress seed i.val

/-- A 4-byte fork version. -/
def mkVersion (seed : Nat) : Version :=
  Vector.ofFn fun (i : Fin 4) => byteVersion seed i.val

/-! ## Sub-container builders -/

/-- The `i`-th validator. `exitEpoch` and `withdrawableEpoch` take
the far-future sentinel every active validator carries. -/
def mkValidator (i : Nat) : Validator :=
  { pubkey                     := mkPubkey i
    withdrawalCredentials      := mkRoot (i + 1000000)
    effectiveBalance           := 32000000000 + (i * 1000000).toUInt64
    slashed                    := i % 7 == 0
    activationEligibilityEpoch := i.toUInt64
    activationEpoch            := (i + 1).toUInt64
    exitEpoch                  := 18446744073709551615
    withdrawableEpoch          := 18446744073709551615 }

/-- The `i`-th balance, in Gwei. -/
def mkBalance (i : Nat) : Gwei := 32000000000 + (i * 7).toUInt64

/-- The `i`-th participation-flag byte. -/
def mkParticipation (i : Nat) : ParticipationFlags := UInt8.ofNat (i % 8)

/-- The `i`-th inactivity score. -/
def mkInactivity (i : Nat) : UInt64 := (i % 17).toUInt64

def mkCheckpoint (seed : Nat) : Checkpoint :=
  { epoch := seed.toUInt64, root := mkRoot (seed + 500) }

def mkFork : Fork :=
  { previousVersion := mkVersion 1, currentVersion := mkVersion 2, epoch := 512 }

def mkBlockHeader (seed : Nat) : BeaconBlockHeader :=
  { slot          := seed.toUInt64
    proposerIndex := (seed % 1024).toUInt64
    parentRoot    := mkRoot (seed + 100)
    stateRoot     := mkRoot (seed + 200)
    bodyRoot      := mkRoot (seed + 300) }

def mkEth1Data (seed : Nat) : Eth1Data :=
  { depositRoot  := mkRoot (seed + 400)
    depositCount := (seed * 32).toUInt64
    blockHash    := mkRoot (seed + 600) }

def mkSyncCommittee (seed : Nat) : SyncCommittee :=
  { pubkeys         := Vector.ofFn fun (i : Fin 512) => mkPubkey (seed + i.val)
    aggregatePubkey := mkPubkey (seed + 4096) }

def mkHistoricalSummary (seed : Nat) : HistoricalSummary :=
  { blockSummaryRoot := mkRoot (seed + 700), stateSummaryRoot := mkRoot (seed + 800) }

def mkPendingDeposit (i : Nat) : PendingDeposit :=
  { pubkey                := mkPubkey (i + 8192)
    withdrawalCredentials := mkRoot (i + 900)
    amount                := 32000000000 + i.toUInt64
    signature             := mkSignature i
    slot                  := (i * 3).toUInt64 }

def mkPendingPartialWithdrawal (i : Nat) : PendingPartialWithdrawal :=
  { validatorIndex := i.toUInt64, amount := (i * 1000).toUInt64
    withdrawableEpoch := (i + 64).toUInt64 }

def mkPendingConsolidation (i : Nat) : PendingConsolidation :=
  { sourceIndex := i.toUInt64, targetIndex := (i + 1).toUInt64 }

/-- The Deneb execution payload header, every field populated. -/
def mkExecHeader : ExecutionPayloadHeader :=
  { parentHash       := mkRoot 2001
    feeRecipient     := mkAddress 2002
    stateRoot        := mkRoot 2003
    receiptsRoot     := mkRoot 2004
    logsBloom        := Vector.ofFn fun (i : Fin 256) => byte32 2005 i.val
    prevRandao       := mkRoot 2006
    blockNumber      := 21000000
    gasLimit         := 30000000
    gasUsed          := 14500000
    timestamp        := 1700000000
    extraData        :=
      ⟨Array.ofFn (n := extraDataLen) fun (i : Fin extraDataLen) => byte32 2007 i.val,
       by simp [Array.size_ofFn, extraDataLen]⟩
    baseFeePerGas    := BitVec.ofNat 256 1234567890
    blockHash        := mkRoot 2008
    transactionsRoot := mkRoot 2009
    withdrawalsRoot  := mkRoot 2010
    blobGasUsed      := 393216
    excessBlobGas    := 131072 }

/-! ## The state -/

/-- Build an `SSZList` of exactly `n` entries from an index
function. The capacity proof is discharged by the caller's `h`;
`Array.size_ofFn` rewrites the built array's size to `n`. -/
private def mkList {α : Type} {cap : Nat} (n : Nat) (h : n ≤ cap)
    (f : Nat → α) : SSZList α cap :=
  ⟨Array.ofFn (n := n) fun (i : Fin n) => f i.val,
   by simpa [Array.size_ofFn] using h⟩

/-- The fixture: a mainnet-preset Fulu `BeaconState` with every
field populated by the generators above. Roughly 2.9 MB on the
wire. -/
def mkBeaconState : BeaconState :=
  { genesisTime                   := 1606824023
    genesisValidatorsRoot         := mkRoot 42
    slot                          := 9007199
    fork                          := mkFork
    latestBlockHeader             := mkBlockHeader 9007198
    blockRoots                    :=
      Vector.ofFn fun (i : Fin 8192) => mkRoot (i.val + 10000)
    stateRoots                    :=
      Vector.ofFn fun (i : Fin 8192) => mkRoot (i.val + 20000)
    historicalRoots               :=
      mkList numHistoricalRoots (by decide) fun i => mkRoot (i + 30000)
    eth1Data                      := mkEth1Data 7
    eth1DataVotes                 :=
      mkList numEth1DataVotes (by decide) fun i => mkEth1Data (i + 40000)
    eth1DepositIndex              := 1234567
    validators                    :=
      mkList numValidators (by decide) mkValidator
    balances                      :=
      mkList numValidators (by decide) mkBalance
    randaoMixes                   :=
      Vector.ofFn fun (i : Fin 65536) => mkRoot (i.val + 50000)
    slashings                     :=
      Vector.ofFn fun (i : Fin 8192) => (i.val * 1000000).toUInt64
    previousEpochParticipation    :=
      mkList numValidators (by decide) mkParticipation
    currentEpochParticipation     :=
      mkList numValidators (by decide) fun i => mkParticipation (i + 3)
    justificationBits             := { data := BitVec.ofNat 4 0b1011 }
    previousJustifiedCheckpoint   := mkCheckpoint 281474
    currentJustifiedCheckpoint    := mkCheckpoint 281475
    finalizedCheckpoint           := mkCheckpoint 281473
    inactivityScores              :=
      mkList numValidators (by decide) mkInactivity
    currentSyncCommittee          := mkSyncCommittee 60000
    nextSyncCommittee             := mkSyncCommittee 70000
    latestExecutionPayloadHeader  := mkExecHeader
    nextWithdrawalIndex           := 987654
    nextWithdrawalValidatorIndex  := 321
    historicalSummaries           :=
      mkList numHistoricalSummaries (by decide) fun i => mkHistoricalSummary (i + 80000)
    depositRequestsStartIndex     := 1000
    depositBalanceToConsume       := 64000000000
    exitBalanceToConsume          := 32000000000
    earliestExitEpoch             := 281470
    consolidationBalanceToConsume := 16000000000
    earliestConsolidationEpoch    := 281471
    pendingDeposits               :=
      mkList numPendingOps (by decide) mkPendingDeposit
    pendingPartialWithdrawals     :=
      mkList numPendingOps (by decide) mkPendingPartialWithdrawal
    pendingConsolidations         :=
      mkList numPendingOps (by decide) mkPendingConsolidation
    proposerLookahead             :=
      Vector.ofFn fun (i : Fin 64) => (i.val * 13 + 5).toUInt64 }

end SizzLeanBench.CompBench.Fixture
