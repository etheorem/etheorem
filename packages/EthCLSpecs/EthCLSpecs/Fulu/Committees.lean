import EthCLSpecs.Fulu.Registry

/-!
# `EthCLSpecs.Fulu.Committees`: shuffling, committees, and balance-weighted selection

The swap-or-not shuffle and everything built on it: seed derivation (`get_seed`),
committee assignment (`get_beacon_committee`), the balance-weighted sampler
(`compute_balance_weighted_selection`) used for proposer and sync-committee
selection, and `get_next_sync_committee`.

These are pure functions of the boxed `State` (no monad); the epoch and operation
steps call them. They hash through the `[HasherTag]` seam (`sha`), so the same
swap-or-not bytes a real client computes. Performance is unoptimised but adequate
for the minimal preset: the permutation is recomputed per committee, and the
weighted sampler is a tail-recursive loop bounded by the spec's `uint64` counter.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-! ## The swap-or-not shuffle -/

/-- `compute_shuffled_permutation`: the swap-or-not shuffle (`SHUFFLE_ROUND_COUNT`
rounds). Each position evolves independently from its own value, so one round is a
single `Array.ofFn` over the previous array. -/
forkdef computeShuffledPermutation (indexCount : Nat) (seed : ByteArray) : Array ValidatorIndex :=
  if indexCount == 0 then #[]
  else
    (List.range Const.shuffleRoundCount).foldl
      (fun indices round =>
        -- Each round mixes in a fresh seed byte and draws the swap pivot.
        let seedRound := seed.push (UInt8.ofNat round)
        let pivot := (le8 (sha seedRound)) % indexCount

        -- Rebuild every slot independently: swap to `flip`, or keep `cur`.
        Array.ofFn (n := indexCount) (fun i : Fin indexCount =>
          let cur := (indices[i.val]!).toNat
          let flip := (pivot + indexCount - cur) % indexCount
          let position := Nat.max cur flip
          -- One bit of the round's hash stream decides the swap: hash the seed with
          -- the high bytes of `position`, then read bit `position % 8` of the byte at
          -- `(position % 256) / 8`. A set bit moves this slot to `flip`.
          let source := sha (seedRound ++ u32leBytes (position / 256))
          let byteVal := (source.get! ((position % 256) / 8)).toNat
          let bit := (byteVal >>> (position % 8)) % 2
          if bit == 1 then UInt64.ofNat flip else UInt64.ofNat cur))
      (Array.ofFn (n := indexCount) (fun i : Fin indexCount => UInt64.ofNat i.val))

/-! ## Seeds and committee counts -/

/-- `get_seed(state, epoch, domain_type)`. The randao-mix slot is a `% EPOCHS_PER_HISTORICAL_VECTOR`
ring-buffer index, read with the proof-carrying `vmodGet` (the modulus's positivity / bound
come from the `[Preset]` well-formedness fields, so the read needs no `Inhabited` default). -/
forkdef getSeed (state : State) (epoch : Epoch) (domainType : ByteArray) : Bytes32 :=
  let epochsPerVector := UInt64.ofNat Const.epochsPerHistoricalVector
  let mix := vmodGet (sszGet state randaoMixes) (epoch + epochsPerVector - Const.minSeedLookahead - 1) Const.epochsPerHistoricalVector
  bytesToRoot (sha (domainType ++ uint64ToBytes epoch ++ mix))

/-- `get_committee_count_per_slot`. -/
forkdef getCommitteeCountPerSlot (state : State) (epoch : Epoch) : Nat :=
  let active := (getActiveValidatorIndices state epoch).size
  Nat.max 1 (Nat.min Const.maxCommitteesPerSlot
    (active / Const.slotsPerEpoch / Const.targetCommitteeSize))

/-! ## Committee assignment -/

/-- `compute_committee`: slice `[start, end)` of the shuffled `indices`. -/
forkdef computeCommittee (indices : Array ValidatorIndex) (seed : Bytes32) (index count : Nat) :
    Array ValidatorIndex :=
  let len := indices.size
  let start := len * index / count
  let stop := len * (index + 1) / count
  let perm := computeShuffledPermutation len seed
  (Array.range (stop - start)).map (fun j => indices[(perm[start + j]!).toNat]!)

/-- `get_beacon_committee(state, slot, index)`. -/
forkdef getBeaconCommittee (state : State) (slot : Slot) (index : Nat) : Array ValidatorIndex :=
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  computeCommittee (getActiveValidatorIndices state epoch) (getSeed state epoch Const.domainBeaconAttester)
    ((slot % UInt64.ofNat Const.slotsPerEpoch).toNat * committeesPerSlot + index) (committeesPerSlot * Const.slotsPerEpoch)

/-- `get_committee_indices`: the committee indices flagged in `committee_bits`. -/
forkdef getCommitteeIndices {n : Nat} (bits : Bitvector n) : Array Nat :=
  Bitvector.trueIndices bits

/-! ## Balance-weighted selection -/

/-- `compute_balance_weighted_selection` inner loop, one call per pass of the spec's
`while len(selected) < size`. The size check exits first, and the tail increment runs the
spec's `uint64` `i += 1` through `checkedSucc`, so the last pass at `i = 2**64 - 1` throws
`.arithmetic`, the spec's overflow, whether or not it filled the selection. -/
forkdef cbwsAux [Preset] (indices effBals : Array Nat) (perm : Array ValidatorIndex)
    (seed : ByteArray) (total size : Nat) (shuffle : Bool) (i : Nat) (randomBytes : ByteArray)
    (selected : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  if selected.size ≥ size then pure selected
  else
    let offset := (i % 16) * 2
    let randomBytes := if offset == 0 then sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else randomBytes
    let nextIndex := if shuffle then (perm[i % total]!).toNat else i % total
    let weight := effBals[nextIndex]! * Const.maxRandomValue
    let randomValue := le2 randomBytes offset
    let threshold := Const.maxEffectiveBalanceElectra * randomValue
    let selected := if weight ≥ threshold then selected.push (UInt64.ofNat (indices[nextIndex]!)) else selected
    let s ← checkedSucc i "compute_balance_weighted_selection: i += 1 past 2**64 - 1"
    cbwsAux indices effBals perm seed total size shuffle s.val randomBytes selected
termination_by counterBudgetUInt64 i

/-- `compute_balance_weighted_selection(state, indices, seed, size, shuffle)`
(`gloas/beacon-chain.md:1195-1234`). An empty `indices` rejects on the spec's
`assert total > 0` (`:1213`). -/
forkdef computeBalanceWeightedSelection (state : State) (indices : Array ValidatorIndex)
    (seed : ByteArray) (size : Nat) (shuffle : Bool) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let total := indices.size
  assert (total > 0)
  let idxNat := indices.map (·.toNat)
  let validators := sszGet state validators
  let effBals := indices.map (fun vi => (validators[vi.toNat]!).effectiveBalance.toNat)
  let perm := if shuffle then computeShuffledPermutation total seed else #[]
  cbwsAux idxNat effBals perm seed total size shuffle 0 ByteArray.empty #[]

/-! ## Proposer and sync-committee selection -/

/-- `compute_proposer_indices`: one balance-weighted proposer per slot in `epoch`. An empty
`indices` rejects through `computeBalanceWeightedSelection`'s `assert total > 0`. -/
forkdef computeProposerIndices (state : State) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) :=
  let startSlot := computeStartSlotAtEpoch epoch
  (Array.range Const.slotsPerEpoch).mapM (fun i => do
    let sd := sha (seed ++ uint64ToBytes (startSlot + UInt64.ofNat i))
    return (← computeBalanceWeightedSelection state indices sd 1 true)[0]!)

/-- `get_beacon_proposer_index`: read the precomputed Fulu lookahead (no shuffle). -/
forkdef getBeaconProposerIndex (state : State) : ValidatorIndex :=
  vmodGet (sszGet state proposerLookahead) (sszGet state slot) Const.slotsPerEpoch

/-- `get_beacon_proposer_indices(state, epoch)`: the per-slot proposers for `epoch`. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) :=
  computeProposerIndices state epoch (getSeed state epoch Const.domainBeaconProposer)
    (getActiveValidatorIndices state epoch)

/-- `get_next_sync_committee`: balance-weighted selection of the next sync committee,
with the real BLS `aggregate_pubkey` through the `[CryptoBackend]` seam. Rejects when no
validator is active next epoch, through `computeBalanceWeightedSelection`. -/
forkdef getNextSyncCommittee [CryptoBackend] (state : State) :
    Except StateTransitionError SyncCommittee := do
  let epoch := currentEpochOf state + 1
  let seed := getSeed state epoch Const.domainSyncCommittee
  let indices ← computeBalanceWeightedSelection state (getActiveValidatorIndices state epoch)
    seed Const.syncCommitteeSize true

  let validators := sszGet state validators
  let pubkeys : Vector BLSPubkey Const.syncCommitteeSize :=
    Vector.ofFn (fun i => (validators[(indices[i.val]!).toNat]?.getD default).pubkey)
  return { pubkeys := pubkeys, aggregatePubkey := blsAggregatePubkeys pubkeys.toArray }

end

end EthCLSpecs.Fulu
