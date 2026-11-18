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

/-- `get_seed(state, epoch, domain_type)` (`fulu/mainnet.py:1483-1491`). The randao-mix
slot is a `% EPOCHS_PER_HISTORICAL_VECTOR` ring-buffer index, read with the proof-carrying
`vmodGet` (the modulus's positivity / bound come from the `[Preset]` well-formedness fields,
so the read needs no `Inhabited` default). The epoch sum
`epoch + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1` is the pyspec's checked
`Epoch` chain ("Avoid underflow", add before subtract), tested per operation in Python's
order, so each step binds (`SPEC_ARITHMETIC.md` §4.3) and the helper carries the fault.
The epoch's bytes are the checked value's wire bytes: `uint64ToBytes` reads the underlying
word, the codec boundary §4.5 asks each projection to name. -/
forkdef getSeed (state : State) (epoch : Epoch) (domainType : ByteArray) :
    Checked Bytes32 := do
  let shifted ← epoch + Const.epochsPerHistoricalVectorC
  let shifted ← shifted - Const.minSeedLookahead
  let mixSlot ← shifted - 1
  let mixIdx ← mixSlot % Const.epochsPerHistoricalVectorC
  pure (bytesToRoot (sha (domainType ++ uint64ToBytes epoch.val ++
    vmodGet (sszGet state randaoMixes) mixIdx.val Const.epochsPerHistoricalVector)))

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

/-- `get_beacon_committee(state, slot, index)` (`fulu/mainnet.py:1508-1521`). The seed walk
is `get_seed`, which raises on its checked epoch chain, so the helper carries the fault and
each caller binds it. The `slot % SLOTS_PER_EPOCH` offset takes the proved-total divisor
view (`SPEC_ARITHMETIC.md` §4.2, the preset value positive); the per-slot committee index
and count are the committee-slice bounds, structural `Nat`s this task leaves to Stage 6
(`SPEC_ARITHMETIC.md` §4.2, the structural-count rule), so the checked remainder narrows
with `toPlainNat` at that boundary. -/
forkdef getBeaconCommittee (state : State) (slot : Slot) (index : Nat) :
    Checked (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let seed ← getSeed state epoch Const.domainBeaconAttester
  let slotInEpoch := slot % Const.slotsPerEpochDiv
  pure (computeCommittee (getActiveValidatorIndices state epoch) seed
    (slotInEpoch.toPlainNat * committeesPerSlot + index) (committeesPerSlot * Const.slotsPerEpoch))

/-- `get_committee_indices`: the committee indices flagged in `committee_bits`. -/
forkdef getCommitteeIndices {n : Nat} (bits : Bitvector n) : Array Nat :=
  Bitvector.trueIndices bits

/-! ## Balance-weighted selection -/

/-- `compute_balance_weighted_selection` inner loop, one call per pass of the spec's
`while len(selected) < size`. The size check exits first. The `weight` and `threshold`
products are the spec's checked `Gwei` chains (`effective_balances[next_index] *
MAX_RANDOM_VALUE`, `MAX_EFFECTIVE_BALANCE_ELECTRA * random_value`), so each binds before
the comparison, and the comparison runs only after both formed. The tail increment runs the
spec's `uint64` `i += 1` through `checkedSucc`, so the last pass at `i = 2**64 - 1` throws
`.arithmetic`, the spec's overflow, whether or not it filled the selection. -/
forkdef cbwsAux [Preset] (indices perm : Array ValidatorIndex) (effBals : Array Gwei)
    (seed : ByteArray) (total size : Nat) (shuffle : Bool) (i : Nat) (randomBytes : ByteArray)
    (selected : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  if selected.size ≥ size then pure selected
  else
    let offset := (i % 16) * 2
    let randomBytes := if offset == 0 then sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else randomBytes
    let nextIndex := if shuffle then (perm[i % total]!).toNat else i % total
    let weight ← effBals[nextIndex]! * Const.maxRandomValue
    -- `bytes_to_uint64` of two bytes: in range by construction, so the checked
    -- construction carries the codec value into the checked kind.
    let randomValue ← CLUint64.ofNat? (le2 randomBytes offset)
    let threshold ← Const.maxEffectiveBalanceElectraG * randomValue
    let selected := if weight ≥ threshold then selected.push (indices[nextIndex]!) else selected
    let s ← checkedSucc i "compute_balance_weighted_selection: i += 1 past 2**64 - 1"
    cbwsAux indices perm effBals seed total size shuffle s.val randomBytes selected
termination_by counterBudgetUInt64 i

/-- `compute_balance_weighted_selection(state, indices, seed, size, shuffle)`
(`gloas/beacon-chain.md:1195-1234`). An empty `indices` rejects on the spec's
`assert total > 0` (`:1213`). The sampled chain reads `effective_balance`, so
the balance list and the `weight` / `threshold` products keep the checked
`Gwei` kind (`SPEC_ARITHMETIC.md` §4.2, each intermediate range test). -/
forkdef computeBalanceWeightedSelection (state : State) (indices : Array ValidatorIndex)
    (seed : ByteArray) (size : Nat) (shuffle : Bool) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let total := indices.size
  assert (total > 0)
  let validators := sszGet state validators
  let effBals := indices.map (fun vi => (validators[vi.toNat]!).effectiveBalance)
  let perm := if shuffle then computeShuffledPermutation total seed else #[]
  cbwsAux indices perm effBals seed total size shuffle 0 ByteArray.empty #[]

/-! ## Proposer and sync-committee selection -/

/-- `compute_proposer_indices`: one balance-weighted proposer per slot in `epoch`. An empty
`indices` rejects through `computeBalanceWeightedSelection`'s `assert total > 0`. The pinned
body (`fulu/minimal.py:6606-6608`) runs in two phases: the `seeds` list forms every checked
`start_slot + index` add first, then the selection runs once per seed. A range fault at any
index therefore precedes the selection assert at index `0`. The seed feed `uint64_to_bytes`
reads the checked value's underlying word, the codec boundary §4.5 asks each projection to
name. -/
forkdef computeProposerIndices (state : State) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  let startSlot ← computeStartSlotAtEpoch epoch
  -- Phase 1, the `seeds` comprehension: one checked `start_slot + index` per slot.
  let seeds : Array ByteArray ← (Array.range Const.slotsPerEpoch).mapM (fun i => do
    let slot ← startSlot + i
    pure (sha (seed ++ uint64ToBytes slot.val)))
  -- Phase 2: one balance-weighted proposer per seed, in slot order.
  seeds.mapM (fun sd => do
    return (← computeBalanceWeightedSelection state indices sd 1 true)[0]!)

/-- `get_beacon_proposer_index`: read the precomputed Fulu lookahead (no shuffle). The
`slot % SLOTS_PER_EPOCH` ring index passes the checked value's word to the proved-total
`vmodGet` route, whose bound is the mod itself (`SPEC_ARITHMETIC.md` §4.5). -/
forkdef getBeaconProposerIndex (state : State) : ValidatorIndex :=
  vmodGet (sszGet state proposerLookahead) (sszGet state slot).val Const.slotsPerEpoch

/-- `get_beacon_proposer_indices(state, epoch)`: the per-slot proposers for `epoch`. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let seed ← getSeed state epoch Const.domainBeaconProposer
  computeProposerIndices state epoch seed
    (getActiveValidatorIndices state epoch)

/-- `get_next_sync_committee`: balance-weighted selection of the next sync committee,
with the real BLS `aggregate_pubkey` through the `[CryptoBackend]` seam. Rejects when no
validator is active next epoch, through `computeBalanceWeightedSelection`. -/
forkdef getNextSyncCommittee [CryptoBackend] (state : State) :
    Except StateTransitionError SyncCommittee := do
  let epoch ← currentEpochOf state + 1
  let seed ← getSeed state epoch Const.domainSyncCommittee
  let indices ← computeBalanceWeightedSelection state (getActiveValidatorIndices state epoch)
    seed Const.syncCommitteeSize true

  let validators := sszGet state validators
  let pubkeys : Vector BLSPubkey Const.syncCommitteeSize :=
    Vector.ofFn (fun i => (validators[(indices[i.val]!).toNat]?.getD default).pubkey)
  return { pubkeys := pubkeys, aggregatePubkey := blsAggregatePubkeys pubkeys.toArray }

end

end EthCLSpecs.Fulu
