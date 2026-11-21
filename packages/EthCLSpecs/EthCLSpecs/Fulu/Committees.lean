import EthCLSpecs.Fulu.Registry

/-!
# `EthCLSpecs.Fulu.Committees`: shuffling, committees, and balance-weighted selection

The swap-or-not shuffle and everything built on it: seed derivation (`get_seed`),
committee assignment (`get_beacon_committee`), Electra's balance-weighted sampling loops for
proposer and sync-committee selection, and `get_next_sync_committee`.

The epoch and operation steps call these functions of the boxed `State`. They hash through
the `[HasherTag]` seam (`sha`), so they compute the same swap-or-not bytes a real client
computes. Performance is adequate for the minimal preset. Each committee recomputes the
permutation.

A function here returns a bare `Except` when the pyspec can raise in it, as
`computeStartSlotAtEpoch` does. It raises where the pyspec raises, with the reject kind that
the runner sees. Two kinds occur:

* `.arithmetic`: the `uint64` encodings and products of the seed, the shuffle, the committee
  slice and the sampling loops. The pyspec raises an uncaught `OverflowError`, `ValueError`
  or `ZeroDivisionError` there.
* `.assert`: the asserts of `compute_shuffled_index` and of `compute_proposer_index`.
* `.outOfBounds`: a sampled candidate past the registry, the pyspec's `IndexError`.

Each sampling loop is tail-recursive and bounded by the spec's `uint64` counter.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-! ## The swap-or-not shuffle -/

/-- `compute_shuffled_permutation` (`phase0/beacon-chain.md:1211-1233`): the swap-or-not
shuffle (`SHUFFLE_ROUND_COUNT` rounds). Each position evolves independently from its own
value, so one round is a single `Array.ofFn` over the previous array.

The pyspec raises an uncaught fault (`.arithmetic`) in three places. The body checks them
first, in the order that the pyspec reaches them:

1. Round 0 computes `% index_count`. This divides by zero when `index_count = 0`.
2. Round 0 reaches the value `n - 1`. Its bucket `position // 256` overflows
   `Uint32(position_bucket)` when `n > 2 ^ 40`, and only then. The pyspec first builds the
   list of all `n` indices, so on a real machine it runs out of memory before that point.
   Both are faults that no reference wrapper catches.
3. Round 256 computes `Uint8(current_round)`, which overflows. Rounds `0 … 255` run before
   it.

With no rounds, the loop body never runs. Then no check fires, and the pyspec returns the
identity, also for `index_count = 0`. After the checks, the body cannot wrap. `UInt8.ofNat`
gets rounds below `256`, and `u32leBytes` gets buckets below `2 ^ 32`. -/
forkdef computeShuffledPermutation (indexCount : Nat) (seed : ByteArray) :
    Except StateTransitionError (Array ValidatorIndex) := do
  -- Built only after the checks, so an `index_count` past `2 ^ 40` faults before any
  -- allocation.
  let identity (n : Nat) : Array ValidatorIndex :=
    Array.ofFn (n := n) (fun i : Fin n => UInt64.ofNat i.val)
  if Const.shuffleRoundCount == 0 then return identity indexCount
  if indexCount == 0 then
    throwArithmetic "compute_shuffled_permutation: pivot % index_count with index_count = 0"
  if 2 ^ 40 < indexCount then
    throwArithmetic "compute_shuffled_permutation: Uint32(position_bucket) past 2 ** 32"
  if 256 < Const.shuffleRoundCount then
    throwArithmetic "compute_shuffled_permutation: Uint8(current_round) at round 256"
  pure <|
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
      (identity indexCount)

/-! ## Seeds and committee counts -/

/-- The seed of `get_seed(state, epoch, domain_type)` once its mix epoch is known to fit. The
randao-mix slot is a `% EPOCHS_PER_HISTORICAL_VECTOR` ring-buffer index, read with the
proof-carrying `vmodGet` (the modulus's positivity / bound come from the `[Preset]`
well-formedness fields, so the read needs no `Inhabited` default). The `uint64` arithmetic
here wraps. `getSeed` runs the pyspec's checks first, so it calls this only where the
arithmetic is exact. -/
forkdef seedOf (state : State) (epoch : Epoch) (domainType : ByteArray) : Bytes32 :=
  let epochsPerVector := UInt64.ofNat Const.epochsPerHistoricalVector
  let mix := vmodGet (sszGet state randaoMixes) (epoch + epochsPerVector - Const.minSeedLookahead - 1) Const.epochsPerHistoricalVector
  bytesToRoot (sha (domainType ++ uint64ToBytes epoch ++ mix))

/-- `get_seed(state, epoch, domain_type)` (`phase0/beacon-chain.md:1496-1503`). The pyspec
computes `Epoch(epoch + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1)` in checked
`uint64` arithmetic, left to right. The add raises `ValueError` at `2 ^ 64` or above, and a
subtraction raises on an underflow. The body makes the three checks in that order, as
`.arithmetic`, and otherwise returns `seedOf`. -/
forkdef getSeed (state : State) (epoch : Epoch) (domainType : ByteArray) :
    Except StateTransitionError Bytes32 := do
  let sum ← checkedAdd epoch (UInt64.ofNat Const.epochsPerHistoricalVector)
    "get_seed: epoch + EPOCHS_PER_HISTORICAL_VECTOR"
  let lessLookahead ← checkedSub sum Const.minSeedLookahead
    "get_seed: … - MIN_SEED_LOOKAHEAD"
  let _ ← checkedSub lessLookahead 1 "get_seed: … - 1"
  pure (seedOf state epoch domainType)

/-- The committee count of `get_committee_count_per_slot` over the active set of
`activeValidatorIndicesOf`. -/
forkdef committeeCountOf (state : State) (epoch : Epoch) : Nat :=
  let active := (activeValidatorIndicesOf state epoch).size
  Nat.max 1 (Nat.min Const.maxCommitteesPerSlot
    (active / Const.slotsPerEpoch / Const.targetCommitteeSize))

/-- `get_committee_count_per_slot` (`phase0/beacon-chain.md:1509-1521`). It raises where its
`get_active_validator_indices` call raises, and otherwise returns `committeeCountOf`. -/
forkdef getCommitteeCountPerSlot (state : State) (epoch : Epoch) :
    Except StateTransitionError Nat := do
  let _ ← getActiveValidatorIndices state epoch
  pure (committeeCountOf state epoch)

/-! ## Committee assignment -/

/-- `compute_committee` (`phase0/beacon-chain.md:1273-1285`): slice `[start, end)` of the
shuffled `indices`.

The pyspec's `index` and `count` are `uint64` values, so the pyspec checks its arithmetic:

* `len * index`, `index + 1` and `len * (index + 1)` raise `ValueError` on overflow
  (`.arithmetic`).
* `// count` raises `ZeroDivisionError` when `count = 0` (`.arithmetic`).

A `Nat` argument at or above `2 ^ 64` is not a `uint64`, so it raises the same fault.

The pyspec computes each entry of the slice with one `compute_shuffled_index(i, len, seed)`
call. That call asserts `i < len` and then shuffles. An empty slice makes no call, so
`len = 0` gives `[]`. For a slice with entries, the first call asserts `start < len` and then
runs the shuffle, which can fault. The calls after it fail their assert when `stop > len`.
The body makes these checks in the same order, so the reject kind agrees. -/
forkdef computeCommittee (indices : Array ValidatorIndex) (seed : Bytes32) (index count : Nat) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let len := indices.size
  if 2 ^ 64 ≤ index ∨ 2 ^ 64 ≤ count then
    throwArithmetic "compute_committee: index or count is not a uint64"

  -- `start` and `end`, each a checked `uint64` product and then a floor division.
  let lo ← checkedMul (UInt64.ofNat len) (UInt64.ofNat index) "compute_committee: len(indices) * index"
  if count == 0 then throwArithmetic "compute_committee: // count with count = 0"
  let start := (lo / UInt64.ofNat count).toNat
  let next ← checkedAdd (UInt64.ofNat index) 1 "compute_committee: index + 1"
  let hi ← checkedMul (UInt64.ofNat len) next "compute_committee: len(indices) * (index + 1)"
  let stop := (hi / UInt64.ofNat count).toNat

  -- The slice, one shuffled read per entry.
  if stop ≤ start then return #[]
  assert (start < len)
  let perm ← computeShuffledPermutation len seed
  assert (stop ≤ len)
  pure <| (Array.range (stop - start)).map (fun j => indices[(perm[start + j]!).toNat]!)

/-- `get_beacon_committee(state, slot, index)` (`phase0/beacon-chain.md:1527-1539`). The
committee number `(slot % SLOTS_PER_EPOCH) * committees_per_slot + index` and the count
`committees_per_slot * SLOTS_PER_EPOCH` are checked `uint64` arithmetic in the pyspec. Python
evaluates the `compute_committee` arguments in order. The count raises first where
`get_active_validator_indices` raises, so the second call of the walk cannot raise. Then
`get_seed` runs, and can raise, before the committee number and the count. -/
forkdef getBeaconCommittee (state : State) (slot : Slot) (index : Nat) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot ← getCommitteeCountPerSlot state epoch
  if 2 ^ 64 ≤ index then throwArithmetic "get_beacon_committee: index is not a uint64"
  let active ← getActiveValidatorIndices state epoch
  let seed ← getSeed state epoch Const.domainBeaconAttester
  let slotBase ← checkedMul (slot % UInt64.ofNat Const.slotsPerEpoch) (UInt64.ofNat committeesPerSlot)
    "get_beacon_committee: (slot % SLOTS_PER_EPOCH) * committees_per_slot"
  let committeeIndex ← checkedAdd slotBase (UInt64.ofNat index)
    "get_beacon_committee: (slot % SLOTS_PER_EPOCH) * committees_per_slot + index"
  let count ← checkedMul (UInt64.ofNat committeesPerSlot) (UInt64.ofNat Const.slotsPerEpoch)
    "get_beacon_committee: committees_per_slot * SLOTS_PER_EPOCH"
  computeCommittee active seed committeeIndex.toNat count.toNat

/-- `get_committee_indices`: the committee indices flagged in `committee_bits`. -/
forkdef getCommitteeIndices {n : Nat} (bits : Bitvector n) : Array Nat :=
  Bitvector.trueIndices bits

/-! ## Electra's balance-weighted sampling

Fulu's pyspec samples proposers and sync committee members with two Electra loops,
`compute_proposer_index` (`electra/beacon-chain.md:600-622`) and
`get_next_sync_committee_indices` (`electra/beacon-chain.md:829-856`).
`compute_balance_weighted_selection` replaces both in Gloas, which defines its own. The
Electra loops read a candidate's validator only when the candidate comes up. So an index past
the registry raises `IndexError` only if the loop reaches it. -/

/-- One acceptance test of Electra's sampling loops, at counter `i` for `candidate`. The steps
run in the pyspec's order. The body hashes `seed ++ uint_to_bytes(i // 16)` and reads the 16-bit
random value at `i % 16 * 2`. It then reads `state.validators[candidate]`, which raises
`IndexError` past the registry (`sszGetIdx`, `.outOfBounds`). Last, it forms the two `uint64`
products, `effective_balance * MAX_RANDOM_VALUE` and then
`MAX_EFFECTIVE_BALANCE_ELECTRA * random_value`. A product at or above `2 ^ 64` raises
`.arithmetic`. The second product overflows only when the `Preset` field
`MAX_EFFECTIVE_BALANCE_ELECTRA` is large. -/
forkdef electraAccepts (state : State) (seed : ByteArray) (i : Nat) (candidate : ValidatorIndex) :
    Except StateTransitionError Bool := do
  let randomBytes := sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16)))
  let randomValue := le2 randomBytes ((i % 16) * 2)
  let validator ← sszGetIdx (sszGet state validators) candidate.toNat
  let weight := validator.effectiveBalance.toNat * Const.maxRandomValue
  if 2 ^ 64 ≤ weight then
    throwArithmetic "electra sampling: effective_balance * MAX_RANDOM_VALUE"
  let threshold := Const.maxEffectiveBalanceElectra * randomValue
  if 2 ^ 64 ≤ threshold then
    throwArithmetic "electra sampling: MAX_EFFECTIVE_BALANCE_ELECTRA * random_value"
  pure (weight ≥ threshold)

/-- `compute_proposer_index`'s `while True` loop, one call per pass. The candidate is
`indices[compute_shuffled_index(i % total, total, seed)]`. That call passes its assert and
reads entry `i % total` of the one permutation `perm`, a position below `total`. The pass
returns the first accepted candidate. Otherwise it runs the `uint64` `i += 1` through
`checkedSucc`, which raises `.arithmetic` past `2 ** 64 - 1`. -/
forkdef cpiAux (state : State) (indices perm : Array ValidatorIndex) (seed : ByteArray) (i : Nat) :
    Except StateTransitionError ValidatorIndex := do
  let candidate := indices[(perm[i % indices.size]!).toNat]!
  if ← electraAccepts state seed i candidate then return candidate
  let s ← checkedSucc i "compute_proposer_index: i += 1 past 2**64 - 1"
  cpiAux state indices perm seed s.val
termination_by counterBudgetUInt64 i

/-- `compute_proposer_index(state, indices, seed)` (Electra). An empty `indices` fails the
spec's `assert len(indices) > 0`. The first pass calls `compute_shuffled_index`, so the
permutation is computed, and can fault, before any candidate is read. -/
forkdef computeProposerIndex (state : State) (indices : Array ValidatorIndex) (seed : ByteArray) :
    Except StateTransitionError ValidatorIndex := do
  assert (indices.size > 0)
  let perm ← computeShuffledPermutation indices.size seed
  cpiAux state indices perm seed 0

/-- `get_next_sync_committee_indices`'s `while` loop (Electra), one call per pass. The size
check exits first. The candidate is `active[compute_shuffled_index(i % count, count, seed)]`,
read off the one permutation `perm` as in `cpiAux`. An accepted candidate joins the selection,
and the `uint64` `i += 1` runs through `checkedSucc`. -/
forkdef syncAux (state : State) (active perm : Array ValidatorIndex) (seed : ByteArray) (i : Nat)
    (selected : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  if selected.size ≥ Const.syncCommitteeSize then return selected
  let candidate := active[(perm[i % active.size]!).toNat]!
  let selected := if ← electraAccepts state seed i candidate then selected.push candidate else selected
  let s ← checkedSucc i "get_next_sync_committee_indices: i += 1 past 2**64 - 1"
  syncAux state active perm seed s.val selected
termination_by counterBudgetUInt64 i

/-- `get_next_sync_committee_indices(state)` (Electra). `get_current_epoch(state) + 1` is a
checked `uint64` add, and `get_seed` can raise. The function has no assert. With no active
validator, the first pass's `i % active_validator_count` raises `ZeroDivisionError`
(`.arithmetic`). With `SYNC_COMMITTEE_SIZE = 0`, the loop never runs and returns `[]`. -/
forkdef getNextSyncCommitteeIndices (state : State) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let epoch ← checkedAdd (currentEpochOf state) 1 "get_next_sync_committee_indices: get_current_epoch(state) + 1"
  let active ← getActiveValidatorIndices state epoch
  let seed ← getSeed state epoch Const.domainSyncCommittee
  if Const.syncCommitteeSize == 0 then return #[]
  if active.size == 0 then
    throwArithmetic "get_next_sync_committee_indices: i % active_validator_count with no active validator"
  let perm ← computeShuffledPermutation active.size seed
  syncAux state active perm seed 0 #[]

/-! ## Proposer and sync-committee selection -/

/-- `compute_proposer_indices` (`fulu/beacon-chain.md:343-352`): one Electra
`compute_proposer_index` per slot of `epoch`, each on its own seed
`hash(seed + uint_to_bytes(start_slot + i))`. `start_slot` is a multiple of `SLOTS_PER_EPOCH`,
so `start_slot + i` stays below the next multiple and cannot wrap. The loop stops at the first
selection that raises, as the pyspec list comprehension does. -/
forkdef computeProposerIndices (state : State) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  let startSlot ← computeStartSlotAtEpoch epoch
  (Array.range Const.slotsPerEpoch).mapM (fun i =>
    computeProposerIndex state indices (sha (seed ++ uint64ToBytes (startSlot + UInt64.ofNat i))))

/-- `get_beacon_proposer_index`: read the precomputed Fulu lookahead (no shuffle). -/
forkdef getBeaconProposerIndex (state : State) : ValidatorIndex :=
  vmodGet (sszGet state proposerLookahead) (sszGet state slot) Const.slotsPerEpoch

/-- `get_beacon_proposer_indices(state, epoch)`: the per-slot proposers for `epoch`. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let indices ← getActiveValidatorIndices state epoch
  computeProposerIndices state epoch (← getSeed state epoch Const.domainBeaconProposer) indices

/-- `get_next_sync_committee` (`altair/beacon-chain.md:356-364`): the next sync committee from
Electra's `get_next_sync_committee_indices`, with the real BLS `aggregate_pubkey` through the
`[CryptoBackend]` seam. Gloas overrides this declaration with its own selection. -/
forkdef getNextSyncCommittee [CryptoBackend] (state : State) :
    Except StateTransitionError SyncCommittee := do
  let indices ← getNextSyncCommitteeIndices state

  let validators := sszGet state validators
  let pubkeys : Vector BLSPubkey Const.syncCommitteeSize :=
    Vector.ofFn (fun i => (validators[(indices[i.val]!).toNat]?.getD default).pubkey)
  return { pubkeys := pubkeys, aggregatePubkey := blsAggregatePubkeys pubkeys.toArray }

end

end EthCLSpecs.Fulu
