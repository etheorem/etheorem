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
single `Array.ofFn` over the previous array. The pyspec returns `Sequence[Uint64]`
positions, never validator indices (`fulu/minimal.py:1252-1275`).

The positions stay structural `Nat`s (`SPEC_ARITHMETIC.md` §4.2), because no step of the
pinned `Uint64` chain can raise here. Every caller passes a registry length, at most
`VALIDATOR_REGISTRY_LIMIT = 2^40`, and every position and `pivot` stay below `index_count`.
So `pivot + index_count - indices[i]` lies in `[1, 2^41)`, and `position // 256` fits the
`Uint32` cast. The bit read `byte_val >> (position % 8)` shifts a plain byte value by a
checked count, so the pinned body range-tests a `Uint64` result. A byte value stays below
`2^8`, so that test passes too. The other width cast, `Uint8(current_round)`, raises in the
pinned body once a preset sets more than `2^8` rounds. The preset premise
`shuffleRoundCountLe` rules such a preset out, so the round byte is a proof-carrying
`CLUint8` and never wraps.

The pinned body forms `pivot = ... % index_count` even for `index_count = 0` and raises
`ZeroDivisionError` there. No pinned caller reaches that case: `compute_committee` calls the
shuffle once per position of its range, which is empty for an empty registry. The
balance-weighted selection asserts `total > 0` first, and Fulu's
`get_next_sync_committee_indices` raises `ZeroDivisionError` on `i % active_validator_count`
before its first `compute_shuffled_index` call. The `index_count = 0` branch below
returns the empty permutation, which `computeCommittee` forms for an empty registry and never
reads. -/
forkdef computeShuffledPermutation (indexCount : Nat) (seed : ByteArray) : Array Nat :=
  if indexCount == 0 then #[]
  else
    (List.finRange Const.shuffleRoundCount).foldl
      (fun indices round =>
        -- Each round mixes in a fresh seed byte and draws the swap pivot. The byte is
        -- `uint_to_bytes(Uint8(current_round))`: the checked width-8 narrowing, built
        -- proof-carrying because `round < shuffleRoundCount ≤ 2 ^ 8` (the preset premise).
        -- `.val` reads the checked value's wire byte, the codec boundary of §4.5.
        let roundByte : CLUint8 := CLUint8.ofNatLT round.val
          (Nat.lt_of_lt_of_le round.isLt Const.shuffleRoundCountLe)
        let seedRound := seed.push roundByte.val
        let pivot := (le8 (sha seedRound)) % indexCount

        -- Rebuild every slot independently: swap to `flip`, or keep `cur`. Both `!` reads
        -- are structural: every round's array has `indexCount` entries, so `indices[i]` is
        -- in range, and `source` is a 32-byte digest read at `(position % 256) / 8 < 32`.
        Array.ofFn (n := indexCount) (fun i : Fin indexCount =>
          let cur := indices[i.val]!
          let flip := (pivot + indexCount - cur) % indexCount
          let position := Nat.max cur flip
          -- One bit of the round's hash stream decides the swap: hash the seed with
          -- the high bytes of `position`, then read bit `position % 8` of the byte at
          -- `(position % 256) / 8`. A set bit moves this slot to `flip`.
          let source := sha (seedRound ++ u32leBytes (position / 256))
          let byteVal := (source.get! ((position % 256) / 8)).toNat
          let bit := (byteVal >>> (position % 8)) % 2
          if bit == 1 then flip else cur))
      (Array.ofFn (n := indexCount) (fun i : Fin indexCount => i.val))

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

/-- `get_committee_count_per_slot` (`fulu/minimal.py:1485-1496`):
`max(Uint64(1), min(MAX_COMMITTEES_PER_SLOT, Uint64(len(active)) // Uint64(SLOTS_PER_EPOCH)
// TARGET_COMMITTEE_SIZE))`. Every operand is a `Uint64`, so the result is a `Uint64`.
The active set's checked `ValidatorIndex` casts carry their fault into the result. The
`Uint64(len(...))` cast cannot fault, since a registry length is below `2^40`. The division by
`SLOTS_PER_EPOCH` takes the proved-total divisor view (`SPEC_ARITHMETIC.md` §4.2), and the
division by `TARGET_COMMITTEE_SIZE` is the checked operator, which raises `ZeroDivisionError`
for a zero preset value. `min` and `max` then pick an operand. -/
forkdef getCommitteeCountPerSlot (state : State) (epoch : Epoch) : Checked CLUint64 := do
  let active ← getActiveValidatorIndices state epoch
  let activeCount ← (len active).toCLUint64?
  let perSlot := activeCount / Const.slotsPerEpochDiv
  let perCommittee ← perSlot / Const.targetCommitteeSizeC
  pure (max 1 (min Const.maxCommitteesPerSlotC perCommittee))

/-! ## Committee assignment -/

/-- `compute_committee` (`fulu/minimal.py:1310-1321`): slice `[start, end)` of the shuffled
`indices`. `index` and `count` are checked `Uint64` values, so the bounds are the pyspec's
checked chains: `start = (len(indices) * index) // count` and
`end = (len(indices) * Uint64(index + 1)) // count`. The plain `len(indices)`, a `CLInt`,
times a checked operand is the mixed route, which computes on the original operands and
raises past `2^64 - 1`, and `// count` raises `ZeroDivisionError` on a zero count. Each step
binds in Python's order, so the fault depends on `index` as well as on the registry size.

The comprehension then calls `compute_shuffled_index(Uint64(index), Uint64(len(indices)),
seed)` for each position of `range(start, end)`, and `compute_shuffled_index`
(`fulu/minimal.py:1278-1283`) asserts `index < index_count` first. With `index < count` the
slice ends at or below `len(indices)`, so the assert holds at every position. A committee
index at or past `count` with a nonempty range starts at or past `len(indices)`, so the
first position raises `AssertionError`, the `.assert` reject. The bounds' checked faults come
first, as in Python. `Checked` carries no assert, so the result is `Except
StateTransitionError`, and each checked step lifts into it. -/
forkdef computeCommittee (indices : Array ValidatorIndex) (seed : Bytes32) (index count : CLUint64) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let indexCount := len indices
  let startProduct ← indexCount * index
  let start ← startProduct / count
  -- The annotation fixes the add's result kind: under the lift the expected type alone
  -- does not name it, so the next product could not pick its instance.
  let nextIndex : CLUint64 ← index + 1
  let stopProduct ← indexCount * nextIndex
  let stop ← stopProduct / count
  -- The shuffle takes the registry length as its structural `Nat` count (see
  -- `computeShuffledPermutation`).
  let perm := computeShuffledPermutation indices.size seed
  -- `toPlainNat`: `range(start, end)` iterates plain positions between two nonnegative
  -- checked bounds, so the bounds' values name the same positions, and the `Nat` difference
  -- is zero exactly where Python's range is empty. The positions ascend, so the first one
  -- at or past `len(indices)` is the one that raises.
  (Array.range (stop.toPlainNat - start.toPlainNat)).mapM fun j => do
    let position := start.toPlainNat + j
    -- `Uint64(index)` of a position below `end ≤ 2^64 - 1` cannot raise, so the assert of
    -- `compute_shuffled_index` is the first check that can fail at this position.
    assert (position < indices.size)
    -- Structural reads: `perm` is a permutation of `[0, len(indices))`, so the assert
    -- bounds `perm[position]` and every entry of `perm` bounds the `indices` read.
    pure indices[perm[position]!]!

/-- `get_beacon_committee(state, slot, index)` (`fulu/minimal.py:1500-1514`). The seed walk
is `get_seed`, which raises on its checked epoch chain, so the helper carries the fault and
each caller binds it. The pyspec forms the count, then the keyword arguments in order: the
active set, the seed, the index, the count. The index
`Uint64(slot % SLOTS_PER_EPOCH) * committees_per_slot + index` takes the proved-total
divisor view for the remainder (`SPEC_ARITHMETIC.md` §4.2), then the checked product and
the checked add of the `CommitteeIndex`; the count `committees_per_slot *
Uint64(SLOTS_PER_EPOCH)` is the checked product. `committees_per_slot` is the `Uint64` that
`get_committee_count_per_slot` returns, so both products are checked `Uint64` products.
`compute_committee` adds the assert of `compute_shuffled_index`, so the result is `Except
StateTransitionError`, and the checked steps lift into it. -/
forkdef getBeaconCommittee (state : State) (slot : Slot) (index : CommitteeIndex) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot ← getCommitteeCountPerSlot state epoch
  let active ← getActiveValidatorIndices state epoch
  let seed ← getSeed state epoch Const.domainBeaconAttester
  let slotInEpoch := slot % Const.slotsPerEpochDiv
  let slotOffset ← slotInEpoch * committeesPerSlot
  let committeeIndex ← slotOffset + index
  let count ← committeesPerSlot * Const.slotsPerEpochC
  computeCommittee active seed committeeIndex count

/-- `get_committee_indices` (`fulu/minimal.py:5948-5949`): the committee indices flagged in
`committee_bits`. Each is the `CommitteeIndex(index)` cast of a plain position, the pyspec's
checked narrowing, so the result is `Checked`. -/
forkdef getCommitteeIndices {n : Nat} (bits : Bitvector n) : Checked (Array CommitteeIndex) :=
  (Bitvector.trueIndices bits).mapM CLUint64.ofNat?

/-! ## Balance-weighted selection -/

/-- `compute_balance_weighted_selection` inner loop, one call per pass of the spec's
`while len(selected) < size`. The size check exits first. The `weight` and `threshold`
products are the spec's checked `Gwei` chains (`effective_balances[next_index] *
MAX_RANDOM_VALUE`, `MAX_EFFECTIVE_BALANCE_ELECTRA * random_value`), so each binds before
the comparison, and the comparison runs only after both formed. The tail increment runs the
spec's `uint64` `i += 1` through `checkedSucc`, so the last pass at `i = 2**64 - 1` throws
`.arithmetic`, the spec's overflow, whether or not it filled the selection. -/
forkdef cbwsAux [Preset] (indices : Array ValidatorIndex) (perm : Array Nat) (effBals : Array Gwei)
    (seed : ByteArray) (total size : Nat) (shuffle : Bool) (i : Nat) (randomBytes : ByteArray)
    (selected : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  if selected.size ≥ size then pure selected
  else
    -- `i` is the pinned `Uint64` counter, kept a structural `Nat` below `2^64` by the
    -- `checkedSucc` budget, so `i % 16 * 2`, `i // 16`, and `i % total` (with `total > 0`
    -- asserted) cannot raise, and `UInt64.ofNat (i / 16)` is exact: the codec bytes of
    -- `uint_to_bytes(i // 16)`.
    let offset := (i % 16) * 2
    let randomBytes := if offset == 0 then sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else randomBytes
    -- The `!` reads below are structural. `perm` is the shuffle of `[0, total)` and has
    -- `total` entries, so `perm[i % total]` is in range and `nextIndex < total`. `effBals`
    -- and `indices` both have `total` entries, so neither read can default.
    let nextIndex := if shuffle then perm[i % total]! else i % total
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
`Gwei` kind (`SPEC_ARITHMETIC.md` §4.2, each intermediate range test). The
`effective_balances` comprehension reads `state.validators[index]` for every candidate
after the assert; each read raises `IndexError` past the end, so it goes through `getAt`. -/
forkdef computeBalanceWeightedSelection (state : State) (indices : Array ValidatorIndex)
    (seed : ByteArray) (size : Nat) (shuffle : Bool) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let total := indices.size
  assert (total > 0)
  let validators := sszGet state validators
  let effBals ← indices.mapM fun vi => do
    let validator ← liftErr (getAt validators vi)
    pure validator.effectiveBalance
  let perm := if shuffle then computeShuffledPermutation total seed else #[]
  cbwsAux indices perm effBals seed total size shuffle 0 ByteArray.empty #[]

/-! ## Proposer and sync-committee selection -/

/-- `compute_proposer_indices`: one balance-weighted proposer per slot in `epoch`. An empty
`indices` rejects through `computeBalanceWeightedSelection`'s `assert total > 0`. The pinned
body (`fulu/minimal.py:6606-6608`) runs in two phases: the `seeds` list forms every checked
`start_slot + index` add first, then the selection runs once per seed. A range fault at any
index therefore precedes the selection assert at index `0`. The seed feed `uint64_to_bytes`
reads the checked value's underlying word, the codec boundary §4.5 asks each projection to
name.

The pinned Fulu body draws each proposer with `compute_proposer_index`, which returns
before its `i += 1`. The shared sampler increments after a selection, so the two differ
only when the pass at `i = 2^64 - 1` selects. That pass needs `2^64 - 1` earlier
rejections, so no run reaches it. The `[0]!` read is structural: a selection of size `1`
returns exactly one entry. -/
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

/-- `get_beacon_proposer_indices(state, epoch)`: the per-slot proposers for `epoch`. The
pyspec forms the active set (its checked casts) before the seed (`fulu/minimal.py`,
`get_beacon_proposer_indices`). -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let indices ← getActiveValidatorIndices state epoch
  let seed ← getSeed state epoch Const.domainBeaconProposer
  computeProposerIndices state epoch seed indices

/-- `get_next_sync_committee_indices` (`fulu/minimal.py:4332-4359`): the balance-weighted
draw of the next sync committee's indices. The Fulu body forms the active set, then the seed,
then runs its own loop. That loop has no `assert`, and a zero `SYNC_COMMITTEE_SIZE` runs no
pass. Otherwise its first pass forms
`i % active_validator_count`, so an empty active set raises `ZeroDivisionError` there, the
`.zeroDivision` cause, which no reference wrapper catches. A nonempty set draws the same
indices as `computeBalanceWeightedSelection` with `shuffle = true`: `compute_shuffled_index`
at each position agrees with the shuffled permutation, and every active index is in the
registry, so reading all effective balances first raises nowhere the loop does not. -/
forkdef getNextSyncCommitteeIndices (state : State) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let epoch ← currentEpochOf state + 1
  let active ← getActiveValidatorIndices state epoch
  let seed ← getSeed state epoch Const.domainSyncCommittee
  -- `while len(sync_committee_indices) < SYNC_COMMITTEE_SIZE` runs no pass for a zero
  -- preset size. Otherwise the first pass forms `i % active_validator_count`.
  if Const.syncCommitteeSize == 0 then return #[]
  if active.size == 0 then
    throw (.zeroDivision "get_next_sync_committee_indices: i % active_validator_count")
  computeBalanceWeightedSelection state active seed Const.syncCommitteeSize true

/-- `get_next_sync_committee`: the next sync committee over the indices of
`getNextSyncCommitteeIndices`, with the real BLS `aggregate_pubkey` through the
`[CryptoBackend]` seam. Each fork's index draw decides how an empty active set rejects. The
pyspec reads `state.validators[index].pubkey` for each selected index, a read that raises
`IndexError` past the end, so it goes through `getAt`. -/
forkdef getNextSyncCommittee [CryptoBackend] (state : State) :
    Except StateTransitionError SyncCommittee := do
  let indices ← getNextSyncCommitteeIndices state

  let validators := sszGet state validators
  let selected ← indices.mapM fun vi => do
    let validator ← liftErr (getAt validators vi)
    pure validator.pubkey
  -- Structural: the selection loop stops at exactly `SYNC_COMMITTEE_SIZE` entries.
  let pubkeys : Vector BLSPubkey Const.syncCommitteeSize :=
    Vector.ofFn (fun i => selected[i.val]!)
  return { pubkeys := pubkeys, aggregatePubkey := blsAggregatePubkeys pubkeys.toArray }

end

end EthCLSpecs.Fulu
