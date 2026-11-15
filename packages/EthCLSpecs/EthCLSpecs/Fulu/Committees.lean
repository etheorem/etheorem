import EthCLSpecs.Fulu.Registry

/-!
# `EthCLSpecs.Fulu.Committees`: shuffling, committees, and balance-weighted selection

The swap-or-not shuffle and everything built on it: seed derivation (`get_seed`),
committee assignment (`get_beacon_committee`), the balance-weighted sampler
(`compute_balance_weighted_selection`) used for proposer and sync-committee
selection, and `get_next_sync_committee`.

These are functions of the boxed `State`; the selection helpers raise through `Checked` /
`Except` where the pyspec's `uint64` arithmetic raises. The epoch and operation
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
        -- `toPlainInt`, the documented `int(x)` read: the swap arithmetic over
        -- `cur` / `flip` is the pyspec's plain-`int` position math.
        Array.ofFn (n := indexCount) (fun i : Fin indexCount =>
          let cur := (indices[i.val]!).toPlainInt
          let flip := (pivot + indexCount - cur) % indexCount
          let position := Nat.max cur flip
          -- One bit of the round's hash stream decides the swap: hash the seed with
          -- the high bytes of `position`, then read bit `position % 8` of the byte at
          -- `(position % 256) / 8`. A set bit moves this slot to `flip`.
          let source := sha (seedRound ++ u32leBytes (position / 256))
          let byteVal := (source.get! ((position % 256) / 8)).toNat
          let bit := (byteVal >>> (position % 8)) % 2
          -- Trusted `CLUint64` route: `flip` / `cur` are positions below `indexCount`,
          -- the active-set size, capped by `VALIDATOR_REGISTRY_LIMIT` far below `2^64`.
          if bit == 1 then CLUint64.trustedOfUInt64 (UInt64.ofNat flip)
          else CLUint64.trustedOfUInt64 (UInt64.ofNat cur)))
      -- Trusted `CLUint64` route: the initial identity permutation is the positions
      -- `0 … indexCount - 1`, all below the registry cap.
      (Array.ofFn (n := indexCount) (fun i : Fin indexCount =>
        CLUint64.trustedOfUInt64 (UInt64.ofNat i.val)))

/-! ## Seeds and committee counts -/

/-- `get_seed(state, epoch, domain_type)` (`fulu/mainnet.py:1483-1490`): hash the domain type,
the epoch, and the randao mix at the lookback epoch. The mix index is the checked `uint64`
chain `epoch + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1`; it raises where that
chain raises, the overflow at `epoch ≥ 2^64 - EPOCHS_PER_HISTORICAL_VECTOR` (the two
subtracts cannot underflow, the sum starts at `EPOCHS_PER_HISTORICAL_VECTOR`). The ring read
is the total route `getRandaoMix` takes: modulo by the proof-carrying divisor, `vget` with
the index provably in range. The epoch serializes through its `val` projection, the SSZ iso
read. -/
forkdef getSeed (state : State) (epoch : Epoch) (domainType : ByteArray) : Checked Bytes32 := do
  let lookbackEpoch ← epoch + Const.epochsPerHistoricalVector - Const.minSeedLookahead - 1
  let mix := vget (sszGet state randaoMixes) (lookbackEpoch % Const.epochsPerHistoricalVectorDiv).toPlainInt
  pure (bytesToRoot (sha (domainType ++ uint64ToBytes epoch.val ++ mix)))

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
  -- `toPlainInt` reason: index-only. `perm[start + j]` names a position in `indices`,
  -- the plain-`Nat` slot the array's `[i]!` read takes; the element itself is the result.
  (Array.range (stop - start)).map (fun j => indices[(perm[start + j]!).toPlainInt]!)

/-- `get_beacon_committee(state, slot, index)` (`fulu/mainnet.py:1508-1519`). `getSeed` is a
checked value now, so the seed binds above `computeCommittee` and the helper raises where the
seed raises. The `slot % SLOTS_PER_EPOCH` index takes the total `PositiveDivisor` route, and
the `.toPlainInt` is index-only; the rest of the index / count arithmetic keeps the `Nat`
spelling it had. That spelling records three dropped raises. The two multiplies lose their
checked tests, and neither can fire: the slot remainder is below `SLOTS_PER_EPOCH` (32 at
mainnet) and `committees_per_slot` is capped at `MAX_COMMITTEES_PER_SLOT` (64 at mainnet), so
each product stays below 2048. The pyspec's `+ index` faults when
`index ≥ 2^64 - (slot % SLOTS_PER_EPOCH) * committees_per_slot`, a condition every
modeled caller already excludes (index < committees_per_slot); closing it also needs
`getCommitteeCountPerSlot` to leave `Nat`, since the pyspec returns `Uint64` and the
`Nat`-operand routes cannot engage otherwise. -/
forkdef getBeaconCommittee (state : State) (slot : Slot) (index : Nat) :
    Checked (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let seed ← getSeed state epoch Const.domainBeaconAttester
  pure (computeCommittee (getActiveValidatorIndices state epoch) seed
    ((slot % Const.slotsPerEpochDiv).toPlainInt * committeesPerSlot + index)
    (committeesPerSlot * Const.slotsPerEpoch))

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
    -- `toPlainInt` reason: index-only. The permuted entry names a position in the
    -- plain-`Nat` arrays `effBals` / `indices`, the slot their `[i]!` reads take.
    let nextIndex := if shuffle then (perm[i % total]!).toPlainInt else i % total
    let weight := effBals[nextIndex]! * Const.maxRandomValue
    let randomValue := le2 randomBytes offset
    let threshold := Const.maxEffectiveBalanceElectra * randomValue
    -- Trusted `CLUint64` route: `indices[nextIndex]` is a registry position, below
    -- the registry size, which `VALIDATOR_REGISTRY_LIMIT` caps far below `2^64`.
    let selected := if weight ≥ threshold
      then selected.push (CLUint64.trustedOfUInt64 (UInt64.ofNat (indices[nextIndex]!)))
      else selected
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
  -- `toPlainInt`, the documented `int(x)` read: the loop's plain-`int` copy of the
  -- index array, the positions `effBals` / `indices` sit under.
  let idxNat := indices.map (·.toPlainInt)
  let validators := sszGet state validators
  -- `toPlainInt` reason: index-only on the read (`getAt` covers plain `Array` only,
  -- `validators` is an `SSZList`); `.effectiveBalance.toPlainInt` is the documented
  -- `int(x)` read, the plain-`int` balance the weight comparison runs on.
  let effBals := indices.map (fun vi => (validators[vi.toPlainInt]!).effectiveBalance.toPlainInt)
  let perm := if shuffle then computeShuffledPermutation total seed else #[]
  cbwsAux idxNat effBals perm seed total size shuffle 0 ByteArray.empty #[]

/-! ## Proposer and sync-committee selection -/

/-- `compute_proposer_indices`: one balance-weighted proposer per slot in `epoch`
(`fulu/mainnet.py:6608-6617`). `computeStartSlotAtEpoch` is a checked value now, so the
start slot binds above the per-slot loop, where the pyspec assigns it. The loop's
`startSlot + i` is the checked `CLUint64` route; its raise cannot fire, because the checked
multiply that produced `startSlot` leaves it a true multiple of `SLOTS_PER_EPOCH` below
`2^64`, `SLOTS_PER_EPOCH` divides `2^64` (a power of two at both presets, 8 and 32), and
`i < SLOTS_PER_EPOCH`; the in-range sum reads back through `val` for the seed
bytes. An empty
`indices` rejects through `computeBalanceWeightedSelection`'s `assert total > 0`. -/
forkdef computeProposerIndices (state : State) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) := do
  let startSlot ← computeStartSlotAtEpoch epoch
  (Array.range Const.slotsPerEpoch).mapM (fun i => do
    let slotI ← startSlot + i
    let sd := sha (seed ++ uint64ToBytes slotI.val)
    return (← computeBalanceWeightedSelection state indices sd 1 true)[0]!)

/-- `get_beacon_proposer_index`: read the precomputed Fulu lookahead (no shuffle). -/
forkdef getBeaconProposerIndex (state : State) : ValidatorIndex :=
  vmodGet (sszGet state proposerLookahead) (sszGet state slot) Const.slotsPerEpoch

/-- `get_beacon_proposer_indices(state, epoch)`: the per-slot proposers for `epoch`. The
seed binds where the pyspec assigns it (`fulu/mainnet.py:6619-6625`). -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let seed ← getSeed state epoch Const.domainBeaconProposer
  computeProposerIndices state epoch seed (getActiveValidatorIndices state epoch)

/-- `get_next_sync_committee`: balance-weighted selection of the next sync committee,
with the real BLS `aggregate_pubkey` through the `[CryptoBackend]` seam. Rejects when no
validator is active next epoch, through `computeBalanceWeightedSelection`. -/
forkdef getNextSyncCommittee [CryptoBackend] (state : State) :
    Except StateTransitionError SyncCommittee := do
  -- `fulu/mainnet.py:4344`: `epoch = get_current_epoch(state) + 1`, the checked `uint64` add.
  let epoch ← currentEpochOf state + 1
  let seed ← getSeed state epoch Const.domainSyncCommittee
  let indices ← computeBalanceWeightedSelection state (getActiveValidatorIndices state epoch)
    seed Const.syncCommitteeSize true

  let validators := sszGet state validators
  let pubkeys : Vector BLSPubkey Const.syncCommitteeSize :=
    -- `toPlainInt` reason: index-only. `indices[i]` names a registry position, the
    -- plain-`Nat` slot the `validators[...]` read takes; the `?.getD default` arm is
    -- the pre-flip spelling and unreachable for a selection output.
    Vector.ofFn (fun i => (validators[(indices[i.val]!).toPlainInt]?.getD default).pubkey)
  return { pubkeys := pubkeys, aggregatePubkey := blsAggregatePubkeys pubkeys.toArray }

end

end EthCLSpecs.Fulu
