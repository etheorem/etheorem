import EthCLSpecs.Fulu.Registry

/-!
# `EthCLSpecs.Fulu.Committees`: shuffling, committees, and balance-weighted selection

The swap-or-not shuffle and everything built on it: seed derivation (`get_seed`),
committee assignment (`get_beacon_committee`), the balance-weighted sampler
(`compute_balance_weighted_selection`) used for proposer and sync-committee
selection, and `get_next_sync_committee`.

The epoch and operation steps call these functions of the boxed `State`. They hash through
the `[HasherTag]` seam (`sha`), so they compute the same swap-or-not bytes a real client
computes. Performance is adequate for the minimal preset. Each committee recomputes the
permutation.

A function here returns a bare `Except` when the pyspec can raise in it, as
`computeStartSlotAtEpoch` does. It raises where the pyspec raises, with the reject kind that
the runner sees. Two kinds occur:

* `.arithmetic`: the `uint64` encodings and products of the shuffle and the committee slice.
  The pyspec raises an uncaught `OverflowError`, `ValueError` or `ZeroDivisionError` there.
* `.assert`: the asserts of `compute_shuffled_index` and of the balance-weighted selection.

The loop of the weighted sampler stops when it has selected `size` candidates. No structural
measure bounds this loop. The pyspec loop has no bound either. The sampler is therefore a
`partial_fixpoint`.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-! ## The swap-or-not shuffle -/

/-- `compute_shuffled_permutation` (`phase0/beacon-chain.md:819-842`): the swap-or-not
shuffle (`SHUFFLE_ROUND_COUNT` rounds). Each position evolves independently from its own
value, so one round is a single `Array.ofFn` over the previous array.

The pyspec raises an uncaught fault (`.arithmetic`) in three places. The body checks them
first, in the order that the pyspec reaches them:

1. Round 0 computes `% index_count`. This divides by zero when `index_count = 0`.
2. Round 0 reaches the value `n - 1`. Its bucket `position // 256` overflows `to_bytes(4)`
   when `n > 2 ^ 40`, and only then.
3. Round 256 computes `current_round.to_bytes(1)`, which overflows. Rounds `0 … 255` run
   before it.

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
    throwArithmetic "compute_shuffled_permutation: position_bucket.to_bytes(4) past 2 ** 32"
  if 256 < Const.shuffleRoundCount then
    throwArithmetic "compute_shuffled_permutation: current_round.to_bytes(1) at round 256"
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

/-- `compute_committee` (`phase0/beacon-chain.md:881-892`): slice `[start, end)` of the
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

/-- `get_beacon_committee(state, slot, index)` (`phase0/beacon-chain.md:1098-1111`). The
committee number `(slot % SLOTS_PER_EPOCH) * committees_per_slot + index` and the count
`committees_per_slot * SLOTS_PER_EPOCH` are checked `uint64` arithmetic in the pyspec. -/
forkdef getBeaconCommittee (state : State) (slot : Slot) (index : Nat) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  if 2 ^ 64 ≤ index then throwArithmetic "get_beacon_committee: index is not a uint64"
  let slotBase ← checkedMul (slot % UInt64.ofNat Const.slotsPerEpoch) (UInt64.ofNat committeesPerSlot)
    "get_beacon_committee: (slot % SLOTS_PER_EPOCH) * committees_per_slot"
  let committeeIndex ← checkedAdd slotBase (UInt64.ofNat index)
    "get_beacon_committee: (slot % SLOTS_PER_EPOCH) * committees_per_slot + index"
  let count ← checkedMul (UInt64.ofNat committeesPerSlot) (UInt64.ofNat Const.slotsPerEpoch)
    "get_beacon_committee: committees_per_slot * SLOTS_PER_EPOCH"
  computeCommittee (getActiveValidatorIndices state epoch) (getSeed state epoch Const.domainBeaconAttester)
    committeeIndex.toNat count.toNat

/-- `get_committee_indices`: the committee indices flagged in `committee_bits`. -/
forkdef getCommitteeIndices {n : Nat} (bits : Bitvector n) : Array Nat :=
  Bitvector.trueIndices bits

/-! ## Balance-weighted selection -/

/-- `compute_balance_weighted_selection` inner loop (`gloas/beacon-chain.md:694-711`).

The loop stops when `selected` reaches `size`. A candidate that fails the weight threshold
fills no slot, so no measure decreases on each iteration. The loop stops with probability 1,
but no structural argument shows it. The pyspec loop has no bound, so this loop has none
either. A fuel bound returns a short list where the pyspec continues. A pinned run took
11,380,081 iterations for 160 picks over four zero-balance candidates.

`partial_fixpoint` defines the loop without a termination argument. It needs the recursive
call in tail position. Lean generates the unfolding equation of the loop, and a proof can
rewrite with it.

The pyspec checks two products as `uint64` arithmetic, in this order in each iteration:
`effective_balance * MAX_RANDOM_VALUE`, then `MAX_EFFECTIVE_BALANCE_ELECTRA * random_value`
after the read of `random_value`. A product at or above `2 ^ 64` raises `.arithmetic`. The
second product overflows only when the `Preset` field `MAX_EFFECTIVE_BALANCE_ELECTRA` is large. -/
forkdef cbwsAux [Preset] (indices effBals : Array Nat) (perm : Array ValidatorIndex)
    (seed : ByteArray) (total size : Nat) (shuffle : Bool) (i : Nat) (randomBytes : ByteArray)
    (selected : Array ValidatorIndex) : Except StateTransitionError (Array ValidatorIndex) :=
  if selected.size ≥ size then .ok selected
  else
    let offset := (i % 16) * 2
    let randomBytes := if offset == 0 then sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else randomBytes
    let nextIndex := if shuffle then (perm[i % total]!).toNat else i % total
    let weight := effBals[nextIndex]! * Const.maxRandomValue
    if 2 ^ 64 ≤ weight then
      throwArithmetic "compute_balance_weighted_selection: effective_balance * MAX_RANDOM_VALUE"
    else
      let randomValue := le2 randomBytes offset
      let threshold := Const.maxEffectiveBalanceElectra * randomValue
      if 2 ^ 64 ≤ threshold then
        throwArithmetic "compute_balance_weighted_selection: MAX_EFFECTIVE_BALANCE_ELECTRA * random_value"
      else
        let selected := if weight ≥ threshold then selected.push (UInt64.ofNat (indices[nextIndex]!)) else selected
        cbwsAux indices effBals perm seed total size shuffle (i + 1) randomBytes selected
partial_fixpoint

/-- `compute_balance_weighted_selection(state, indices, seed, size, shuffle)`
(`gloas/beacon-chain.md:675-711`). The pyspec asserts `total > 0` first (`.assert`). With
`shuffle_indices`, each iteration calls `compute_shuffled_index`. So the shuffle runs, and can
fault, only when the loop runs at least once, which needs `size > 0`. -/
forkdef computeBalanceWeightedSelection (state : State) (indices : Array ValidatorIndex)
    (seed : ByteArray) (size : Nat) (shuffle : Bool) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let total := indices.size
  assert (0 < total)
  let idxNat := indices.map (·.toNat)
  let validators := sszGet state validators
  let effBals := indices.map (fun vi => (validators[vi.toNat]!).effectiveBalance.toNat)
  let perm ← if shuffle && 0 < size then computeShuffledPermutation total seed else pure #[]
  cbwsAux idxNat effBals perm seed total size shuffle 0 ByteArray.empty #[]

/-! ## Proposer and sync-committee selection -/

/-- `compute_proposer_indices`: one balance-weighted proposer per slot in `epoch`.

For each slot, Fulu's pyspec runs Electra's `compute_proposer_index` loop
(`electra/beacon-chain.md:450-472`). Gloas's pyspec runs `compute_balance_weighted_selection`
(`gloas/beacon-chain.md:717-729`). The two pick the same proposer: a pinned run agreed on 30
of 30 random states. Both assert a nonempty candidate list first. So one body serves both
forks. -/
forkdef computeProposerIndices (state : State) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : StateTransition (Array ValidatorIndex) := do
  let startSlot ← liftErr (computeStartSlotAtEpoch epoch)
  -- The loop reads no state, so it runs in `Except` and the body lifts it once. It stops at
  -- the first selection that raises, as the pyspec list comprehension does.
  liftErr <| (Array.range Const.slotsPerEpoch).mapM (fun i => do
    let sd := sha (seed ++ uint64ToBytes (startSlot + UInt64.ofNat i))
    let picked ← computeBalanceWeightedSelection state indices sd 1 true
    pure picked[0]!)

/-- `get_beacon_proposer_index`: read the precomputed Fulu lookahead (no shuffle). -/
forkdef getBeaconProposerIndex (state : State) : ValidatorIndex :=
  vmodGet (sszGet state proposerLookahead) (sszGet state slot) Const.slotsPerEpoch

/-- `get_beacon_proposer_indices(state, epoch)`: the per-slot proposers for `epoch`. -/
forkdef getBeaconProposerIndices (state : State) (epoch : Epoch) :
    StateTransition (Array ValidatorIndex) :=
  computeProposerIndices state epoch (getSeed state epoch Const.domainBeaconProposer)
    (getActiveValidatorIndices state epoch)

/-- `get_next_sync_committee`: balance-weighted selection of the next sync committee,
with the real BLS `aggregate_pubkey` through the `[CryptoBackend]` seam.

Fulu's pyspec selects with Electra's `get_next_sync_committee_indices`
(`electra/beacon-chain.md:679-705`). That function has no assert. With no active validator,
its `i % active_validator_count` raises `ZeroDivisionError`, an uncaught fault
(`.arithmetic`). This body checks that case before it calls the shared selection. The
selection's own assert is the Gloas behavior, and Gloas overrides this declaration without
the check. -/
forkdef getNextSyncCommittee [CryptoBackend] (state : State) :
    Except StateTransitionError SyncCommittee := do
  let epoch := currentEpochOf state + 1
  let seed := getSeed state epoch Const.domainSyncCommittee
  let active := getActiveValidatorIndices state epoch
  if active.size == 0 && 0 < Const.syncCommitteeSize then
    throwArithmetic "get_next_sync_committee_indices: i % active_validator_count with no active validator"
  let indices ← computeBalanceWeightedSelection state active seed Const.syncCommitteeSize true

  let validators := sszGet state validators
  let pubkeys : Vector BLSPubkey Const.syncCommitteeSize :=
    Vector.ofFn (fun i => (validators[(indices[i.val]!).toNat]?.getD default).pubkey)
  pure { pubkeys := pubkeys, aggregatePubkey := blsAggregatePubkeys pubkeys.toArray }

end

end EthCLSpecs.Fulu
