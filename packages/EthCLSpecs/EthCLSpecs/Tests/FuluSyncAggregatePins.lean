import EthCLSpecs.Fulu.Transition
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Tests.FuluSyncAggregatePins`: the keys `process_sync_aggregate` verifies

Each pin states what the pinned pyspec (`v1.7.0-alpha.11`, minimal preset) does on the same
input. The probe script that produced the pyspec side is `.tmp/batchfaith/probe_b5.py` (local,
not committed). `ValueError` is `.arithmetic`, `AssertionError` is `.assert`.

A capture backend shows which keys reach `eth_fast_aggregate_verify`. Its verify accepts one
expected key list and rejects all others. So a run that succeeds shows the keys that the body
chose. The other key operations use the real FFI.

The base fixture is the `default` state at slot 1. Its registry holds 32 active 32 ETH
validators, and their keys are the sync committee, in order. A pin that changes the slot, the
registry, a committee key or the stored aggregate passes that change to `fixture`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluSyncAggregatePins

open EthCLSpecs.Fulu
open EthCLLib.Proofs (runPure)
open EthCLSpecs.Proofs.Fulu (FuluRun)

section
-- The pins share one preset, config and hasher. The instances stay local to this section.
-- Each pin names its crypto backend.
local instance : Preset := minimal
local instance : Config := minimalConfig
local instance : HasherTag := fastHasherTag

/-- The result raised the uncaught-fault kind (`.arithmetic`). -/
private def isArith {α : Type} : Except StateTransitionError α → Bool
  | .error (.arithmetic _) => true
  | _ => false

/-- The result raised the assertion kind (`.assert`). -/
private def isAssert {α : Type} : Except StateTransitionError α → Bool
  | .error (.assert _) => true
  | _ => false

/-- The run succeeded. -/
private def isOk {α : Type} : Except StateTransitionError α → Bool
  | .ok _ => true
  | _ => false

/-- The real FFI, except that the verify accepts only the key list `expected`. -/
@[reducible] private def capture (expected : Array BLSPubkey) : CryptoBackend :=
  { CryptoBackend.ffi with
    ethFastAggregateVerify := fun pks _ _ =>
      pks.map (·.toList) == expected.map (fun k => (vecToBytes k).toList) }

/-- The real FFI, except that the verify rejects every input. -/
@[reducible] private def rejectAll : CryptoBackend :=
  { CryptoBackend.ffi with ethFastAggregateVerify := fun _ _ _ => false }

private def eth32 : Gwei := 32000000000

/-- The committee keys: the public keys of the secret keys `1` to `32`. -/
private def keys : Array BLSPubkey := (Array.range Const.syncCommitteeSize).map fun i =>
  bytesToVec 48 (LeanHazmat.Bls.skToPk ⟨(Array.replicate 31 (0 : UInt8)).push (i + 1).toUInt8⟩)

/-- Bytes that do not decode as a G1 point (the compression flag is clear). -/
private def badKey : BLSPubkey := Vector.replicate 48 0x22

/-- The compressed G1 identity, which decodes but fails `KeyValidate`. -/
private def identityKey : BLSPubkey := (Vector.replicate 48 0).set 0 0xc0

/-- The aggregate of a key list, through the real FFI. -/
private def aggregateOf (ks : Array BLSPubkey) : BLSPubkey :=
  bytesToVec 48 (LeanHazmat.Bls.ethAggregatePubkeys (ks.map vecToBytes))

/-- The SSZ list of `a`. Every fixture array is far below the list limit, so the empty-list
branch never runs. The branch exists because `fixture` takes its arrays as variables. -/
private def listOf {α : Type} {cap : Nat} (a : Array α) : SSZList α cap :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], Nat.zero_le _⟩

/-- The fixture: `committee` as the sync committee with stored aggregate `aggregate`, and
`registry` as the validator keys. -/
private def fixture (committee : Array BLSPubkey) (aggregate : BLSPubkey)
    (registry : Array BLSPubkey := keys) (slot : Slot := 1) : BeaconState :=
  let validator (pk : BLSPubkey) : Validator :=
    { (default : Validator) with
      pubkey := pk, effectiveBalance := eth32
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : BeaconState) with
    slot := slot
    validators := listOf (registry.map validator)
    balances := listOf (registry.map fun _ => eth32)
    previousEpochParticipation := listOf (registry.map fun _ => 0)
    currentEpochParticipation := listOf (registry.map fun _ => 0)
    inactivityScores := listOf (registry.map fun _ => 0)
    currentSyncCommittee :=
      { pubkeys := Vector.ofFn fun i => committee[i.val]!, aggregatePubkey := aggregate } }

/-- A sync aggregate with the first `k` bits set. -/
private def firstBits (k : Nat) : SyncAggregate :=
  { (default : SyncAggregate) with syncCommitteeBits := ⟨BitVec.ofNat _ (2 ^ k - 1)⟩ }

/-- `process_sync_aggregate` on `st`, under the backend `cb`. -/
private def run (cb : CryptoBackend) (k : Nat) (st : BeaconState) :
    Except StateTransitionError (Unit × BeaconState) :=
  letI := cb
  runPure (processSyncAggregate (StateTransition := FuluRun) (firstBits k)) st

/-! ## P5: the key choice -/

-- All 32 bits set: the verify gets the stored aggregate unchanged. The stored bytes do not
-- decode as a G1 point, and the run still succeeds, so the body does not decode them.
example : isOk (run (capture #[badKey]) 32 (fixture keys badKey)) = true := by native_decide

-- 31 bits set: the verify gets the stored aggregate minus the one non-participant key. That
-- difference is the aggregate of the 31 participant keys.
example : isOk (run (capture #[aggregateOf (keys.extract 0 31)]) 31
    (fixture keys (aggregateOf keys))) = true := by native_decide

-- 17 bits set, the smallest count above half of 32: the verify gets the stored aggregate
-- minus the 15 non-participant keys.
example : isOk (run (capture #[aggregateOf (keys.extract 0 17)]) 17
    (fixture keys (aggregateOf keys))) = true := by native_decide

-- 16 bits set, exactly half: the verify gets the 16 participant keys.
example : isOk (run (capture (keys.extract 0 16)) 16 (fixture keys (aggregateOf keys))) = true := by
  native_decide

-- One bit set: the verify gets that participant's key. The body does not read the stored
-- aggregate.
example : isOk (run (capture #[keys[0]!]) 1 (fixture keys badKey)) = true := by native_decide

-- 31 bits set and a stored aggregate that does not decode: `bytes48_to_G1` raises `ValueError`.
example : isArith (run (capture #[]) 31 (fixture keys badKey)) = true := by native_decide

-- 31 bits set and a non-participant key that does not decode: `AggregatePKs` raises
-- `ValueError`.
example : isArith (run (capture #[]) 31
    (fixture (keys.pop.push badKey) (aggregateOf keys))) = true := by native_decide

-- 31 bits set and the identity as the non-participant key: `AggregatePKs` raises `ValueError`.
example : isArith (run (capture #[]) 31
    (fixture (keys.pop.push identityKey) (aggregateOf keys))) = true := by native_decide

-- At slot 0, `get_block_root_at_slot` fails its assertion `slot < state.slot`. With 31 bits
-- set and a stored aggregate that does not decode, the key fault raises first. With one bit
-- set the body has no key fault, and the assertion raises.
example : isArith (run (capture #[]) 31 (fixture keys badKey (slot := 0))) = true := by
  native_decide
example : isAssert (run (capture #[keys[0]!]) 1 (fixture keys badKey (slot := 0))) = true := by
  native_decide

/-! ## Q13: a committee key the registry does not hold -/

-- The registry lacks the first committee key: `all_pubkeys.index` raises `ValueError`.
example : isArith (run (capture #[keys[0]!]) 1
    (fixture keys badKey (registry := keys.extract 1 32))) = true := by native_decide

-- The same state, with a verify that rejects: the signature assertion raises before the
-- registry search.
example : isAssert (run rejectAll 1 (fixture keys badKey (registry := keys.extract 1 32))) = true := by
  native_decide

end

/-! ## Item 5, site g: the reward products under patched constants

The two site g rows of `specs/2026-10-24-batchfaith-probes.md` (local, not committed). The probe
sets `EFFECTIVE_BALANCE_INCREMENT = 1` and a large `BASE_REWARD_FACTOR`, turns BLS off, and runs
an empty aggregate on one validator of `2 ^ 50` at slot 1. The pin sets the same `Preset` fields
(both increment fields) and uses `CryptoBackend.verifyOff`. The aggregate is empty, so neither
side runs a key operation. The reward products raise before `all_pubkeys.index`. -/

section
local instance : Config := minimalConfig
local instance : HasherTag := fastHasherTag
local instance : CryptoBackend := CryptoBackend.verifyOff

/-- The preset of the site g rows: `EFFECTIVE_BALANCE_INCREMENT = 1` and the given
`BASE_REWARD_FACTOR`. -/
@[reducible] private def ebi1Brf (brf : Nat) : Preset :=
  { minimal with
    effectiveBalanceIncrement := 1, effectiveBalanceIncrementG := 1, baseRewardFactor := brf }

/-- `process_sync_aggregate` with an empty aggregate on one validator of `2 ^ 50` at slot 1,
under the preset `P` and the backend `cb`. -/
private def runEmpty (P : Preset) (cb : CryptoBackend := CryptoBackend.verifyOff) :
    Except StateTransitionError (Unit × @BeaconState P) :=
  letI : Preset := P
  letI : CryptoBackend := cb
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 1125899906842624
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  runPure (processSyncAggregate (StateTransition := FuluRun) default)
    { (default : BeaconState) with
      slot := 1
      validators := listOf #[v]
      balances := listOf #[32000000000] }

-- `BASE_REWARD_FACTOR = 2 ^ 40`: `2 ^ 15 * 2 ^ 50` raises at the first product.
example : (match runEmpty (ebi1Brf (2 ^ 40)) with
    | .error (.arithmetic d) =>
      d == "process_sync_aggregate: get_base_reward_per_increment(state) * total_active_increments"
    | _ => false) = true := by native_decide

-- Order: the same state under the real backend. The zero signature over the empty aggregate
-- fails the signature assert, which pyspec checks before the reward products.
example : (match runEmpty (ebi1Brf (2 ^ 40)) CryptoBackend.realBackend with
    | .error (.assert _) => true
    | _ => false) = true := by native_decide

-- `BASE_REWARD_FACTOR = 2 ^ 38`: the first product is `2 ^ 63`, and `* SYNC_REWARD_WEIGHT`
-- raises.
example : (match runEmpty (ebi1Brf (2 ^ 38)) with
    | .error (.arithmetic d) => d == "process_sync_aggregate: total_base_rewards * SYNC_REWARD_WEIGHT"
    | _ => false) = true := by native_decide

end

end EthCLSpecs.Tests.FuluSyncAggregatePins
