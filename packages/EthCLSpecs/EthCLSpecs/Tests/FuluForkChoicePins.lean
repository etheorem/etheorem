import EthCLSpecs.Fulu.ForkChoice

/-!
# `EthCLSpecs.Tests.FuluForkChoicePins`: the Fulu fork-choice build-enforced pins

The vectorless pins for Fulu's fork choice: reject branches and helper values no
conformance vector reaches, locked by `#guard` / `native_decide` so a regression fails
the build rather than passing silently.

They live in `EthCLSpecsTests` rather than beside the declarations they pin. The
lakefile already declares that library for exactly this content, and a pin compiled
into `EthCLSpecs` is shipped weight: `native_decide` bakes its evaluation into the
shipped module, and a consumer importing the fork body pays for checks that only the
build gate reads. The pinned declarations are all public, so nothing is lost by the
move except adjacency.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluForkChoicePins

open EthCLSpecs.Fulu

/-! ### Build-enforced pins (vectorless): the Fulu fork-choice throws

These throw conversions' reject branches are unreachable by conformance vectors, so they
are locked here, the same pattern as the Gloas pins. `pinStore` mirrors the
`getForkchoiceStore` literal with every map empty. -/

/-- The pins' concrete fork-choice monad: the minimal preset over `treeMap` + FFI hasher. -/
private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

private def pinRoot : Root := Vector.replicate 32 9

/-- A minimal empty Fulu `Store`. -/
private def pinStore : @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { time := 0, genesisTime := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty }

/-- `getAncestor` rejects (`missingKey`) when the walk root is not in `store.blocks`,
the pinned plain-`Dict` read. Returning the root as a silent `.done` instead would hand
the caller a walk result indistinguishable from a real ancestor. `FcMap`/hash-free, so
kernel `#guard`. -/
private def pinGetAncestorThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match (getAncestor (map := treeMap) pinStore pinRoot 0 : PinM Root).run pinStore with
  | .error (.missingKey _) _ => true
  | _ => false
#guard pinGetAncestorThrows = true

/-- `getHead` rejects end-to-end when the justified-checkpoint root is unknown: the
`filter_block_tree` opening read misses. Locks the whole `getHead` monadic path.
`State`-free here (no checkpoint state read reached before the block miss), so `FcMap`
kernel `#guard`. -/
private def pinGetHeadThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let store := { pinStore with justifiedCheckpoint := { epoch := 0, root := pinRoot } }
  match (getHead (map := treeMap) store : PinM Root).run store with
  | .error (.missingKey _) _ => true
  | _ => false
#guard pinGetHeadThrows = true

/-- `storeTargetCheckpointState` propagates a `process_slots` reject. The fixture
state is `default` (zero validators, slot 0) carrying one queued `PendingConsolidation`:
advancing to epoch 1 reaches `process_pending_consolidations`, whose plain-list read
rejects (`outOfBounds`), and the unguarded pinned `process_slots` means the helper
re-throws it (`.transition`) with nothing cached. The consolidation carrier is
deliberate. A bare zero-validator advance grinds `cbwsAux`'s 10M fuel instead of
rejecting. `State` is FFI-backed, so `native_decide`. -/
private def pinTargetAdvanceRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let bs : @EthCLSpecs.Fulu.BeaconState minimal :=
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
      pendingConsolidations := sszOfArray #[{ sourceIndex := 0, targetIndex := 0 }] }
  let state : State := SSZ.FastBox bs
  let store := { pinStore with blockStates := FcMap.insert FcMap.empty pinRoot state }
  let target : Checkpoint := { epoch := 1, root := pinRoot }
  match (storeTargetCheckpointState (map := treeMap) store target : PinM (Store treeMap)).run store with
  -- Match the constructor, not the wrapper: `.transition` also spans `.arithmetic`, an uncaught
  -- fault that would fail the very step this fixture pins as an expected rejection. The pin has
  -- to break when the reject class changes, which is what Leo's note 3 asked for.
  | .error (.transition (.outOfBounds _ _)) _ => true
  | _ => false
example : pinTargetAdvanceRejects = true := by native_decide

/-- `balanceAfterWithdrawals` rejects (`outOfBounds`) on an out-of-range validator
index: the pinned bare `state.balances[vi]` list read. A `default` state has zero
validators, so index 99 misses, where the pre-conversion `def` clamped
(`balances[vi]!` defaulting, `0` on underflow). `State` is FFI-backed, so
`native_decide`. -/
private def pinBalanceAfterWithdrawalsThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := SSZ.FastBox (default : @EthCLSpecs.Fulu.BeaconState minimal)
  match (balanceAfterWithdrawals state 99 #[] : EStateM StateTransitionError State Gwei).run state with
  | .error (.outOfBounds _ _) _ => true
  | _ => false
example : pinBalanceAfterWithdrawalsThrows = true := by native_decide

/-- `balanceAfterWithdrawals` rejects (`.arithmetic`) a `uint64` underflow: a validator whose
queued withdrawals exceed its balance drives `balances[vi] - withdrawn` negative
(`capella/beacon-chain.md:378`), which pyspec raises as `ValueError`, uncaught by the reference
runner (`context.py:424-435`), so the Lean throws the uncaught `.arithmetic` reject rather than a
caught `.assert`. Fixture: balance 5 at index 0, a queued withdrawal of 10. `State` is FFI-backed,
so `native_decide`. -/
private def pinBalanceUnderflowThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let bs : @EthCLSpecs.Fulu.BeaconState minimal :=
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with balances := sszOfArray #[(5 : Gwei)] }
  let state : State := SSZ.FastBox bs
  let w : Withdrawal := { (default : Withdrawal) with validatorIndex := 0, amount := 10 }
  match (balanceAfterWithdrawals state 0 #[w] : EStateM StateTransitionError State Gwei).run state with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinBalanceUnderflowThrows = true := by native_decide

/-- `getProposerHead` rejects (`.assert`) the restored `proposer_boost_root != head_root`
guard: with the head and its parent present in `store.blocks`, the reads that precede the
assert seeded (`blockTimeliness[head]` for `is_head_late`, `unrealizedJustifications` for
head and parent for `is_ffg_competitive`), and the boost root equal to the head, the assert
is the first reject, exactly as on a well-formed store handed in by `get_head`. Vectorless
(a valid `get_proposer_head` is only reached once the boost has worn off). `native_decide`
to keep the `BeaconBlock` reduction out of the kernel. -/
private def pinProposerHeadBoostRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let headBlock : @EthCLSpecs.Fulu.BeaconBlock minimal := default
  let blocks := FcMap.insert (FcMap.insert FcMap.empty pinRoot headBlock) headBlock.parentRoot headBlock
  let timeliness := FcMap.insert FcMap.empty pinRoot true
  let uj := FcMap.insert (FcMap.insert FcMap.empty pinRoot (default : Checkpoint))
    headBlock.parentRoot (default : Checkpoint)
  let store := { pinStore with
      blocks := blocks
      blockTimeliness := timeliness
      unrealizedJustifications := uj
      proposerBoostRoot := pinRoot }
  match (getProposerHead (map := treeMap) store pinRoot 0 : PinM Root).run store with
  | .error (.assert _) _ => true
  | _ => false
example : pinProposerHeadBoostRejects = true := by native_decide

end EthCLSpecs.Tests.FuluForkChoicePins
