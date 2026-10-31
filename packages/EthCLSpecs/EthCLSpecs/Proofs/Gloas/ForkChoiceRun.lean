import EthCLSpecs.Gloas.ForkChoice
import EthCLLib.Proofs.StoreRun
import EthCLSpecs.Proofs.Gloas.InitiateBuilderExit
import EthCLSpecs.Proofs.Gloas.BuilderPendingPayments
import EthCLLib.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Gloas.ForkChoiceRun`: the fork-choice store monad these proofs would run at

`Proofs/Gloas/Run.lean` names the monad for the *state* machine (`GloasRun`), and
`EthCLLib/Proofs/StoreRun.lean` names the fork-generic one for the *store* machine
(`ForkChoiceStoreRun`). This file specializes the latter to Gloas's `Store` as
`GloasStoreRun`, and proves a fork-choice `forkdef` at it.

Nothing here is a fork-choice proof yet; `PROOF_LEDGER.md` queues five under Gloas
"Fork-choice correctness".
This file establishes the two things such a proof needs.

**A store monad with no `EStateM` in it.** `getSlotsSinceGenesis_run_of_time_eq_genesis`
is a real fork-choice `forkdef` proved at `GloasStoreRun`, the pure column's store monad.
`getSlotsSinceGenesis` is the subject because it is small and it throws. At v1.7.0-beta.4 it
is `compute_slot_at_time_ms(store.genesis_time_ms, store.time_ms)`, a state-machine clock
helper whose checked `uint64` subtraction reaches the store machine through `liftErr`. That
checked op is the reason the fork-choice read layer is monadic at all, and the lift is how
every clock read crosses into fork choice, so proving the equation at the pure monad exercises
both without dragging in a walk or a nested transition.

**A route for the state-machine theorems.** `NestedStateMachine`
(`EthCLLib/Spec/NestedMachine.lean`) resolves the nested monad from the store's, and for
the pure column that is `GloasRun`, the monad every theorem in `Proofs/` pins. So a fact
proved about a step standalone is a fact about that step running under fork choice. The
transport is framework-level and proved there once for every action; the two `example`s
at the end of this file are that composition, and claim nothing about Gloas on their
own.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StoreTransitionError MapKind FcMap NestedStateMachine
  runNestedStateTransition runNestedStateTransition_of_ok)
open EthCLSpecs.Gloas (Preset Config BuilderIndex BeaconState BuilderPendingWithdrawal)
open EthCLSpecs.Gloas (Store getSlotsSinceGenesis getCurrentSlot State currentEpochOf
  initiateBuilderExit processBuilderPendingPayments)
open EthCLLib.Proofs (pureState ForkChoiceStoreRun)
open SizzLean.Repr
open SizzLean.Cache

/-- Gloas specialization of `ForkChoiceStoreRun`: pure `StateT`/`Except` over
`Gloas.Store`, parameterized by the map backing rather than fixed to `treeMap`. -/
abbrev GloasStoreRun [Preset] [HasherTag] (map : MapKind) : Type → Type :=
  ForkChoiceStoreRun (Store map)

/-- **A fork-choice `forkdef`, at the pure store monad.** `get_slots_since_genesis` on a
store whose clock has not advanced past genesis returns `0`, leaving the store alone.

The checked `uint64` subtraction stays in range for the trivial reason: `time_ms -
genesis_time_ms` is `0` when they are equal, so it cannot underflow, and `0 //
SLOT_DURATION_MS` is `0` for the opaque `[Config]` divisor. `run_liftErr_of_ok` carries the
helper's `.ok` across the lift; `simp` then discharges the guard inside it. -/
theorem getSlotsSinceGenesis_run_of_time_eq_genesis
    [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.timeMs = store.genesisTimeMs →
      (getSlotsSinceGenesis (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime
  apply EthCLLib.Proofs.run_liftErr_of_ok
  -- `checkedSub g g` takes its `else` branch (`g > g` is false) and yields `g - g = 0`.
  simp [EthCLSpecs.Gloas.computeSlotAtTimeMs, htime, EthCLLib.Spec.checkedSub]
  rfl

/-- The same fact one layer up, through `get_current_slot`. At v1.7.0-beta.4 that is
`get_slots_since_genesis` itself (the `GENESIS_SLOT +` term is gone), so the fact carries
across the one `forkdef` unchanged. -/
theorem getCurrentSlot_run_of_time_eq_genesis
    [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.timeMs = store.genesisTimeMs →
      (getCurrentSlot (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime
  exact getSlotsSinceGenesis_run_of_time_eq_genesis store htime

/-! ## The bridge carries a step's own theorem, unchanged

`EthCLLib/Spec/NestedMachine.lean` proves once, for every action, that the bridge hands a
successful run's post-state back with `pure`. So carrying a state-machine fact into the
store machine is function application, and there is nothing left here to state as a
theorem of the Gloas spec. The fact must be a `.run` fact: a contract theorem states
`act.run (pureState preState) = .ok (a, pureState postState)` (`EthCLLib/Proofs/Run.lean`),
and the `runPure` value-level reading of the same contract hides the box, so it cannot feed the bridge.

These are `example`s rather than named theorems for that reason: they claim nothing about
Gloas that `Proofs/Gloas/InitiateBuilderExit.lean` and `Proofs/Gloas/BuilderPendingPayments.lean` do
not already claim. They are here so the build keeps the composition honest, and so a
reader looking for "how do I use a step's theorem inside a fork-choice proof" finds the
two lines that answer it.

`[NestedStateMachine m State GloasRun]` says only "a store machine whose nested column is
the pure one", which `instNestedPure` supplies for `GloasStoreRun map` and for every other
store monad in that column. No store value appears; a state transition's effect does not
depend on one. -/

/-- `initiateBuilderExit_run_eq` crossing the bridge, by application. The contract is a
`.run` fact on `pureState preState`, exactly the shape `runNestedStateTransition_of_ok` consumes. -/
example [Preset] [HasherTag] [Config] {m : Type → Type} [Monad m]
    [MonadExceptOf StoreTransitionError m] [NestedStateMachine m State GloasRun] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      runNestedStateTransition (pureState preState)
          (initiateBuilderExit (StateTransition := GloasRun) builderIndex)
        = (pure (pureState
          { preState with builders :=
              (preState.builders.set! builderIndex.toNat
                { preState.builders[builderIndex.toNat]! with
                  withdrawableEpoch :=
                    currentEpochOf (pureState preState)
                      + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay }) })
            : m State) :=
  fun preState builderIndex =>
    runNestedStateTransition_of_ok (initiateBuilderExit_run_eq preState builderIndex)

/-- `processBuilderPendingPayments_run` likewise, and this is the one that shows the point:
its proof rests on a `List.forIn` induction over the withdrawals loop, and that induction is
not re-entered here. `builderPendingWithdrawals` is a progressive list (since alpha.12), so the
contract is unconditional: the run always appends the qualifying withdrawals and shifts the
payment window. -/
example [Preset] [HasherTag] {m : Type → Type} [Monad m]
    [MonadExceptOf StoreTransitionError m] [NestedStateMachine m State GloasRun] :
    ∀ (preState : BeaconState),
      runNestedStateTransition (pureState preState)
          (processBuilderPendingPayments (StateTransition := GloasRun))
        = (pure (pureState { preState with
              builderPendingWithdrawals := expectedWithdrawals preState,
              builderPendingPayments := expectedPaymentWindow preState }) : m State) :=
  fun preState =>
    runNestedStateTransition_of_ok (processBuilderPendingPayments_run preState)

end EthCLSpecs.Proofs.Gloas
