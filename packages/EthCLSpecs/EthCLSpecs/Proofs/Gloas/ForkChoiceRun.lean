import EthCLSpecs.Gloas.ForkChoice
import EthCLSpecs.Proofs.Gloas.InitiateBuilderExit
import EthCLSpecs.Proofs.Gloas.BuilderPendingPayments

/-!
# `EthCLSpecs.Proofs.Gloas.ForkChoiceRun`: the fork-choice store monad these proofs would run at

`Proofs/Gloas/Run.lean` names the monad for the *state* machine. This names the one for the
*store* machine, and proves a fork-choice `forkdef` at it.

Nothing here is a fork-choice proof yet; `PROOF_LEDGER.md` queues five under Gloas
"Fork-choice correctness".
This file establishes the two things such a proof needs.

**A store monad with no `EStateM` in it.** `getSlotsSinceGenesis_run_of_time_eq_genesis`
is a real fork-choice `forkdef` proved at `GloasStoreRun`, the pure column's store monad.
`getSlotsSinceGenesis` is the subject because it is small and it throws. Its two checked
`uint64` ops are the reason the fork-choice read layer is monadic at all, so proving its
equation at the pure monad exercises the part that makes the monad matter, without
dragging in a walk or a nested transition.

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
open EthCLSpecs.Gloas (Preset Config BuilderIndex)
open EthCLSpecs.Gloas (Store getSlotsSinceGenesis getCurrentSlot State currentEpochOf
  initiateBuilderExit processBuilderPendingPayments)
open SizzLean.Repr
open SizzLean.Cache

/-- The store machine's pure monad: `StateT` over `Except`, threading the fork-choice
`Store` and rejecting with `StoreTransitionError`. The store-side counterpart of
`GloasRun`, and the store-side reading of `SPECS_ARCHITECTURE.md` §11.1.

Parameterized by the map backing rather than fixed to `treeMap`: the backing is a
separate axis of the fast/pure duality from the monad, and a theorem that does not
read a map should not pin one. -/
abbrev GloasStoreRun [Preset] [HasherTag] (map : MapKind) : Type → Type :=
  StateT (Store map) (Except StoreTransitionError)

/-- **A fork-choice `forkdef`, at the pure store monad.** `get_slots_since_genesis` on a
store whose clock has not advanced past genesis returns `0`, leaving the store alone.

The two `uint64` ops both stay in range for the trivial reason: `time - genesis_time` is
`0` when they are equal, so the checked subtraction cannot underflow and the checked
multiply has nothing to overflow. `simp` discharges those two guards; the `rfl` after it
is the whole `do` block reducing at this monad, binds included. -/
theorem getSlotsSinceGenesis_run_of_time_eq_genesis
    [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.time = store.genesisTime →
      (getSlotsSinceGenesis (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime
  -- `checkedSub g g` takes its `else` branch (`g > g` is false) and yields `g - g = 0`;
  -- `checkedMul 0 1000` takes its `else` branch (the `a != 0` guard) and yields `0`;
  -- `0 / SLOT_DURATION_MS` is `0` for the opaque `[Config]` divisor.
  simp [getSlotsSinceGenesis, htime, EthCLLib.Spec.checkedSub, EthCLLib.Spec.checkedMul]
  rfl

/-- The same fact one layer up, through `get_current_slot`'s `GENESIS_SLOT + _`. Two
`forkdef`s composed, so the bind between them is at this monad too, not just the leaf. -/
theorem getCurrentSlot_run_of_time_eq_genesis
    [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.time = store.genesisTime →
      (getCurrentSlot (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime
  simp [getCurrentSlot, getSlotsSinceGenesis, htime, EthCLLib.Spec.checkedSub,
    EthCLLib.Spec.checkedMul, EthCLSpecs.Gloas.Const.genesisSlot]
  rfl

/-! ## The bridge carries a step's own theorem, unchanged

`EthCLLib/Spec/NestedMachine.lean` proves once, for every action, that the bridge hands a
successful run's post-state back with `pure`. So carrying a state-machine fact into the
store machine is function application, and there is nothing left here to state as a
theorem of the Gloas spec.

These are `example`s rather than named theorems for that reason: they claim nothing about
Gloas that `Proofs/Gloas/InitiateBuilderExit.lean` and `Proofs/Gloas/BuilderPendingPayments.lean` do
not already claim. They are here so the build keeps the composition honest, and so a
reader looking for "how do I use a step's theorem inside a fork-choice proof" finds the
two lines that answer it.

`[NestedStateMachine m State GloasRun]` says only "a store machine whose nested column is
the pure one", which `instNestedPure` supplies for `GloasStoreRun map` and for every other
store monad in that column. No store value appears; a state transition's effect does not
depend on one. -/

/-- `initiateBuilderExit_run_eq` crossing the bridge, by application. -/
example [Preset] [HasherTag] [Config] {m : Type → Type} [Monad m]
    [MonadExceptOf StoreTransitionError m] [NestedStateMachine m State GloasRun] :
    ∀ (pre : State) (builderIndex : BuilderIndex),
      runNestedStateTransition pre
          (initiateBuilderExit (StateTransition := GloasRun) builderIndex)
        = (pure (sszModify pre builders[builderIndex.toNat]! as b =>
            { b with withdrawableEpoch :=
                currentEpochOf pre + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay })
          : m State) :=
  fun pre builderIndex =>
    runNestedStateTransition_of_ok (initiateBuilderExit_run_eq pre builderIndex)

/-- `processBuilderPendingPayments_run` likewise, and this is the one that shows the point:
its proof rests on a `List.forIn` induction over the withdrawals loop, and that induction is
not re-entered here. -/
example [Preset] [HasherTag] {m : Type → Type} [Monad m]
    [MonadExceptOf StoreTransitionError m] [NestedStateMachine m State GloasRun] :
    ∀ pre : State,
      ∃ post : State,
        runNestedStateTransition pre
            (processBuilderPendingPayments (StateTransition := GloasRun))
          = (pure post : m State) ∧
        ProcessBuilderPendingPaymentsPost pre post :=
  fun pre =>
    let ⟨post, hrun, hpost⟩ := processBuilderPendingPayments_run pre
    ⟨post, runNestedStateTransition_of_ok hrun, hpost⟩

end EthCLSpecs.Proofs.Gloas
