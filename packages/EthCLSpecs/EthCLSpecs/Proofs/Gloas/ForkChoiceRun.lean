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
helper whose checked `uint64` subtraction and division reach the store machine through the
arithmetic lift. Those checked ops are the reason the fork-choice read layer is monadic at all,
and the lift is how every clock read crosses into fork choice, so proving the equation at the
pure monad exercises both without dragging in a walk or a nested transition.

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

open EthCLLib.Spec (StoreTransitionError MapKind FcMap NestedStateMachine
  runNestedStateTransition runNestedStateTransition_of_ok)
open EthCLSpecs.Gloas (Preset Config BuilderIndex BeaconState Builder BuilderPendingWithdrawal Gwei)
open EthCLLib.Spec (Checked CLUint64 ArithFault)
open EthCLLib.Proofs (sub_eq_ok sub_ok_iff div_eq_ok)
open EthCLSpecs.Gloas (Store getSlotsSinceGenesis getCurrentSlot State currentEpochOf
  initiateBuilderExit processBuilderPendingPayments)
open EthCLLib.Proofs (ForkChoiceStoreRun)

/-- Gloas specialization of `ForkChoiceStoreRun`: pure `StateT`/`Except` over
`Gloas.Store`, parameterized by the map backing rather than fixed to `treeMap`. -/
abbrev GloasStoreRun [Preset] (map : MapKind) : Type → Type :=
  ForkChoiceStoreRun (Store map)

/-- `compute_slot_at_time_ms(t, t)` is slot `0` when `SLOT_DURATION_MS` is positive. The
checked subtraction `t - t` cannot underflow and gives `0`, and `0 // SLOT_DURATION_MS` is `0`.
The premise names the one real obligation: the division by the configuration value raises on
a zero divisor, as the pyspec's `//` does. -/
theorem computeSlotAtTimeMs_self [Preset] [Config] (t : CLUint64)
    (hdur : EthCLSpecs.Gloas.Const.slotDurationMs.toPlainNat ≠ 0) :
    EthCLSpecs.Gloas.computeSlotAtTimeMs t t = .ok 0 := by
  have hzero : (0 : CLUint64).toPlainNat = 0 := rfl
  have hsub : CLUint64.sub t t = .ok 0 :=
    (sub_eq_ok t t 0).mpr ⟨Nat.le_refl _, by rw [hzero, Nat.sub_self]⟩
  have hdiv : CLUint64.div 0 EthCLSpecs.Gloas.Const.slotDurationMs = .ok 0 :=
    (div_eq_ok _ _ 0).mpr ⟨hdur, by rw [hzero, Nat.zero_div]⟩
  show (CLUint64.sub t t >>= fun elapsedMs =>
    CLUint64.div elapsedMs EthCLSpecs.Gloas.Const.slotDurationMs) = _
  rw [hsub]
  exact hdiv

/-- **A fork-choice `forkdef`, at the pure store monad.** `get_slots_since_genesis` on a
store whose clock has not advanced past genesis returns `0`, leaving the store alone, when
`SLOT_DURATION_MS` is positive.

`computeSlotAtTimeMs_self` gives the clock helper's `.ok 0`. The helper returns `Checked`,
and the arithmetic lift is `liftErr` of the fault conversion, so `run_liftErr_of_ok` carries
the `.ok` across the lift. `getSlotsSinceGenesis_run_of_zero_duration` states the failure the
premise excludes. -/
theorem getSlotsSinceGenesis_run_of_time_eq_genesis
    [Preset] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.timeMs = store.genesisTimeMs →
      EthCLSpecs.Gloas.Const.slotDurationMs.toPlainNat ≠ 0 →
      (getSlotsSinceGenesis (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime hdur
  apply EthCLLib.Proofs.run_liftErr_of_ok
  rw [htime, computeSlotAtTimeMs_self _ hdur]
  rfl

/-- **The failure the positive-duration premise excludes.** With `SLOT_DURATION_MS = 0` and
the store time at or after genesis, `get_slots_since_genesis` raises the zero divisor: the
checked subtraction succeeds, and the `//` by the configuration value raises Python's
`ZeroDivisionError`. The lift lands it on the store machine as a nested `.zeroDivision`, the
class no reference wrapper catches. -/
theorem getSlotsSinceGenesis_run_of_zero_duration
    [Preset] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.genesisTimeMs.toPlainNat ≤ store.timeMs.toPlainNat →
      EthCLSpecs.Gloas.Const.slotDurationMs.toPlainNat = 0 →
      (getSlotsSinceGenesis (StoreTransition := GloasStoreRun map) store).run store
        = .error (.transition (.zeroDivision "//")) := by
  intro store hle hdur
  obtain ⟨elapsedMs, hsub⟩ := (sub_ok_iff store.timeMs store.genesisTimeMs).mpr hle
  have hval : EthCLSpecs.Gloas.Const.slotDurationMs.val = 0 :=
    UInt64.toNat_inj.1 hdur
  have hdiv : CLUint64.div elapsedMs EthCLSpecs.Gloas.Const.slotDurationMs
      = .error (ArithFault.zeroDivisor "//" 64 elapsedMs.toPlainNat) := by
    simp [CLUint64.div, hval]
  apply EthCLLib.Proofs.run_liftErr_of_error
  show Except.mapError _ (Except.mapError _ (CLUint64.sub store.timeMs store.genesisTimeMs >>=
    fun elapsedMs => CLUint64.div elapsedMs EthCLSpecs.Gloas.Const.slotDurationMs)) = _
  rw [hsub]
  show Except.mapError _ (Except.mapError _ (CLUint64.div elapsedMs
    EthCLSpecs.Gloas.Const.slotDurationMs)) = _
  rw [hdiv]
  rfl

/-- The same fact one layer up, through `get_current_slot`. At v1.7.0-beta.4 that is
`get_slots_since_genesis` itself, with no `GENESIS_SLOT +` term, so the fact carries
across the one `forkdef` unchanged. -/
theorem getCurrentSlot_run_of_time_eq_genesis
    [Preset] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.timeMs = store.genesisTimeMs →
      EthCLSpecs.Gloas.Const.slotDurationMs.toPlainNat ≠ 0 →
      (getCurrentSlot (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime hdur
  exact getSlotsSinceGenesis_run_of_time_eq_genesis store htime hdur

/-! ## The bridge carries a step's own theorem, unchanged

`EthCLLib/Spec/NestedMachine.lean` proves once, for every action, that the bridge hands a
successful run's post-state back with `pure`. So carrying a state-machine fact into the
store machine is function application, and there is nothing left here to state as a
theorem of the Gloas spec. The fact must be a `.run` fact. The Gloas `State` is the plain
`BeaconState`, so a contract theorem states `act.run preState = .ok (a, postState)`, and
that one equation is the shape the bridge consumes.

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
`.run` fact on the plain `preState`, exactly the shape `runNestedStateTransition_of_ok` consumes.
The bridge is conditional on the raising `builders[builder_index]` read being in range and on
the checked withdrawability sum succeeding: past the registry's end the run raises the
`.outOfBounds` fault, past `2 ^ 64 - 1` the sum raises the `.arithmetic` fault, and in both
cases the bridge equation's `.ok` reading fails. -/
example [Preset] [Config] {m : Type → Type} [Monad m]
    [MonadExceptOf StoreTransitionError m] [NestedStateMachine m State GloasRun] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex) (we : Gloas.Epoch),
      builderIndex.toPlainNat < preState.builders.size →
      (currentEpochOf preState +
          EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Gloas.Epoch) = .ok we →
      runNestedStateTransition preState
          (initiateBuilderExit (StateTransition := GloasRun) builderIndex)
        = (pure
          { preState with builders :=
              (preState.builders.set! builderIndex.toPlainNat
                { preState.builders[builderIndex.toPlainNat]! with withdrawableEpoch := we }) }
            : m State) := by
  intro preState builderIndex we hidx hwe
  refine runNestedStateTransition_of_ok ?_
  show (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run preState = _
  have hsome : preState.builders.val[builderIndex.toPlainNat]?
      = some preState.builders[builderIndex.toPlainNat]! := by
    rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.ProgressiveList Builder) i =>
      i < xs.size) (h := hidx)]
    show preState.builders.val[builderIndex.toPlainNat]? = some _
    exact Array.getElem?_eq_getElem hidx
  rw [initiateBuilderExit_run_eq preState builderIndex, hsome, hwe]

/-- `processBuilderPendingPayments_run` likewise, and this is the one that shows the point:
its proof rests on a `List.forIn` induction over the withdrawals loop, and that induction is
not re-entered here. After `builderPaymentQuorum` succeeds, the run appends the qualifying
withdrawals and shifts the payment window. `builderPendingWithdrawals` is a progressive
list, so the append needs no capacity premise. -/
example [Preset] {m : Type → Type} [Monad m]
    [MonadExceptOf StoreTransitionError m] [NestedStateMachine m State GloasRun] :
    ∀ (preState : BeaconState) (quorum : Gwei),
      builderPaymentQuorum preState = .ok quorum →
      runNestedStateTransition preState
          (processBuilderPendingPayments (StateTransition := GloasRun))
        = (pure { preState with
              builderPendingWithdrawals := expectedWithdrawals quorum preState,
              builderPendingPayments := expectedPaymentWindow preState } : m State) :=
  fun preState quorum hq =>
    runNestedStateTransition_of_ok (processBuilderPendingPayments_run_ok preState quorum hq)

end EthCLSpecs.Proofs.Gloas
