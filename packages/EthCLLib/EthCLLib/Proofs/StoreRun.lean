import EthCLLib.Spec
import EthCLLib.Proofs.Run

/-!
# `EthCLLib.Proofs.StoreRun`: the fork-choice store runner these proofs run against

A theorem about a fork-choice `forkdef`'s effect has to pin down the monad the spec
body is elaborated into, since `StoreTransition` is a parameter of the fork body
rather than a fixed type. Every fork-choice proof pins the runner named here, at its
own fork's `Store`, through `(StoreTransition := ForkChoiceStoreRun (Store map))`.

The module lives in the framework, beside the other generic proof modules, rather
than in one fork's directory. The runner
is a monad over an arbitrary store type, so it belongs to no fork, and the theorems
that pin it live in `EthCLSpecs/Proofs/Gloas/` and `EthCLSpecs/Proofs/Heze/` alike.

`SPEC_AUTHORING_MODEL.md` sets out a fast/pure duality across three axes, and
`SPECS_ARCHITECTURE.md` §11.1 states that the fast configuration (`fastHasherTag`,
`EStateM`, `hashMap`) is never a proof target. This is the pure column's store
monad, the store-side counterpart of `EthCLSpecs/Proofs/Gloas/Run.lean`'s `GloasRun`.

The generic `StateT`-over-`Except` bind, pure, throw, and `Except.bind` equations
live in `EthCLLib/Proofs/Run.lean`. This file keeps the `ForkChoiceStoreRun`
abbreviation and the store-specific `throwArithmetic_run` / `throwZeroDivision_run` equations:
`throwArithmetic` and `throwZeroDivision` lift a `StateTransitionError` that the store
machine wraps as `.transition`, so the generic `run_throw` does not apply. The two
`liftChecked` equations give the `.run` of a lifted checked expression on the same
grounds: a fault reaches the store machine wrapped as `.transition`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (StoreTransitionError StateTransitionError throwArithmetic
  throwZeroDivision Checked ArithFault)

/-- Pure runner for fork-choice store proofs: `StateT` over `Except`, threading an
arbitrary store state `σ` and rejecting with `StoreTransitionError`.

Parameterized by the store type rather than by a fork-specific `Store`, so Gloas and
Heze, and any later fork, pin `(StoreTransition := ForkChoiceStoreRun (Store map))` at
the same shared name. `abbrev` (reducible) so a goal mentioning it unifies with the
spelled-out `StateT σ (Except StoreTransitionError)`. -/
abbrev ForkChoiceStoreRun (σ : Type) : Type → Type :=
  StateT σ (Except StoreTransitionError)

/-- `.run` of `throwArithmetic` at `ForkChoiceStoreRun`. Closes by `rfl`
without unfolding `liftErr`. -/
theorem ForkChoiceStoreRun.throwArithmetic_run {σ α : Type}
    (descr : String) (s : σ) :
    (throwArithmetic
        (m := ForkChoiceStoreRun σ)
        (E := StoreTransitionError)
        descr : ForkChoiceStoreRun σ α).run s
      = .error (.transition (.arithmetic descr)) :=
  rfl

/-- `.run` of `throwZeroDivision` at `ForkChoiceStoreRun`, the zero-divisor class's store-side
wrap. Same shape as `throwArithmetic_run`; only the constructor differs. -/
theorem ForkChoiceStoreRun.throwZeroDivision_run {σ α : Type}
    (descr : String) (s : σ) :
    (throwZeroDivision
        (m := ForkChoiceStoreRun σ)
        (E := StoreTransitionError)
        descr : ForkChoiceStoreRun σ α).run s
      = .error (.transition (.zeroDivision descr)) :=
  rfl

/-- `.run` of a lifted checked value at `ForkChoiceStoreRun`, the success side: the value
passes with the store unchanged. A spec body's `let x ← a + b` elaborates to this lift
(`SPEC_ARITHMETIC.md` §4.4). -/
theorem ForkChoiceStoreRun.liftChecked_ok_run {σ α : Type} (a : α) (s : σ) :
    (liftM (Except.ok a : Checked α) : ForkChoiceStoreRun σ α).run s = .ok (a, s) :=
  rfl

/-- `.run` of a lifted checked value at `ForkChoiceStoreRun`, the fault side: the fault
becomes its typed machine reject, `StateTransitionError.ofArithFault`, wrapped as
`.transition`. The reject keeps the fault's cause, so a range fault stays `.arithmetic`. -/
theorem ForkChoiceStoreRun.liftChecked_error_run {σ α : Type} (e : ArithFault) (s : σ) :
    (liftM (Except.error e : Checked α) : ForkChoiceStoreRun σ α).run s
      = .error (.transition (StateTransitionError.ofArithFault e)) :=
  rfl

end EthCLLib.Proofs
