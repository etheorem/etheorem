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

`SPEC_AUTHORING_MODEL.md` sets out a fast/pure duality across four axes, and
`SPECS_ARCHITECTURE.md` §11.1 states that the fast configuration (`FastBox`,
`EStateM`, `hashMap`) is never a proof target. This is the pure column's store
monad, the store-side counterpart of `EthCLSpecs/Proofs/Gloas/Run.lean`'s `GloasRun`.

The generic `StateT`-over-`Except` bind, pure, throw, and `Except.bind` equations
live in `EthCLLib/Proofs/Run.lean`. The same module pins the box on the state side: a
state-transition theorem states its run on `pureState v`, the uncached box, and that
`.run` fact is what the nested-machine bridge consumes unchanged. This file keeps the
`ForkChoiceStoreRun` abbreviation
and the store-specific `throwArithmetic_run` equation: `throwArithmetic` lifts a
`StateTransitionError` that the store machine wraps as `.transition`, so the
generic `run_throw` does not apply.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (StoreTransitionError throwArithmetic)

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

end EthCLLib.Proofs
