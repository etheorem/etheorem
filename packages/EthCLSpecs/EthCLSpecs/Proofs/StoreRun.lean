import EthCLLib.Spec

/-!
# `EthCLSpecs.Proofs.StoreRun`: the fork-choice store runner these proofs run against

A theorem about a fork-choice `forkdef`'s effect has to pin down the monad the spec
body is elaborated into, since `StoreTransition` is a parameter of the fork body
rather than a fixed type. Every fork-choice proof pins the runner named here, at its
own fork's `Store`, through `(StoreTransition := ForkChoiceStoreRun (Store map))`.

The module sits beside the per-fork directories rather than inside one. The runner
is a monad over an arbitrary store type, so it belongs to no fork, and the theorems
that pin it live in `Proofs/Gloas/` and `Proofs/Heze/` alike.

`SPEC_AUTHORING_MODEL.md` sets out a fast/pure duality across four axes, and
`SPECS_ARCHITECTURE.md` §11.1 states that the fast configuration (`FastBox`,
`EStateM`, `hashMap`) is never a proof target. This is the pure column's store
monad, the store-side counterpart of `Proofs/Gloas/Run.lean`'s `GloasRun`.

The `.run` / `Except.bind` lemmas below are independent of any fork's `State`.
The GloasRun lemmas delegate to these shared lemmas.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (StoreTransitionError)

/-- Pure runner for fork-choice store proofs: `StateT` over `Except`, threading an
arbitrary store state `σ` and rejecting with `StoreTransitionError`.

Parameterized by the store type rather than by a fork-specific `Store`, so Gloas and
Heze, and any later fork, pin `(StoreTransition := ForkChoiceStoreRun (Store map))` at
the same shared name. `abbrev` (reducible) so a goal mentioning it unifies with the
spelled-out `StateT σ (Except StoreTransitionError)`. -/
abbrev ForkChoiceStoreRun (σ : Type) : Type → Type :=
  StateT σ (Except StoreTransitionError)

/-! ## Running a bind

`EStateM` ships `run_bind` / `run_pure` as `simp` lemmas; the `StateT`-over-`Except`
stack does not, because both steps are definitional there (`StateT.run x s` is `x s`,
and `StateT.bind` threads the pair through `Except`'s own bind). Proofs that pin
`ForkChoiceStoreRun` or `GloasRun` need the same rewrites, so they are stated once
here. Both close by `rfl`.

Stated at any `σ` / `ε` rather than at a fork's `Store` / `StoreTransitionError`:
nothing in either proof is specific to one fork, and the general form applies to
`PUnit`-valued loop bodies without an instantiation dance. -/

/-- `.run` of a bind: run the first action, and on success run the continuation from the
value and state it produced. The `Except` bind on the right short-circuits a reject. -/
theorem ForkChoiceStoreRun.run_bind {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s : σ) :
    (x >>= f).run s = (x.run s) >>= fun p => (f p.1).run p.2 :=
  rfl

/-- `.run` of a `pure`: the value paired with the state, unchanged. -/
theorem ForkChoiceStoreRun.run_pure {σ ε α : Type} (a : α) (s : σ) :
    (pure a : StateT σ (Except ε) α).run s = .ok (a, s) :=
  rfl

/-- `.run` of a `throw`: the error alone. `EStateM`'s throw carries the state it had
reached; here a reject is just the error, so a theorem about one has no post-state
to characterize. -/
theorem ForkChoiceStoreRun.run_throw {σ ε α : Type} (e : ε) (s : σ) :
    (throw e : StateT σ (Except ε) α).run s = .error e :=
  rfl

/-- `Except`'s bind on the success branch, the step that fires after
`ForkChoiceStoreRun.run_bind` on a run known to have succeeded. -/
theorem ForkChoiceStoreRun.except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a :=
  rfl

/-- `Except`'s bind on the error branch: the continuation is skipped. -/
theorem ForkChoiceStoreRun.except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α) >>= f = .error e :=
  rfl

end EthCLSpecs.Proofs
