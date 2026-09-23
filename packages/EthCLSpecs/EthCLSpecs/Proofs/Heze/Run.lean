import EthCLSpecs.Heze.State
import EthCLSpecs.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Heze.Run`: the Heze state-transition runner

Heze elaborates its own constant for each state-transition `forkdef`. Inherited
declarations get their own constant too. These constants thread `Heze.State`. A
theorem about one of them pins this runner with `(StateTransition := HezeRun)`.
`HezeRun` is the Heze counterpart of `GloasRun` (`Proofs/Gloas/Run.lean`). That module
gives the reason for the choice of monad.

The `.run` rewrites `run_bind`, `run_pure`, and `except_bind_ok` live in
`Proofs/Run.lean` and apply to all state types. Heze proofs use them without change.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLSpecs.Heze (Preset State)

/-- The monad for proofs about the Heze state-transition bodies. It is `StateT` over
`Except`, and it threads the boxed Heze `BeaconState`. It is an `abbrev`, so a goal
that spells out `StateT State (Except StateTransitionError)` unifies with it. -/
abbrev HezeRun [Preset] [HasherTag] : Type → Type :=
  StateT State (Except StateTransitionError)

end EthCLSpecs.Proofs.Heze
