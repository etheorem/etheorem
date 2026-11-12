import EthCLSpecs.Heze.State
import EthCLLib.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Heze.Run`: the Heze state-transition runner these proofs run against

`StateTransition` is a parameter of the fork body, so a theorem about a `forkdef`'s effect has
to pin the monad the body elaborates into. Every Heze proof about the beacon-state machine pins
the runner named here, through `(StateTransition := HezeRun)`. It is the Heze copy of
`GloasRun` (`Proofs/Gloas/Run.lean`), whose docstring gives the reasons for `StateT` over
`Except`. The store machine's counterpart is `ForkChoiceStoreRun`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLSpecs.Heze (Preset State)

/-- The monad the Heze spec bodies are proved at: `StateT` over `Except`, threading the boxed
Heze `BeaconState` and rejecting with `StateTransitionError`. `abbrev` (reducible), so a goal
that mentions it unifies with the spelled-out type. -/
abbrev HezeRun [Preset] [HasherTag] : Type → Type :=
  StateT State (Except StateTransitionError)

end EthCLSpecs.Proofs.Heze
