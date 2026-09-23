import EthCLSpecs.Heze.State

/-!
# `EthCLSpecs.Proofs.Heze.Run`: the Heze state-transition runner these proofs run against

`StateTransition` is a parameter of the fork body, so a theorem about a `forkdef`'s effect
names the monad the body elaborates into. Every Heze state-transition proof pins the runner
named here, through `(StateTransition := HezeRun)`. It is the Heze instance of the monad that
`Proofs/Gloas/Run.lean` describes: `StateT` over `Except`, the proving column of
`SPEC_AUTHORING_MODEL.md`.
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
