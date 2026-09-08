import EthCLSpecs.Fulu.State

/-!
# `EthCLSpecs.Proofs.Fulu.Run`: the Fulu state-transition runner these proofs run against

`StateTransition` is a parameter of the fork body, so a theorem about a `forkdef`'s effect has
to pin the monad the body elaborates into. Every Fulu proof in this directory pins the runner
named here, through `(StateTransition := FuluRun)`. `SPECS_ARCHITECTURE.md` §11.1 names the
pure configuration this runner belongs to.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLSpecs.Fulu (Preset State)

/-- The monad the Fulu spec bodies are proved at: `StateT` over `Except`, threading the boxed
Fulu `BeaconState` and rejecting with `StateTransitionError`. `abbrev` (reducible), so a goal
that mentions it unifies with the spelled-out type. -/
abbrev FuluRun [Preset] [HasherTag] : Type → Type :=
  StateT State (Except StateTransitionError)

end EthCLSpecs.Proofs.Fulu
