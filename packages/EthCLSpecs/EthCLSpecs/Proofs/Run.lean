import EthCLSpecs.Gloas.State

/-!
# `EthCLSpecs.Proofs.Run`: the Gloas state-transition runner these proofs run against

A theorem about a `forkdef`'s effect has to pin down the monad the spec body is
elaborated into, since `StateTransition` is a parameter of the fork body rather than a
fixed type. Every Gloas proof in this directory pins the same one, so it is named once
here and instantiated at each theorem through `(StateTransition := GloasRun)`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLSpecs.Fulu (Preset)
open EthCLSpecs.Gloas (State)

/-- The concrete monad the Gloas spec bodies run in: `EStateM` over the boxed Gloas
`BeaconState`, rejecting with `StateTransitionError`. `abbrev` (reducible) so a goal
mentioning it unifies with the spelled-out `EStateM StateTransitionError State`. -/
abbrev GloasRun [Preset] [HasherTag] : Type → Type :=
  EStateM StateTransitionError State

end EthCLSpecs.Proofs
