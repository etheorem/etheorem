import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.PySpecTests.Interface

/-!
# `EthCLLib.TheoremVectors.ForkBinding`: the fork binding seam

`ForkBinding` is the one type through which the framework half sees a fork
(`THEOREM_VECTORS_ARCHITECTURE.md` §6). It plays the role `ForkInterface` plays for the
pyspec runner: a fork supplies one value, and the generator consumes it. A
new fork needs one binding and one generator file, with no edit in the
framework half.

The binding holds names, and term construction (§10) turns each into an
`Expr.const` when the command fixes the instance binders. The
framework half's tests can run against a binding over a toy fork, the same
way `EthCLLib.Tests` tests the DSL over toy forks.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The instance constants one preset fixes (`THEOREM_VECTORS_ARCHITECTURE.md` §6). -/
structure PresetInstances where
  /-- The fork's `Preset` value for the entry, `EthCLSpecs.Gloas.minimal`. -/
  preset : Name
  /-- The matching `Config` value, `EthCLSpecs.Gloas.minimalConfig`. -/
  config : Name
  deriving Inhabited, Repr

/-- The fork facts the generator runs on (`THEOREM_VECTORS_ARCHITECTURE.md` §6). One value
per fork, written in the spec half and read with `evalConst`. -/
structure ForkBinding where
  /-- The fork namespace, `EthCLSpecs.Gloas`. The reader checks a theorem's
  target against the fork's captured spec functions through this name. -/
  fork        : Name
  /-- The path segment and the pyspec fork name, `"gloas"`. -/
  tag         : String
  /-- One entry per preset the fork supports. -/
  presets     : Array (PresetId × PresetInstances)
  /-- The hasher the probe binds, `EthCLLib.Spec.fastHasherTag`. -/
  hasherTag   : Name
  /-- The crypto backend the probe binds, `EthCLLib.Spec.CryptoBackend.verifyOff`. -/
  crypto      : Name
  /-- The state container, so the pyspec format can tell a state input
  apart. -/
  stateType   : Name
  /-- The types that put a theorem out of scope (§1.2). -/
  blockTypes  : Array Name
  /-- The namespaces the probe opens to elaborate its term. -/
  opens       : Array Name
  /-- The state-builder catalog (§9.9): a display name and a constant of
  type `[Preset] → [Config] → Knobs → BeaconState`, cheapest first. -/
  builders    : Array (String × Name)
  /-- Which `(runner, handler)` pair a spec function answers to in the
  pyspec layout; `none` for a function no vector format drives. -/
  handlerOf   : Name → Option (String × String)
  /-- The fork's `ForkInterface` at a preset, for the pyspec format's
  check (§13.5). -/
  interface   : PresetId → Option EthCLLib.PySpecTests.ForkInterface
  deriving Inhabited

/-- Is the input type the binding's state container? §9.4's rule: no source
proposes `default` for it, so a source that would fill the input from the
serialized defaults answers `nothing`. §7.3 reads the same predicate over
the theorem's value binders: the run's state is one of the state-typed
binders, and the type identifies the store whatever the binder's
position. -/
def isStateType (binding : ForkBinding) (t : Expr) : Bool :=
  match t.getAppFn with
  | .const c _ => c == binding.stateType
  | _ => false

end EthCLLib.TheoremVectors
