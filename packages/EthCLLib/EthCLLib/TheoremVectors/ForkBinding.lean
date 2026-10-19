import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.PySpecTests.Interface
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.TheoremVectors.ForkBinding`: the fork binding seam

`ForkBinding` is the one type through which the framework half sees a fork
(`THEOREM_VECTORS_ARCHITECTURE.md` §6). It plays the role `ForkInterface` plays for the
pyspec runner: a fork supplies one value, and the generator consumes it. A
new fork needs one binding and one generator file, with no edit in the
framework half.

The pyspec spelling of a function is data the binding carries: the
`pyspecNames` table sits beside `handlerOf` and `builders`, one row per
function the fork owns. The statement reader looks a discovered target up
in the table, a target with no row answers `none`, and the function format
falls back to the Lean target name.

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
  /-- The pyspec spelling of the fork's spec functions (`THEOREM_VECTORS_ARCHITECTURE.md`
  §6): the full Lean name of a function the fork owns, to the snake-case
  name clients consume. The statement reader looks a discovered target up
  here; a target with no row answers `none`, and the function format then
  falls back to the Lean target name. -/
  pyspecNames : Array (Name × String)
  /-- The fork's `ForkInterface` at a preset, for the pyspec format's
  check (§13.5). -/
  interface   : PresetId → Option EthCLLib.PySpecTests.ForkInterface
  deriving Inhabited

/-- Is the input type the binding's state container? §9.4's rule: no
searcher proposes `default` for it, so a searcher that would fill the
input from the serialized defaults answers `nothing`. §7.3 reads the same predicate over
the theorem's value binders: the run's state is one of the state-typed
binders, and the type identifies the store whatever the binder's
position. -/
def isStateType (binding : ForkBinding) (t : Expr) : Bool :=
  match t.getAppFn with
  | .const c _ => c == binding.stateType
  | _ => false

/-- Does the string match `[a-z][a-z0-9_]*`, the pyspec identifier's shape?
The same shape the deleted docstring parse demanded of the opening span,
now a property of the table's values. -/
private def isPyspecName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    'a' ≤ c && c ≤ 'z' &&
      cs.all fun d => d == '_' || d.isDigit || ('a' ≤ d && d ≤ 'z')

/-- Does the binding's fork own `c` as a target the reader can pick: the
fork owns the name, `c` is no structure accessor, and it is a `def` or an
`opaque`? This is `THEOREM_VECTORS_ARCHITECTURE.md` §7.2's target test,
and the binding's `pyspecNames` validation reads through it, so the table
can hold exactly the rows a target can use. -/
def ownedSpecFunction? (env : Environment) (binding : ForkBinding)
    (c : Name) : Bool :=
  if (EthCLLib.Internal.specFunctionOwner? env c).map (·.1) != some binding.fork then
    false
  else if env.isProjectionFn c then
    -- a structure accessor names a field, not a function under test:
    -- `store.justifiedCheckpoint.epoch`'s `Checkpoint.epoch` must not
    -- become the target of the monotonicity bound over it
    false
  else
    match env.find? c with
    | some (.defnInfo _) | some (.opaqueInfo _) => true
    | _ => false

open Lean.Elab in
/-- The `pyspecNames` table's checks (`THEOREM_VECTORS_ARCHITECTURE.md` §6):
one row per function, each value in the pyspec identifier's shape, and
each key a function the binding's fork owns as a target. The header's
elaborator runs this once, so a stale row fails the build the way a stale
`skip` line does. The key test is `ownedSpecFunction?`, the reader's own
target rule: the owner query alone matches only the namespace prefix, so
it would accept a misspelled name, and the capture-based spec-function
test would reject the plain `def`s a target can name. -/
def validatePyspecNames (binding : ForkBinding) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  for i in [0:binding.pyspecNames.size] do
    let (name, pyspec) := binding.pyspecNames[i]!
    if (binding.pyspecNames.take i).any fun (n, _) => n == name then
      throwError "theorem_vectors: the binding of fork `{binding.fork}` \
        lists `{name}` twice in `pyspecNames`; one row per function (§6)"
    unless isPyspecName pyspec do
      throwError "theorem_vectors: the binding of fork `{binding.fork}` \
        maps `{name}` to `{pyspec}`, which is no pyspec identifier \
        (`[a-z][a-z0-9_]*`) (§6)"
    unless ownedSpecFunction? env binding name do
      throwError "theorem_vectors: the binding of fork `{binding.fork}` \
        lists `{name}` in `pyspecNames`, and `{name}` names no function \
        the fork owns as a target (§7.2)"

end EthCLLib.TheoremVectors
