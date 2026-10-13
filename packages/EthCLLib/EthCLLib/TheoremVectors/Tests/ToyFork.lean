import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.PySpecTests.Interface
import EthCLLib.Spec.State
import SizzLean
import EthCLLib.Spec.Hasher
import EthCLLib.Proofs.Run
import EthCLLib.TheoremVectors.Tests.ToyRun

/-!
# `EthCLLib.TheoremVectors.Tests.ToyFork`: the command tests' toy binding

The `ForkBinding` the command tests run over, in its own module: the test
module imports `EthCLLib.TheoremVectors.Command`, and Lean reserves the
command syntax's atoms at import time, so a module below the import cannot
spell the binding's `presets` field. Declaring the binding here, where the
command module is not imported, keeps the field speakable.

The file also carries the toy run facts the pyspec format's tests drive
(`THEOREM_VECTORS_ARCHITECTURE.md` §13.4, §13.5): the toy `ForkInterface`
value and the second `ForkBinding` over the toy state, `toyRunBinding`.
The two bindings share the file, so a reader sees both in one place and
neither disturbs the other.
-/

set_option autoImplicit false

open EthCLLib.Spec (HasherTag fastHasherTag RunError StateTransitionError
  ErrorConv)
open EthCLLib.PySpecTests
open EthCLLib.Proofs (pureState)

namespace EthCLLib.TheoremVectors.Tests.ToyFork

/-- A toy binding over the registered toy fork
`EthCLLib.Tests.InheritanceReplay.Base` (`EthCLLib.Tests.InheritanceReplay`). -/
def toyBinding : EthCLLib.TheoremVectors.ForkBinding where
  fork := `EthCLLib.Tests.InheritanceReplay.Base
  tag := "toybase"
  presets := #[]
  hasherTag := `EthCLLib.Spec.fastHasherTag
  crypto := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType := `Nat
  blockTypes := #[]
  opens := #[]
  builders := #[]
  handlerOf := fun _ => none
  interface := fun _ => none

/-- The scratch output root the test drives share, under this package's
gitignored build tree. -/
def scratchOutDir : System.FilePath := ".lake/build/test-theorem-vectors"

/-- Decode a toy state, or the runner's `decode` error. -/
private def decodeToy (bytes : ByteArray) :
    Except (RunError StateTransitionError) ToyRun.ToyState :=
  match SizzLean.SSZ.deserialize (T := ToyRun.ToyState) bytes with
  | .ok v    => .ok v
  | .error _ => .error (.decode "ToyState")

/-- The toy `ForkInterface` at minimal (`THEOREM_VECTORS_ARCHITECTURE.md`
§13.5). Three steps are wired, and the rest answer an explicit `todo`:
`.effectiveBalanceUpdates` runs the `.runOk` theorem's action, and
`.slashings` is the toy's rejection. The reject runs `toyFail`, whose
`throw "boom"` the interface reports as the spec assert `toy: boom`, the
expected reject an invalid vector carries under the driver's caught set.
`.inactivityUpdates` is the toy's index miss: the step runs `toyIndexMiss`,
whose read rejects with the SSZ `IndexError`, lifted to the state machine's
`outOfBounds` the way the fork bodies lift it. The driver scores that
reject as a pass with the bug-smell flag, the divergence `pyspecCheck`
fails on. -/
@[reducible] def toyRunInterface : ForkInterface where
  stateRoot := fun bytes =>
    letI : HasherTag := fastHasherTag
    match decodeToy bytes with
    | .ok v    => .ok (SizzLean.SSZ.hashTreeRoot HasherTag.H v)
    | .error e => .error e
  sszStatic     := fun _ _     => .error (.spec (.todo "toyrun ssz_static: not modeled"))
  runBlocks     := fun _ _ _   => .error (.spec (.todo "toyrun blocks: not modeled"))
  runSlots      := fun _ _     => .error (.spec (.todo "toyrun slots: not modeled"))
  runEpochSubstep := fun step bytes =>
    letI : HasherTag := fastHasherTag
    match decodeToy bytes with
    | .error e => .error e
    | .ok pre =>
      match step with
      | .effectiveBalanceUpdates =>
        match (ToyRun.toySetBal 42).run (pureState pre) with
        | .ok (_, post) => .ok (SizzLean.SSZ.hashTreeRoot HasherTag.H post.view)
        | .error e => .error (.spec (.assert s!"toy: {e}"))
      | .slashings =>
        match ToyRun.toyFail.run (pureState pre) with
        | .error e => .error (.spec (.assert s!"toy: {e}"))
        | .ok (_, post) => .ok (SizzLean.SSZ.hashTreeRoot HasherTag.H post.view)
      | .inactivityUpdates =>
        match (ToyRun.toyIndexMiss 5).run (pureState pre) with
        | .error e => .error (.spec (ErrorConv.conv e))
        | .ok (_, post) => .ok (SizzLean.SSZ.hashTreeRoot HasherTag.H post.view)
      | _ => .error (.spec (.todo "toyrun epoch substep: not modeled"))
  runOperation  := fun _ _ _ _ => .error (.spec (.todo "toyrun operations: not modeled"))
  runRewards    := fun _       => .error (.spec (.todo "toyrun rewards: not modeled"))
  runForkChoice := fun _ _ _   => .error (.spec (.todo "toyrun fork_choice: not modeled"))
  runGenesis    := fun _ _     => .error (.spec (.todo "toyrun genesis: not modeled"))
  runUpgrade    := fun _       => .error (.spec (.todo "toyrun fork upgrade: not modeled"))
  runTransition := fun _ _ _   => .error (.spec (.todo "toyrun transition: not modeled"))

/-- The toy run binding for the pyspec format's tests (§13.4, §13.5): the
same fork facts as `toyBinding`, with the toy state type, the `handlerOf`
map over the three toy actions, and the toy interface at minimal. The map
arms name real `epoch_processing` directories, because the driver parses
the handler string through `EpochStep.ofString?` before it reaches the
interface: the `.runOk` action runs under the real `effective_balance_updates`
directory, `toyFail`'s rejection under `slashings`, and the index miss
under `inactivity_updates`. The `presets` field stays empty; the pyspec
path reads only `handlerOf` and `interface`. -/
def toyRunBinding : EthCLLib.TheoremVectors.ForkBinding where
  fork := `EthCLLib.Tests.InheritanceReplay.Base
  tag := "toyrun"
  presets := #[]
  hasherTag := `EthCLLib.Spec.fastHasherTag
  crypto := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType := `EthCLLib.TheoremVectors.Tests.ToyRun.ToyState
  blockTypes := #[]
  opens := #[]
  builders := #[]
  handlerOf := fun
    | `EthCLLib.TheoremVectors.Tests.ToyRun.toySetBal =>
        some ("epoch_processing", "effective_balance_updates")
    | `EthCLLib.TheoremVectors.Tests.ToyRun.toyFail =>
        some ("epoch_processing", "slashings")
    | `EthCLLib.TheoremVectors.Tests.ToyRun.toyIndexMiss =>
        some ("epoch_processing", "inactivity_updates")
    | _ => none
  interface := fun
    | .minimal => some toyRunInterface
    | .mainnet => none

end EthCLLib.TheoremVectors.Tests.ToyFork
