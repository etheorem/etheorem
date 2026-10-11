import Lean
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLSpecs.Proofs.Gloas
import EthCLSpecs.Proofs.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Gloas
import EthCLSpecs.TheoremVectors.Bindings.Fulu

/-!
# `EthCLSpecs.Tests.TheoremVectorsPins`: the statement reader's known answers

Spec-half pins for the theorem-vector generator's statement reader
(`THEOREM_VECTORS_ARCHITECTURE.md` §7; the plan's stage 1, step 9). Ten theorems with known
shapes run through `Statement.readIn` and `Scope.classify`, and each pin
checks the reader's answer: target, shape, block inputs, and the input
names in binder order.

The ten cover the pin list the plan names: one `.iffTrue`
(`canBuilderCoverBid_iff`), one `.runOk` in each of its two forms
(`processBuilderPendingPayments_run` at the box, `processBuilderPendingPayments_run_of_fits`
through `runPure`), one `.bound` with implicit value binders
(`getPtcElseOffset_lt_next_slot`), one explicit-bound `.bound`
(`getPtcElseOffset_lt_same_slot`), one with a block input
(`processOperations_eq_seq`, over `BeaconBlockBody`), one with a
function-typed input (`modBalance_pureState`, over `Gwei → Gwei`), one
whose target the walk finds under a projection
(`initializePtcWindow_lt`), one whose conclusion matches no shape
(`processOperations_run_ok_iff`, an `↔` whose left side is not `… = true`),
one with a `Store` block input (`updateCheckpoints_justifiedEpoch_le`),
and one with an unknown instance seam
(`getSlotsSinceGenesis_run_of_time_eq_genesis`, which binds `[FcMap map]`).

Each pin runs inside the reader's telescope scope
(`Statement.readIn`), because the statement cannot leave it.
-/

set_option autoImplicit false

open Lean
open Lean.Elab.Command
open EthCLLib.TheoremVectors

namespace EthCLSpecs.Tests.TheoremVectorsPins

/-- What one pin expects: the target, the shape's wire tag, the block
inputs, and the input names in binder order. -/
private structure Expect where
  target      : Option Name
  shape       : String
  blockInputs : Array String
  inputs      : Array String

/-- One pin: read the theorem, classify it, and fail with a diff when the
reader's answer misses. -/
private def pin (binding : ForkBinding) (thm : Name) (e : Expect) :
    CommandElabM Unit := do
  let got ← liftTermElabM do
    Statement.readIn binding thm fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      return (stmt.target, stmt.shape.wire,
        stmt.blockInputs.map (·.toString),
        stmt.inputs.map (·.name.toString))
  let (target, shape, blockInputs, inputs) := got
  unless target == e.target do
    throwError s!"pin {thm}: target is {repr target}, expected {repr e.target}"
  unless shape == e.shape do
    throwError s!"pin {thm}: shape is {shape}, expected {e.shape}"
  unless blockInputs == e.blockInputs do
    throwError s!"pin {thm}: blockInputs is {repr blockInputs}, \
      expected {repr e.blockInputs}"
  unless inputs == e.inputs do
    throwError s!"pin {thm}: inputs are {repr inputs}, expected {repr e.inputs}"

private unsafe def readBindingImpl {α : Type} (env : Environment)
    (constName : Name) : Except String α :=
  env.evalConst α {} constName

@[implemented_by readBindingImpl]
private opaque readBinding' {α : Type} (env : Environment)
    (constName : Name) : Except String α := .error "unreachable"

private def readBinding {α : Type} (constName : Name) : MetaM α := do
  match readBinding' (← getEnv) constName with
  | .ok a => return a
  | .error e => throwError s!"cannot read `{constName}`: {e}"


-- The reader's answers for the ten known theorems.
run_cmd do
  let gloas : ForkBinding ← liftTermElabM <|
    readBinding (`EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas)
  let fulu : ForkBinding ← liftTermElabM <|
    readBinding (`EthCLSpecs.TheoremVectors.Bindings.Fulu.fulu)
  -- `.iffTrue`, target on the left side's head
  pin gloas `EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff
    { target := some `EthCLSpecs.Gloas.canBuilderCoverBid
      shape := "iffTrue"
      blockInputs := #[]
      inputs := #["state", "builderIndex", "bidAmount"] }
  -- `.runOk`, form 1: the box-level `.run` equation
  pin gloas `EthCLSpecs.Proofs.Gloas.processBuilderPendingPayments_run
    { target := some `EthCLSpecs.Gloas.processBuilderPendingPayments
      shape := "runOk"
      blockInputs := #[]
      inputs := #["preState"] }
  -- `.runOk`, form 2: the `runPure` reading
  pin gloas `EthCLSpecs.Proofs.Gloas.processBuilderPendingPayments_run_of_fits
    { target := some `EthCLSpecs.Gloas.processBuilderPendingPayments
      shape := "runOk"
      blockInputs := #[]
      inputs := #["preState"] }
  -- `.bound` with implicit value binders, and no spec function on the
  -- conclusion's left side: the target is none, the shape matches
  pin gloas `EthCLSpecs.Proofs.Gloas.getPtcElseOffset_lt_next_slot
    { target := none
      shape := "bound"
      blockInputs := #[]
      inputs := #["slot", "curSlot"] }
  -- `.bound`, explicit binders
  pin gloas `EthCLSpecs.Proofs.Gloas.getPtcElseOffset_lt_same_slot
    { target := none
      shape := "bound"
      blockInputs := #[]
      inputs := #["slot"] }
  -- a block input puts the theorem's base-source-only rule in play
  pin gloas `EthCLSpecs.Proofs.Gloas.processOperations_eq_seq
    { target := some `EthCLSpecs.Gloas.processOperations
      shape := "eq"
      blockInputs := #["body"]
      inputs := #["body"] }
  -- a function-typed input folds into `.unsupported` (§7.4)
  pin fulu `EthCLSpecs.Proofs.Fulu.modBalance_pureState
    { target := some `EthCLSpecs.Fulu.modBalance
      shape := "unsupported"
      blockInputs := #[]
      inputs := #["state", "i", "f"] }
  -- the target sits under a `GetElem` projection, the walk finds it (§7.2)
  pin gloas `EthCLSpecs.Proofs.Gloas.initializePtcWindow_lt
    { target := some `EthCLSpecs.Gloas.initializePtcWindow
      shape := "eq"
      blockInputs := #[]
      inputs := #["state", "i"] }
  -- an `↔` whose left side is not `… = true` matches no shape
  pin gloas `EthCLSpecs.Proofs.Gloas.processOperations_run_ok_iff
    { target := some `EthCLSpecs.Gloas.processOperations
      shape := "unsupported"
      blockInputs := #["body"]
      inputs := #["preState", "postState", "body"] }
  -- a `Store` input is a block input (§1.2); the implicit
  -- `{map : MapKind}` binder is a type parameter, so it stays out of the
  -- inputs and the bound stands
  pin gloas `EthCLSpecs.Proofs.Gloas.updateCheckpoints_justifiedEpoch_le
    { target := none
      shape := "bound"
      blockInputs := #["store"]
      inputs := #["store", "j", "f"] }
  -- an unknown instance seam folds into `.unsupported` (§7.5)
  pin gloas `EthCLSpecs.Proofs.Gloas.getSlotsSinceGenesis_run_of_time_eq_genesis
    { target := some `EthCLSpecs.Gloas.getSlotsSinceGenesis
      shape := "unsupported"
      blockInputs := #["store"]
      inputs := #["store"] }
  -- a box lemma names its family in the reason (§7.3, rule 7), which the
  -- report counts apart from the other unsupported reasons
  pin gloas `EthCLSpecs.Proofs.Gloas.keepsUncached_getBlockRoot
    { target := some `EthCLSpecs.Gloas.getBlockRoot
      shape := "unsupported"
      blockInputs := #[]
      inputs := #["state", "epoch"] }

end EthCLSpecs.Tests.TheoremVectorsPins
