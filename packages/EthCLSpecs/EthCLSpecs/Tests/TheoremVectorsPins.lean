import Lean
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Built
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Sampleable
import EthCLSpecs.Gloas.Interface
import EthCLSpecs.Fulu.Interface
import EthCLSpecs.Heze.Interface
import EthCLSpecs.Proofs.Gloas
import EthCLSpecs.Proofs.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Gloas
import EthCLSpecs.TheoremVectors.Bindings.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Heze
import EthCLSpecs.TheoremVectors.Builders.Gloas
import EthCLSpecs.TheoremVectors.Builders.Fulu
import EthCLSpecs.TheoremVectors.Builders.Heze

/-!
# `EthCLSpecs.Tests.TheoremVectorsPins`: the statement reader's known answers

Spec-half pins for the theorem-vector generator's statement reader
(`THEOREM_VECTORS_ARCHITECTURE.md` §7; the plan's stage 1, step 9) and, since
stage 3, its prepare pass (§8). Ten theorems with known shapes run through
`Statement.readIn` and `Scope.classify`, and each pin checks the reader's
answer: target, shape, block inputs, and the input names in binder order.
Three stage-3 acceptance theorems then run through `Prepare.pass`, and
each pin checks the split's answer: the disjunct count, the sides, and the
conjunctions' shape-relevant constants. Stage 4's draw pin and stage 6's
state-builder pins close the file.

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
  -- a box lemma names its family in the reason (§7.3, rule 8), which the
  -- report counts apart from the other unsupported reasons; the target
  -- walk reads the conclusion's left side (§7.2), and a box lemma's
  -- conclusion names no function under test, so the target is none
  pin gloas `EthCLSpecs.Proofs.Gloas.keepsUncached_getBlockRoot
    { target := none
      shape := "unsupported"
      blockInputs := #[]
      inputs := #["state", "epoch"] }

  -- ── The prepare pass's answers for the three stage-3 acceptance
  -- theorems (§8). Each pin folds inside the reader's telescope scope,
  -- because the statement and its disjuncts cannot leave it.

  let prepareDisjuncts (thm : Name) : CommandElabM (Nat × Array (Option Bool)) :=
    liftTermElabM do
      Statement.readIn gloas thm fun ctx => do
        let stmt ← Scope.classify gloas ctx.stmt
        let (disjuncts, dropped) ← Prepare.pass stmt
        unless dropped.isEmpty do
          throwError s!"pin {thm}: the prepare pass dropped \
            {dropped.size} note(s): {repr dropped}"
        return (disjuncts.size, disjuncts.map (·.side))
  -- the slot-successor bound: one disjunct over the two rewritten hypotheses
  let (n, sides) ← prepareDisjuncts `EthCLSpecs.Proofs.Gloas.getPtcElseOffset_lt_next_slot
  unless n == 1 && sides == #[none] do
    throwError s!"pin getPtcElseOffset_lt_next_slot: {n} disjunct(s) with \
      sides {repr sides}, expected one unsplit disjunct"
  -- the builder-cover bound: the true side's conjunction is one
  -- disjunct, the false side's De Morgan is two
  let (n, sides) ← prepareDisjuncts `EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff
  unless n == 3 && sides == #[some true, some false, some false] do
    throwError s!"pin canBuilderCoverBid_iff: {n} disjunct(s) with sides \
      {repr sides}, expected three (one per side pair)"
  -- the payload-attestation gates: one true-side disjunct, one
  -- false-side disjunct per check
  let (n, sides) ← prepareDisjuncts
    `EthCLSpecs.Proofs.Gloas.isValidIndexedPayloadAttestation_eq_true_iff_checks
  unless n == 5 && sides.countP (· == some false) == 4 do
    throwError s!"pin isValidIndexedPayloadAttestation_eq_true_iff_checks: \
      {n} disjunct(s) with sides {repr sides}, expected five (one true side, \
      one per check)"

  -- ── The generic draw's answers (§9.5): the same seed draws the same
  -- state twice, and the drawn bytes pass the state's own strict decode.
  -- The draw runs through the generic `SSZRepr` instance at the minimal
  -- preset.
  liftTermElabM do
    let g : Plausible.Gen (@EthCLSpecs.Gloas.BeaconState EthCLSpecs.Gloas.minimal) :=
      Plausible.SampleableExt.interpSample _
    let some drawn1 := EthCLLib.TheoremVectors.runDrawPure 7 8 g
      | throwError "pin draw: the generator failed"
    let some drawn2 := EthCLLib.TheoremVectors.runDrawPure 7 8 g
      | throwError "pin draw: the generator failed"
    let b1 := SizzLean.SSZ.serialize drawn1
    let b2 := SizzLean.SSZ.serialize drawn2
    unless EthCLLib.TheoremVectors.compareBytes b1 b2 do
      throwError "pin draw: the same seed drew different bytes (§9.5)"
    match SizzLean.SSZ.deserialize (T :=
        @EthCLSpecs.Gloas.BeaconState EthCLSpecs.Gloas.minimal) b1 with
    | .ok _ => pure ()
    | .error e =>
      throwError s!"pin draw: the drawn bytes did not decode: {repr e}"

/-- One builder pin: serialize the state and decode it through the fork
interface's own `stateRoot`, failing with the builder's name when it
does not. The interface is the per-fork value the call site names
(`gloasInterface`, `fuluInterface`, `hezeInterface`); the per-fork pin
blocks below stay separate. -/
private def pinStateRoot (iface : EthCLLib.PySpecTests.ForkInterface)
    (name : String) (bytes : ByteArray) : MetaM Unit := do
  match iface.stateRoot bytes with
  | .ok _ => pure ()
  | .error e =>
    throwError s!"pin {name}: the state did not decode through the \
      fork's stateRoot: {repr e}"

/-- The binding's minimal instance set, the one every record writes at.
File-level definitions carry the local instance attribute; the drive's
`letI` binders left the statements after them without the earlier
statements' locals and instances under this module's build, and the
pins need both across statements. `local` scopes the four to this file, so no other test
module inherits them. The hasher needs no entry: the builders pin it
locally, and the serialize and `stateRoot` reads take no tag. -/
@[reducible] private def tvMinimalPreset : EthCLSpecs.Gloas.Preset :=
  EthCLSpecs.Gloas.minimal
@[reducible] private def tvMinimalConfig : EthCLSpecs.Gloas.Config :=
  EthCLSpecs.Gloas.minimalConfig
@[reducible] private def tvVerifyOff : EthCLLib.Spec.CryptoBackend :=
  EthCLLib.Spec.CryptoBackend.verifyOff
/-- The parent fork's config, for the previous version the `upgraded`
pin reads; a distinct class from the Gloas one, so the two locals do not
compete. -/
@[reducible] private def tvFuluConfig : EthCLSpecs.Fulu.Config :=
  EthCLSpecs.Fulu.minimalConfig
/-- The Fulu preset, beside its config: Fulu's catalog builds under it. -/
@[reducible] private def tvFuluPreset : EthCLSpecs.Fulu.Preset :=
  EthCLSpecs.Fulu.minimal
/-- The Heze preset, for Heze's catalog; the fork's `upgraded` reaches
the Gloas spine through the `Downgrade` bridge. -/
@[reducible] private def tvHezePreset : EthCLSpecs.Heze.Preset :=
  EthCLSpecs.Heze.minimal
/-- The Heze config, whose `hezeForkVersion` the fork record pins read. -/
@[reducible] private def tvHezeConfig : EthCLSpecs.Heze.Config :=
  EthCLSpecs.Heze.minimalConfig
attribute [local instance] tvMinimalPreset tvMinimalConfig tvVerifyOff
  tvFuluConfig tvFuluPreset tvHezePreset tvHezeConfig

-- The state builders' answers (§9.9, the plan's stage 6, step 7, and
-- stage 9): every fork's catalog runs, each builder's state decodes
-- through its fork's own `stateRoot`, `advanced` at the first epoch
-- boundary lands on the boundary slot, `upgraded` carries the fork
-- version with the previous one its fork boundary gives, and `withQueue`
-- leaves
-- builders in the registry the onboarding step put there and validator
-- deposits in the queue it kept. The instances are each binding's
-- minimal set, the preset every record writes at; the pins run at
-- elaboration time, the way the draw pin above does.
--
-- Expected noise: this block's checks force the builders' interpreted
-- evaluation, and every `advanced`/`withQueue` run crosses an epoch
-- boundary. `process_epoch` reads the per-validator lists
-- `inactivityScores` (`EpochProcessing.lean`) and the participation
-- flags (`Accessors.lean`, `getUnslashedParticipatingIndices`) with
-- `!`, and the `genesis` builder leaves those lists at `default`,
-- empty. Each read past the end prints one `PANIC at outOfBounds` line,
-- answers `default`, and drops the write-back, so the built states
-- carry the empty lists through. The pins ask for a strict decode and
-- coarse shape only, which the empty lists satisfy, and the committed
-- built hints replay through the same builders, so the answers this
-- block checks are the ones the generator records. Sizing the lists in
-- `genesis` would change every built state's bytes and churn the hints,
-- so the block leaves the builders alone. The count scales with the
-- registry length times the epoch boundaries the grid's slots cross;
-- the `just theorem-vectors` recipe banners it.
open EthCLLib.Spec in
run_cmd do
  liftTermElabM do
    -- the grid's epoch boundary reads the fork's constant through the
    -- framework's own face, at both presets: minimal 8, mainnet 32, so a
    -- silent fallback to 8 cannot hide a broken read
    let gloas : ForkBinding ←
      readBinding (`EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas)
    unless (← Built.epochBoundaryOf gloas .minimal) == 8 do
      throwError "pin epoch boundary: minimal is not 8"
    unless (← Built.epochBoundaryOf gloas .mainnet) == 32 do
      throwError "pin epoch boundary: mainnet is not 32"
    let boundary : Nat := EthCLSpecs.Gloas.Const.slotsPerEpoch
    -- `genesis`: decodes, and every validator is active from the genesis
    -- epoch
    let stG := EthCLSpecs.TheoremVectors.Builders.Gloas.genesis
      { validators := 8, balance := 32000000000 }
    pinStateRoot EthCLSpecs.Gloas.Interface.gloasInterface "genesis"
      (SizzLean.SSZ.serialize stG)
    unless stG.validators.val.size == 8 &&
        (stG.validators.val.all fun v =>
          v.activationEpoch == EthCLSpecs.Gloas.Const.genesisEpoch) do
      throwError "pin genesis: the registry is not eight active validators"
    -- `advanced` at the first epoch boundary: the slot is the boundary,
    -- which is the plan's pin. The plain value's own field projection
    -- reads the slot; `sszGet` reads a box.
    let stA := EthCLSpecs.TheoremVectors.Builders.Gloas.advanced
      { validators := 8, slot := boundary }
    pinStateRoot EthCLSpecs.Gloas.Interface.gloasInterface "advanced"
      (SizzLean.SSZ.serialize stA)
    unless stA.slot == UInt64.ofNat boundary do
      throwError s!"pin advanced: slot is {stA.slot}, expected {boundary}"
    -- `upgraded`: the fork version is the config's, and the previous
    -- version is the chain's genesis fork version, the one the parent's
    -- config names
    let stU := EthCLSpecs.TheoremVectors.Builders.Gloas.upgraded
      { validators := 8, slot := boundary }
    pinStateRoot EthCLSpecs.Gloas.Interface.gloasInterface "upgraded"
      (SizzLean.SSZ.serialize stU)
    unless stU.forkData.currentVersion ==
        EthCLSpecs.Gloas.Const.gloasForkVersion do
      throwError "pin upgraded: the fork version is not the config's"
    unless stU.forkData.previousVersion ==
        EthCLSpecs.Fulu.Const.genesisForkVersion do
      throwError "pin upgraded: the previous version is not the \
chain's genesis fork version"
    -- `withQueue` at the grid's queue step, the table's literal slot
    -- 40: two builder deposits reached the registry at the deposit
    -- balance, two validator deposits stayed queued
    let stQ := EthCLSpecs.TheoremVectors.Builders.Gloas.withQueue
      { validators := 16, slot := 40, queue := 4 }
    pinStateRoot EthCLSpecs.Gloas.Interface.gloasInterface "withQueue"
      (SizzLean.SSZ.serialize stQ)
    unless stQ.builders.val.size == 2 do
      throwError s!"pin withQueue: {stQ.builders.val.size} builders in the \
        registry, expected two"
    unless stQ.builders.val.all fun b => b.balance == 32000000000 do
      throwError "pin withQueue: a builder's balance is not the deposit's"
    unless stQ.pendingDeposits.val.size == 2 do
      throwError s!"pin withQueue: {stQ.pendingDeposits.val.size} deposits \
        stayed queued, expected two"

    -- ── Fulu's catalog answers (§9.9): the base fork's two rows. The
    -- boundary read goes through the framework's own face, so a silent
    -- fallback to 8 cannot hide a broken read there either.
    let fulu : ForkBinding ←
      readBinding (`EthCLSpecs.TheoremVectors.Bindings.Fulu.fulu)
    unless (← Built.epochBoundaryOf fulu .minimal) == 8 do
      throwError "pin epoch boundary: fulu minimal is not 8"
    let fuluBoundary : Nat := EthCLSpecs.Fulu.Const.slotsPerEpoch
    -- `genesis`: decodes, every validator is active from the genesis
    -- epoch, and the fork record names the chain's genesis version on
    -- both sides, Fulu being the base fork
    let stGF := EthCLSpecs.TheoremVectors.Builders.Fulu.genesis
      { validators := 8, balance := 32000000000 }
    pinStateRoot EthCLSpecs.Fulu.Interface.fuluInterface "fulu genesis"
      (SizzLean.SSZ.serialize stGF)
    unless stGF.validators.val.size == 8 &&
        (stGF.validators.val.all fun v =>
          v.activationEpoch == EthCLSpecs.Fulu.Const.genesisEpoch) do
      throwError "pin fulu genesis: the registry is not eight active \
        validators"
    unless stGF.forkData.previousVersion == stGF.forkData.currentVersion &&
        stGF.forkData.currentVersion ==
          EthCLSpecs.Fulu.Const.genesisForkVersion do
      throwError "pin fulu genesis: the fork record does not name the \
        chain's genesis version on both sides"
    -- `advanced` at the first epoch boundary: the slot is the boundary
    let stAF := EthCLSpecs.TheoremVectors.Builders.Fulu.advanced
      { validators := 8, slot := fuluBoundary }
    pinStateRoot EthCLSpecs.Fulu.Interface.fuluInterface "fulu advanced"
      (SizzLean.SSZ.serialize stAF)
    unless stAF.slot == UInt64.ofNat fuluBoundary do
      throwError s!"pin fulu advanced: slot is {stAF.slot}, \
        expected {fuluBoundary}"

    -- ── Heze's catalog answers (§9.9): the same four rows Gloas walks.
    -- The boundary read goes through the framework's own face.
    let heze : ForkBinding ←
      readBinding (`EthCLSpecs.TheoremVectors.Bindings.Heze.heze)
    unless (← Built.epochBoundaryOf heze .minimal) == 8 do
      throwError "pin epoch boundary: heze minimal is not 8"
    let hezeBoundary : Nat := EthCLSpecs.Heze.Const.slotsPerEpoch
    -- `genesis`: decodes, every validator is active from the genesis
    -- epoch, and the fork record names the config's `hezeForkVersion` on
    -- both sides, the seam the catalog reads
    let stGH := EthCLSpecs.TheoremVectors.Builders.Heze.genesis
      { validators := 8, balance := 32000000000 }
    pinStateRoot EthCLSpecs.Heze.Interface.hezeInterface "heze genesis"
      (SizzLean.SSZ.serialize stGH)
    unless stGH.validators.val.size == 8 &&
        (stGH.validators.val.all fun v =>
          v.activationEpoch == EthCLSpecs.Heze.Const.genesisEpoch) do
      throwError "pin heze genesis: the registry is not eight active \
        validators"
    unless stGH.forkData.previousVersion == stGH.forkData.currentVersion &&
        stGH.forkData.currentVersion ==
          EthCLSpecs.Heze.Const.hezeForkVersion do
      throwError "pin heze genesis: the fork record does not name the \
        config's heze version on both sides"
    -- `advanced` at the first epoch boundary: the slot is the boundary
    let stAH := EthCLSpecs.TheoremVectors.Builders.Heze.advanced
      { validators := 8, slot := hezeBoundary }
    pinStateRoot EthCLSpecs.Heze.Interface.hezeInterface "heze advanced"
      (SizzLean.SSZ.serialize stAH)
    unless stAH.slot == UInt64.ofNat hezeBoundary do
      throwError s!"pin heze advanced: slot is {stAH.slot}, \
        expected {hezeBoundary}"
    -- `upgraded`: the current version is the config's Heze version, and
    -- the previous version is the Gloas version the pre-state carries
    let stUH := EthCLSpecs.TheoremVectors.Builders.Heze.upgraded
      { validators := 8, slot := hezeBoundary }
    pinStateRoot EthCLSpecs.Heze.Interface.hezeInterface "heze upgraded"
      (SizzLean.SSZ.serialize stUH)
    unless stUH.forkData.currentVersion ==
        EthCLSpecs.Heze.Const.hezeForkVersion do
      throwError "pin heze upgraded: the fork version is not the \
        config's"
    unless stUH.forkData.previousVersion ==
        EthCLSpecs.Gloas.Const.gloasForkVersion do
      throwError "pin heze upgraded: the previous version is not the \
        Gloas version the pre-state carries"
    -- `withQueue` at the grid's queue step, the table's literal slot
    -- 40: the same knobs the Gloas pin runs, so the same two builder
    -- deposits reach the registry and two validator deposits stay queued
    let stQH := EthCLSpecs.TheoremVectors.Builders.Heze.withQueue
      { validators := 16, slot := 40, queue := 4 }
    pinStateRoot EthCLSpecs.Heze.Interface.hezeInterface "heze withQueue"
      (SizzLean.SSZ.serialize stQH)
    unless stQH.builders.val.size == 2 do
      throwError s!"pin heze withQueue: {stQH.builders.val.size} builders \
        in the registry, expected two"
    unless stQH.builders.val.all fun b => b.balance == 32000000000 do
      throwError "pin heze withQueue: a builder's balance is not the \
        deposit's"
    unless stQH.pendingDeposits.val.size == 2 do
      throwError s!"pin heze withQueue: {stQH.pendingDeposits.val.size} \
        deposits stayed queued, expected two"

end EthCLSpecs.Tests.TheoremVectorsPins
