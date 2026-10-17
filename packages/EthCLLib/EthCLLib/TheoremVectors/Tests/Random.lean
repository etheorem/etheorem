import Lean
import SizzLean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Searcher
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Witness.Random
import EthCLLib.TheoremVectors.Witness.Shrink
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.Support

/-!
# `EthCLLib.TheoremVectors.Tests.Random`: the draw, the random searcher, the shrink

Build-gate checks for stage 4 (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4, §9.5,
§9.6), over a toy container:

- the generic `SSZRepr` draw (§9.5) produces bytes the strict decode
  accepts, and the same seed draws the same bytes twice;
- the random searcher (§9.4) wins a container theorem with no manual
  terms: it draws, grounds the hypothesis's container read, and hands
  the disjunct to the loop's check;
- the shrink (§9.6) reaches a witness whose bytes are smaller than the
  first draw's, and the check still holds;
- the mainnet cap (§9.4): a state-typed container input at mainnet
  answers `nothing` before any draw, the same statement at minimal
  still draws, and the same statement over a `Nat` state type still
  draws at mainnet, so the cap keys on the state type alone.

The toy binding's `stateType` is the toy container itself, so the base
searcher refuses it the way it refuses the fork's state (§9.4), and the
random searcher is what finds the witness.

## Lean idioms annotated

- The drives run inside `run_cmd` with `liftTermElabM` and fold inside the
  reader's telescope scope, the same shapes the stage-2 and stage-3 test
  modules use.
- `deriving` on the toy structure hands the generator its `SSZRepr`
  description, which is what the generic instance walks (§9.5).
-/

set_option autoImplicit false

open Lean
open SizzLean (SSZRepr)
open EthCLLib.Spec (HasherTag)

namespace EthCLLib.TheoremVectors.Tests.Random

/-- The toy container: one scalar field, one bounded list. -/
structure ToyBox where
  /-- The field the toy theorem's hypothesis reads. -/
  tag   : UInt64
  /-- The field the shrink cuts. -/
  items : SizzLean.Repr.SSZList UInt64 8
  deriving Inhabited, SSZRepr

/-- The toy function under test. -/
def toyTag (b : ToyBox) : UInt64 := b.tag

/-- The random searcher's drive theorem: the hypothesis reads the drawn
container, the conclusion is the bound the executor records. -/
theorem toyBoxBound [HasherTag] (b : ToyBox) (h : b.tag < 10) :
    toyTag b < 1000 := by
  show b.tag < 1000
  have h' : b.tag.toNat < 10 := UInt64.lt_iff_toNat_lt.mp h
  rw [UInt64.lt_iff_toNat_lt]
  show b.tag.toNat < 1000
  omega

/-- The two-read drive theorem: one maximal container-mentioning subterm
holding two guarded reads, the entry shape the read bounds' fold exists
for (§9.4, the stage-4 outcome). The conclusion is reflexive, so the
probe's answer rides on the hypothesis alone. -/
theorem toyTwoReads [HasherTag] (b : ToyBox)
    (_h : b.items[0]! + b.items[1]! < 100) :
    toyTag b = toyTag b := rfl

/-- A toy binding whose state type is the toy container. -/
def toyBoxBinding : ForkBinding :=
  { EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding with
      stateType := `EthCLLib.TheoremVectors.Tests.Random.ToyBox }

/-- The evaluated probe for the drive theorem, with a skip reason turned
into the test failure it is. The theorem binds no preset seam, so the
probe builds the same at both presets, and both toy bindings declare an
empty `builders` catalog, so the builder face's state dispatch is the
empty stub under either one. -/
private def builtProbe (b : ForkBinding) (ctx : StatementCtx)
    (disjuncts : Array Disjunct) (p : PresetId) : MetaM (ProbeInfo × Probe) := do
  match ← Probe.ofStatement b p ctx disjuncts #[] with
  | .ok r => pure r
  | .error e => throwError s!"the probe refused to build: {e}"

end EthCLLib.TheoremVectors.Tests.Random

open Lean.Elab.Command
open EthCLLib.TheoremVectors
open EthCLLib.TheoremVectors.Tests.Random in
run_cmd do
  liftTermElabM do
    let binding := toyBoxBinding
    -- ── the draw pin (§9.5): the same seed draws the same bytes, and the
    -- strict decode accepts them
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.Random.toyBoxBound fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, dropped) ← Prepare.pass stmt
      unless disjuncts.size == 1 && dropped.isEmpty do
        throwError s!"expected one prepared disjunct, got {disjuncts.size}"
      let (info, probe) ← builtProbe toyBoxBinding ctx disjuncts .minimal
      let drawn1 := probe.sample 7 8
      let drawn2 := probe.sample 7 8
      unless (drawn1.zip drawn2).all fun (a, b) => compareBytes a b do
        throwError "the same seed drew different bytes (§9.5)"
      for b in drawn1 do
        match SizzLean.SSZ.deserialize (T := ToyBox) b with
        | .ok _ => pure ()
        | .error e =>
          throwError s!"the draw's bytes did not decode: {repr e}"
      -- ── the random searcher's drive (§9.4): no manual terms, the base
      -- searcher refuses the state-typed container, the random searcher wins
      let searchers : Array WitnessSearcher := #[baseSearcher, bitVecSearcher, randomSearcher]
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let d := disjuncts[0]!
      match ← searchDisjunct searchers sctx stmt d with
      | .ok (a, won) =>
        unless won == .random do
          throwError s!"expected the random searcher to win, got {won.tag}"
        unless probe.check d.index a do
          throwError "the random witness failed the check"
        -- ── the shrink pin (§9.6): a smaller value or smaller bytes,
        -- and the check still holds
        let shrunk ← shrinkWitness probe d.index 200 a
        unless probe.check d.index shrunk do
          throwError "the shrunk witness failed the check"
        unless Tests.Support.leOf shrunk[0]! < Tests.Support.leOf a[0]!
            || shrunk[0]!.size < a[0]!.size do
          throwError s!"the shrunk container is not smaller \
            ({shrunk[0]!.size} against {a[0]!.size})"
      | .error f =>
        throwError s!"the random searcher found no witness: {repr f}"
    -- ── the two-read entry (§9.4, the stage-4 outcome): one maximal
    -- container-mentioning subterm holding two guarded reads, whose
    -- checks fold innermost first, and a drawn list gates both
    Statement.readIn binding
      `EthCLLib.TheoremVectors.Tests.Random.toyTwoReads fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyTwoReads: expected one disjunct, got {disjuncts.size}"
      let d := disjuncts[0]!
      let (info, probe) ← builtProbe toyBoxBinding ctx disjuncts .minimal
      -- the defaults leave both reads past an empty drawn list's end: the
      -- gate answers false, and the compiled reads never evaluate
      unless !(probe.safe d.index probe.defaults).all (· == true) do
        throwError "toyTwoReads: the empty default should fail the gate"
      -- the search wins: a draw with both reads in range passes the gate
      -- and the check, and the gate rejects the short draws without
      -- evaluating them
      let sctx2 ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let searchers2 : Array WitnessSearcher := #[baseSearcher, bitVecSearcher, randomSearcher]
      match ← searchDisjunct searchers2 sctx2 stmt d with
      | .ok (a, won) =>
        unless won == .random do
          throwError s!"toyTwoReads: expected the random searcher to win, \
            got {won.tag}"
        unless (probe.safe d.index a).all (· == true) do
          throwError "toyTwoReads: the winning candidate passed an unsafe \
            gate"
        unless probe.check d.index a do
          throwError "toyTwoReads: the winning candidate failed the check"
      | .error f =>
        throwError s!"toyTwoReads: the search found nothing: {repr f}"
    -- ── the mainnet cap (§9.4): the toy state is the statement's
    -- container input, so at mainnet the random searcher answers
    -- `nothing` before any draw runs, and at minimal the same statement
    -- still draws
    Statement.readIn binding
      `EthCLLib.TheoremVectors.Tests.Random.toyBoxBound fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"cap drive: expected one disjunct, got {disjuncts.size}"
      let d := disjuncts[0]!
      -- the cap direction: mainnet, no draw, the reason names the cap
      let (infoM, probeM) ← builtProbe toyBoxBinding ctx disjuncts .mainnet
      let sctxM ← Tests.Support.searchCtxOf binding .mainnet
        Tests.ToyFork.scratchOutDir "" stmt ctx infoM probeM
      match ← randomSearcher.search sctxM stmt d with
      | .nothing (some r) =>
        unless r.contains "mainnet cap" do
          throwError s!"cap drive: the mainnet reason does not name the \
            cap: {r}"
      | _ =>
        throwError "cap drive: expected `.nothing` at mainnet"
      unless (← sctxM.drawMemo.get).isEmpty do
        throwError "cap drive: the mainnet cap drew anyway, the memo is \
          not empty"
      -- the negative direction: minimal, the same statement draws
      let (info, probe) ← builtProbe toyBoxBinding ctx disjuncts .minimal
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      match ← randomSearcher.search sctx stmt d with
      | .candidate a =>
        unless probe.check d.index a do
          throwError "cap drive: the minimal draw failed the check"
      | _ =>
        throwError "cap drive: expected a draw at minimal"
      if (← sctx.drawMemo.get).isEmpty then
        throwError "cap drive: the minimal drive did not draw, the memo \
          stayed empty"
      -- the cap keys on the state type alone: the same statement over a
      -- binding whose state type is `Nat` still draws at mainnet
      let (infoP, probeP) ← builtProbe Tests.ToyFork.toyBinding ctx disjuncts
        .mainnet
      let sctxP ← Tests.Support.searchCtxOf Tests.ToyFork.toyBinding .mainnet
        Tests.ToyFork.scratchOutDir "" stmt ctx infoP probeP
      match ← randomSearcher.search sctxP stmt d with
      | .candidate a =>
        if (← sctxP.drawMemo.get).isEmpty then
          throwError "cap drive: the `Nat` state type's mainnet drive \
            left the memo empty"
        unless probeP.check d.index a do
          throwError "cap drive: the `Nat` state type's draw failed the \
            check"
      | _ =>
        throwError "cap drive: expected a draw at mainnet over the \
          `Nat` state type"
