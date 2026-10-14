import Lean
import SizzLean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Witness.Random
import EthCLLib.TheoremVectors.Witness.Shrink
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.Support

/-!
# `EthCLLib.TheoremVectors.Tests.Random`: the draw, the random source, the shrink

Build-gate checks for stage 4 (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4, §9.5,
§9.6), over a toy container:

- the generic `SSZRepr` draw (§9.5) produces bytes the strict decode
  accepts, and the same seed draws the same bytes twice;
- the random source (§9.4) wins a container theorem with no seed: it
  draws, grounds the hypothesis's container read, and hands the case to
  the loop's check;
- the shrink (§9.6) reaches a witness whose bytes are smaller than the
  first draw's, and the check still holds.

The toy binding's `stateType` is the toy container itself, so the base
source refuses it the way it refuses the fork's state (§9.4), and the
random source is what finds the witness.

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

/-- The random source's drive theorem: the hypothesis reads the drawn
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
into the test failure it is. -/
private def builtProbe (ctx : StatementCtx) (cases : Array Case) :
    MetaM (ProbeInfo × Probe) := do
  match ← Probe.ofStatement toyBoxBinding .minimal ctx cases #[] with
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
      let (cases, dropped) ← Prepare.pass stmt
      unless cases.size == 1 && dropped.isEmpty do
        throwError s!"expected one prepared case, got {cases.size}"
      let (info, probe) ← builtProbe ctx cases
      let drawn1 := probe.sample 7 8
      let drawn2 := probe.sample 7 8
      unless (drawn1.zip drawn2).all fun (a, b) => compareBytes a b do
        throwError "the same seed drew different bytes (§9.5)"
      for b in drawn1 do
        match SizzLean.SSZ.deserialize (T := ToyBox) b with
        | .ok _ => pure ()
        | .error e =>
          throwError s!"the draw's bytes did not decode: {repr e}"
      -- ── the random source's drive (§9.4): no seed, the base source
      -- refuses the state-typed container, the random source wins
      let sources : Array WitnessSource := #[baseSource, bitVecSource, randomSource]
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let c := cases[0]!
      match ← searchCase sources sctx stmt c with
      | .ok (a, won) =>
        unless won == .random do
          throwError s!"expected the random source to win, got {won.tag}"
        unless probe.check c.index a do
          throwError "the random witness failed the check"
        -- ── the shrink pin (§9.6): a smaller value or smaller bytes,
        -- and the check still holds
        let shrunk ← shrinkWitness probe c.index 200 a
        unless probe.check c.index shrunk do
          throwError "the shrunk witness failed the check"
        unless Tests.Support.leOf shrunk[0]! < Tests.Support.leOf a[0]!
            || shrunk[0]!.size < a[0]!.size do
          throwError s!"the shrunk container is not smaller \
            ({shrunk[0]!.size} against {a[0]!.size})"
      | .error f =>
        throwError s!"the random source found no witness: {repr f}"
    -- ── the two-read entry (§9.4, the stage-4 outcome): one maximal
    -- container-mentioning subterm holding two guarded reads, whose
    -- checks fold innermost first, and a drawn list gates both
    Statement.readIn binding
      `EthCLLib.TheoremVectors.Tests.Random.toyTwoReads fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (cases, _) ← Prepare.pass stmt
      unless cases.size == 1 do
        throwError s!"toyTwoReads: expected one case, got {cases.size}"
      let c := cases[0]!
      let (info, probe) ← builtProbe ctx cases
      -- the defaults leave both reads past an empty drawn list's end: the
      -- gate answers false, and the compiled reads never evaluate
      unless !(probe.safe c.index probe.defaults).all (· == true) do
        throwError "toyTwoReads: the empty default should fail the gate"
      -- the search wins: a draw with both reads in range passes the gate
      -- and the check, and the gate rejects the short draws without
      -- evaluating them
      let sctx2 ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let sources2 : Array WitnessSource := #[baseSource, bitVecSource, randomSource]
      match ← searchCase sources2 sctx2 stmt c with
      | .ok (a, won) =>
        unless won == .random do
          throwError s!"toyTwoReads: expected the random source to win, \
            got {won.tag}"
        unless (probe.safe c.index a).all (· == true) do
          throwError "toyTwoReads: the winning candidate passed an unsafe \
            gate"
        unless probe.check c.index a do
          throwError "toyTwoReads: the winning candidate failed the check"
      | .error f =>
        throwError s!"toyTwoReads: the search found nothing: {repr f}"
