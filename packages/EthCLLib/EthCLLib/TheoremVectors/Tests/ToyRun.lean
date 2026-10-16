import SizzLean
import EthCLLib.Spec.Hasher
import EthCLLib.Spec.State
import EthCLLib.Proofs.Run

/-!
# `EthCLLib.TheoremVectors.Tests.ToyRun`: the run-shape theorems

The toy fixtures the stage-7 run-shape tests drive
(`THEOREM_VECTORS_ARCHITECTURE.md` §7.3, forms 2 and 4): a toy SSZ state
container with one field, and three toy actions over the boxed state in
the `GloasRun` style, `StateT` over `Except` threading the uncached box.
The third action, `toyIndexMiss`, reads past the end of a one-element
table, so its reject is the SSZ `IndexError` the pyspec format's tests
lift to the flagged `outOfBounds` bucket (§13.5).

The conclusion shapes are the reader's run forms. `toyRunOk` states
`act.run (pureState pre) = .ok (ret, pureState post)` (form 2), with the
pre-state a state-typed value binder and the post-state a term over
the binders alone, which is what §7.3's match requires. `toyRunError`
states the error form (form 4). Two `runPure`-form theorems beside them
carry the value-level readings: `toyRunPureOkSecond` states form 3 over
two state binders and runs on the second, which pins §7.3's type rule,
and `toyRunPureError` states form 5. Beside the clean fixtures, the module
holds the two disagreement fixtures the stage-7 pins drive
(`THEOREM_VECTORS_ARCHITECTURE.md` §18): `toyWrongRunOk`, whose compiled
implementation rejects where the kernel's body returns `.ok`, and
`toyCleanRunError`, whose compiled implementation returns cleanly where
the kernel's body rejects. Both proofs stay `rfl`; only the compiled code
disagrees. The first two actions' error type is `String`, which already
carries the `Repr` instance the miss assemblers need; `toyIndexMiss`
rejects with the SSZ `IndexError`.

## Lean idioms annotated

- `deriving SSZRepr` gives the toy container the SSZ type description the
  probe serializes and hashes through, the same way the fork's containers
  get theirs.
- The actions spell the `StateT` type directly, so the reader's
  `StateT.run` head match sees the spine it looks for; `pureState` is the
  uncached box, the only box a theorem builds.
- `rfl` proves both theorems: `StateT.run` unfolds to the action applied
  to the box, and the box's `view` of `pureState s` reduces to `s`.
-/

set_option autoImplicit false

open SizzLean (SSZRepr)
open SizzLean.Cache
open EthCLLib.Spec (HasherTag arrGetIdx IndexError)
open EthCLLib.Proofs (pureState runPure)

namespace EthCLLib.TheoremVectors.Tests.ToyRun

/-- The toy state: one field, the balance. -/
structure ToyState where
  /-- The field the `.runOk` action writes. -/
  bal : UInt64
  deriving Inhabited, SSZRepr

/-- The toy action that sets the balance and returns nothing. -/
def toySetBal [HasherTag] (v : UInt64) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) Unit :=
  fun b => .ok ((), pureState { b.view with bal := v })

/-- The `.runOk` toy theorem (§7.3, form 2). -/
theorem toyRunOk [HasherTag] (s : ToyState) :
    (toySetBal 42).run (pureState s) = .ok ((), pureState { s with bal := 42 }) :=
  rfl

/-- The toy action that rejects with a constant error. -/
def toyFail [HasherTag] :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) Unit :=
  throw "boom"

/-- The `.runError` toy theorem (§7.3, form 4). -/
theorem toyRunError [HasherTag] (s : ToyState) :
    toyFail.run (pureState s) = .error "boom" :=
  rfl

/-- The toy action that reads past the end of a one-element table: the
modeled index miss (`THEOREM_VECTORS_ARCHITECTURE.md` §13.5). The read
runs through `arrGetIdx`, so the reject is the genuine `IndexError`
carrying the index and the bound, the shape the spec layer lifts to
`outOfBounds`. The error type is the SSZ `IndexError`: the toy interface
lifts it through `ErrorConv IndexError StateTransitionError`, the same
lift the fork bodies take, and the driver scores the result as the
flagged `likelyBug` reject. -/
def toyIndexMiss [HasherTag] (i : Nat) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except IndexError) Unit :=
  fun b =>
    -- The `let` pins `arrGetIdx`'s monad. The body's expected type is the
    -- unfolded `StateT` run type, so the bare call would unify `m` with
    -- `Except` and mistype the array element.
    let read : Except IndexError UInt64 := arrGetIdx #[b.view.bal] i
    read.map (fun _ => ((), b))

/-- The index-miss run: the read at index 5 of the one-element table
rejects with `IndexError.indexError 5 1`. -/
theorem toyIndexMissRun [HasherTag] (s : ToyState) :
    (toyIndexMiss 5).run (pureState s) = .error (IndexError.indexError 5 1) :=
  rfl

/-- The `runPure`-form `.runOk` reading over two state binders (§7.3,
form 3): the run's store is the second binder, `s`, and the first one,
`_other`, threads beside it untouched. §7.3's type rule picks the store
whatever the binder's position; the Fulu balance theorems state the
same shape over two `BeaconState` binders. -/
theorem toyRunPureOkSecond [HasherTag] (_other s : ToyState) :
    runPure (toySetBal 42) s = .ok ((), { s with bal := 42 }) :=
  rfl

/-- The `runPure`-form `.runError` reading (§7.3, form 5): the error
carries no post-state, and the store arrives as the plain binder. -/
theorem toyRunPureError [HasherTag] (s : ToyState) :
    runPure toyFail s = .error "boom" :=
  rfl

/-! ## The value-style mutators (§11.3's output rule) -/

/-- The value-style toy action, `increaseBalance`'s shape: it takes the
state it writes as an argument and returns the mutated state as its
value, while the threaded store passes through untouched. -/
def toyBumpBal [HasherTag] (st : ToyState) (v : UInt64) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) ToyState :=
  fun b => .ok ({ st with bal := st.bal + v }, b)

/-- The value-style `.runOk` toy theorem (§7.3, form 3, two state
binders): the run's return value is the mutated `state`, and the
threaded `preState` passes through. §11.3's output rule records the
return value, so the record's output carries the written balance. -/
theorem toyRunValueOk [HasherTag] (state preState : ToyState) :
    runPure (toyBumpBal state 1) preState
      = .ok ({ state with bal := state.bal + 1 }, preState) :=
  rfl

/-- The boxed-value spelling of `toyBumpBal`: it returns the mutated
state wrapped in the box, the form the fork's `State` abbrev gives the
Fulu balance mutators' return values. -/
def toyBumpBalBox [HasherTag] (st : ToyState) (v : UInt64) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String)
      (SSZ.Box HasherTag.H ToyState) :=
  fun b => .ok (pureState { st with bal := st.bal + v }, b)

/-- The boxed-value `.runOk` toy theorem: the return value's type is the
box, so the record picks the pair's `.1` through the box's `.view` read
and records the container's bytes. -/
theorem toyRunBoxValueOk [HasherTag] (state preState : ToyState) :
    runPure (toyBumpBalBox state 1) preState
      = .ok (pureState { state with bal := state.bal + 1 }, preState) :=
  rfl

/-! ## The disagreement fixtures (§18) -/

/-- The compiled body of `toyWrongSetBal`: rejects where the kernel's
body returns `.ok`. The binder name carries the underscore because the
rejection reads no argument; the signature still matches `toyWrongSetBal`. -/
private def toyWrongSetBalImpl [HasherTag] (_v : UInt64) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) Unit :=
  fun _ => throw "toy: the wrong run rejected"

/-- The kernel's `.runOk` action: sets the balance. The compiled
implementation above rejects instead, so the kernel and the compiled
code disagree. -/
@[implemented_by toyWrongSetBalImpl]
def toyWrongSetBal [HasherTag] (v : UInt64) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) Unit :=
  fun b => .ok ((), pureState { b.view with bal := v })

/-- The `.runOk` disagreement theorem. The kernel proves it with `rfl`;
the compiled code rejects the run. -/
theorem toyWrongRunOk [HasherTag] (s : ToyState) :
    (toyWrongSetBal 42).run (pureState s) =
      .ok ((), pureState { s with bal := 42 }) :=
  rfl

/-- The compiled body of `toyCleanFail`: returns cleanly where the
kernel's body rejects. -/
private def toyCleanFailImpl [HasherTag] :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) Unit :=
  fun b => .ok ((), b)

/-- The kernel's `.runError` action: rejects. The compiled
implementation above returns cleanly instead. -/
@[implemented_by toyCleanFailImpl]
def toyCleanFail [HasherTag] :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) Unit :=
  throw "boom"

/-- The `.runError` ran-clean theorem. The kernel proves it with `rfl`;
the compiled code returns cleanly. -/
theorem toyCleanRunError [HasherTag] (s : ToyState) :
    toyCleanFail.run (pureState s) = .error "boom" :=
  rfl

end EthCLLib.TheoremVectors.Tests.ToyRun
