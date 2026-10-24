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
table, so its reject is the SSZ `IndexError` the epoch_processing
format's tests lift to the flagged `outOfBounds` bucket (§13.5).

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
rejects with the SSZ `IndexError`. A third disagreement fixture,
`toyWrongBoxValueEq`, states the projected path's `.eq` over a
disagreeing action: the kernel proves it, and the compiled
implementation rejects, so the projections land on the mixed miss (§18).
The `.eq` face's projected-rule
fixtures close the file's run theorems: two run equations over the whole
`Except`, one `.ok`-valued and one `.error`-valued, the shape the Fulu
balance contracts state.

A final section holds the toy operation handler's fixtures (§13.6): the
`ToyReq` operand container and the `toyOpApply` action the toy
interface's `runOperation` arm runs. Beside it, `toyOpMiss` ignores the
operand and reads past the one-element table's end, the `toyIndexMiss`
shape over the operand, the reject the operations drive's two undriven
check branches pin.

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

/-! ## The `.eq` face's projected output rule (§11.3)

The two run equations stated over the whole `Except`, the shape the Fulu
balance contracts state: the output type is an `Except` over a pair of
boxed states, which carries neither an `SSZRepr` nor a `ToString`
instance, and the right side is a named term over the binders, which is
what keeps the reader's run shapes from firing (§7.3). Both
statements classify `.eq`, so the face's projected rule records the
pair's first component through the box's `.view`. One wins at an `.ok`
point and one at an `.error` point, the two kinds one compiled body must
answer. -/

/-- The toy action that always rejects; its value side is the boxed
state, so the projected rule arms, and every point lands on the rule's
`.error` arm. -/
def toyFailBox [HasherTag] :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String)
      (SSZ.Box HasherTag.H ToyState) :=
  fun _ => throw "boom"

/-- The ok-point run equation's expected value, named so the reader's
run shapes stay off (§7.3). -/
def toyRunBoxValueEqRhs [HasherTag] (state preState : ToyState) :
    Except String (SSZ.Box HasherTag.H ToyState × SSZ.Box HasherTag.H ToyState) :=
  .ok (pureState { state with bal := state.bal + 1 }, pureState preState)

/-- The ok-point `.eq` toy theorem (§11.3's projected rule): the record
is the returned state's container bytes, and the threaded `preState` is
a bystander. -/
theorem toyRunBoxValueEq [HasherTag] (state preState : ToyState) :
    (toyBumpBalBox state 1).run (pureState preState)
      = toyRunBoxValueEqRhs state preState :=
  rfl

/-- The error-point run equation's expected value, named for the same
reason. The binder names carry the underscore because the error carries
no state. -/
def toyRunBoxValueErrorEqRhs [HasherTag] (_state _preState : ToyState) :
    Except String (SSZ.Box HasherTag.H ToyState × SSZ.Box HasherTag.H ToyState) :=
  .error "boom"

/-- The error-point `.eq` toy theorem (§11.3's projected rule): both
sides answer `.error` at every point, so the record follows the
`.runError` row, no output value and the error's repr in the error
slot. -/
theorem toyRunBoxValueErrorEq [HasherTag] (state preState : ToyState) :
    toyFailBox.run (pureState preState)
      = toyRunBoxValueErrorEqRhs state preState :=
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

/-- The compiled body of `toyWrongBoxEq`: rejects where the kernel's
body returns `.ok`. The binder names carry the underscore because the
rejection reads no argument; the signature still matches `toyWrongBoxEq`. -/
private def toyWrongBoxEqImpl [HasherTag] (_st : ToyState) (_v : UInt64) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String)
      (SSZ.Box HasherTag.H ToyState) :=
  fun _ => throw "toy: the wrong projected run rejected"

/-- The kernel's boxed-value action: returns the mutated state. The
compiled implementation above rejects instead, so the kernel and the
compiled code disagree. -/
@[implemented_by toyWrongBoxEqImpl]
def toyWrongBoxEq [HasherTag] (st : ToyState) (v : UInt64) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String)
      (SSZ.Box HasherTag.H ToyState) :=
  fun b => .ok (pureState { st with bal := st.bal + v }, b)

/-- The projected path's mixed-miss theorem (§18): the `.eq` statement
over the whole `Except`, so the projected rule arms, and the compiled
left side rejects where the kernel proved `.ok`. The projections land
one on each side of the point kinds, and the executor's disagreement
print names the rejection repr. -/
theorem toyWrongBoxValueEq [HasherTag] (state preState : ToyState) :
    (toyWrongBoxEq state 1).run (pureState preState)
      = toyRunBoxValueEqRhs state preState :=
  rfl

/-! ## The toy operation handler (§13.6)

The `operations` pyspec layout gives each handler records with two inputs,
the state and one operand. The toy fork answers with one operand
container and one action over the boxed state, so the layout's tests
drive a real handler instead of a `todo`. -/

/-- The toy operand container: one field, the amount. One field keeps
serialization trivial, the same single-operand shape the `operations`
layout models (§13.6). -/
structure ToyReq where
  /-- The amount the `.ok` face writes into the balance. -/
  amt : UInt64
  deriving Inhabited, SSZRepr

/-- The toy operation over the state and the operand: rejects with
`"zero"` when the amount is zero, and writes the amount into the balance
otherwise. -/
def toyOpApply [HasherTag] (r : ToyReq) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except String) Unit :=
  fun b => if r.amt == 0 then throw "zero" else .ok ((), pureState { b.view with bal := r.amt })

/-- The operation's `.runOk` face (§7.3, form 2). -/
theorem toyOpRunOk [HasherTag] (s : ToyState) :
    (toyOpApply { amt := 42 }).run (pureState s) = .ok ((), pureState { s with bal := 42 }) :=
  rfl

/-- The operation's `.runError` face (§7.3, form 4). -/
theorem toyOpRunError [HasherTag] (s : ToyState) :
    (toyOpApply { amt := 0 }).run (pureState s) = .error "zero" :=
  rfl

/-- The toy operation that ignores its operand and reads past the end of a
one-element table (§13.6): the `toyIndexMiss` shape over the `ToyReq`
operand. The read runs through `arrGetIdx`, so the reject is the genuine
`IndexError` carrying the index and the bound. The interface lifts it
through `ErrorConv IndexError StateTransitionError` to the state machine's
`outOfBounds`. The operations format's check must fail both scorings: the
caught set admits a post-less case's reject, so the driver answers a
flagged pass, and a post-carrying case fails on the reject itself. The
binder carries the underscore because the body reads no operand field. -/
def toyOpMiss [HasherTag] (_r : ToyReq) :
    StateT (SSZ.Box HasherTag.H ToyState) (Except IndexError) Unit :=
  fun b =>
    -- The `let` pins `arrGetIdx`'s monad, the same way `toyIndexMiss` does.
    let read : Except IndexError UInt64 := arrGetIdx #[b.view.bal] 5
    read.map (fun _ => ((), b))

/-- The miss operation's run: the read at index 5 of the one-element table
rejects with `IndexError.indexError 5 1`, whatever the operand carries. -/
theorem toyOpMissRun [HasherTag] (r : ToyReq) (s : ToyState) :
    (toyOpMiss r).run (pureState s) = .error (IndexError.indexError 5 1) :=
  rfl

/-- The miss operation's `runPure` reading: the same reject over the plain
state binder. -/
theorem toyOpMissPure [HasherTag] (r : ToyReq) (s : ToyState) :
    runPure (toyOpMiss r) s = .error (IndexError.indexError 5 1) :=
  rfl

end EthCLLib.TheoremVectors.Tests.ToyRun
