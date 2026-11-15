import EthCLLib.Spec
import EthCLLib.Spec.DroppedCheckedLint

/-!
# `EthCLLib.Tests.DroppedCheckedLint`: the dropped-expression linter prototype

The gate for the §4.3 dropped-expression hazard check
(`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md`, plan task 6.3). The module turns the
linter on and pins its verdicts with `#guard_msgs`, which makes the gate a build
check (`lake build EthCLLibTests`): a linter that stops flagging the §4.3 example,
or that starts flagging the allowed shapes, fails here.

`droppedFault` is the §4.3 example: `total` is a `let`-bound `Checked` value, the
`else` path returns without ever binding it, and the model returns `0` there where
the pyspec raises at the assignment. `droppedFaultLift` is the same shape one rung
up the lift (§4.4): the then path binds `total` through the error lift, the else
path drops it. The two `#guard_msgs` docstrings pin those warnings.

The silent cases, each a plain `--` comment (the `#guard_msgs` docstring slot is the
expectation, so the notes ride above as ordinary comments): `layoutSplit` is the
§4.3 allowance, an unbound sub-expression every path uses; `boundEverywhere` binds
with `←` where the pyspec assigns, the normal discipline; `deadBinding` never uses
the value at all, dead code and the core unused-variable linter's finding, not this
hazard.
-/

set_option linter.droppedChecked true

namespace EthCLLib.Tests.DroppedCheckedLint

open EthCLLib.Spec

/--
warning: EthCLLib.Tests.DroppedCheckedLint.droppedFault: 'let total' binds a `Checked` value that some return path never uses: the path returns without examining the fault, where the pyspec raises at the assignment (SPEC_ARITHMETIC.md §4.3, dropped expression)

Note: This linter can be disabled with `set_option linter.droppedChecked false`
-/
#guard_msgs (warning) in
def droppedFault (a b : CLUint64) (useIt : Bool) : Checked CLUint64 := do
  let total := a + b
  if useIt then total else pure 0

/--
warning: EthCLLib.Tests.DroppedCheckedLint.droppedFaultLift: 'let total' binds a `Checked` value that some return path never uses: the path returns without examining the fault, where the pyspec raises at the assignment (SPEC_ARITHMETIC.md §4.3, dropped expression)

Note: This linter can be disabled with `set_option linter.droppedChecked false`
-/
#guard_msgs (warning) in
def droppedFaultLift (a b : CLUint64) (useIt : Bool) :
    Except StateTransitionError CLUint64 := do
  let total := a + b
  if useIt then pure (← total) else pure 0

/--
warning: EthCLLib.Tests.DroppedCheckedLint.okCtorDropped: 'let total' binds a `Checked` value that some return path never uses: the path returns without examining the fault, where the pyspec raises at the assignment (SPEC_ARITHMETIC.md §4.3, dropped expression)

Note: This linter can be disabled with `set_option linter.droppedChecked false`
-/
#guard_msgs (warning) in
def okCtorDropped (a b : CLUint64) (useIt : Bool) : Checked CLUint64 := do
  let total := a + b
  if useIt then total else Except.ok 0

-- The known silence of the letFun form: the let binds a `StateT`-lifted `Checked`
-- action (§4.4), the `else` path returns without running it. The elaborated value
-- is `have act := liftM (a + b)`, and `liftM`'s inferred type still carries the
-- monad metavariable after instantiation, so the syntactic filter stays silent.
-- The `letE` route (an annotated term let, or the fork bodies' `Checked do`
-- blocks, where the fault rides the plain `Checked` type) is covered above.
#guard_msgs (warning) in
def stDroppedSilent (a b : CLUint64) (useIt : Bool) :
    StateT Unit (Except ArithFault) CLUint64 := do
  let act : StateT Unit (Except ArithFault) CLUint64 := do
    let x ← a + b
    pure x
  if useIt then act else pure 0

-- The §4.3 allowance: the layout split, every path uses the unbound product.
-- Expected: no warning.
#guard_msgs (warning) in
def layoutSplit (a b c : CLUint64) : Checked CLUint64 :=
  let product := a * b
  product / c

-- The normal discipline: bound where the pyspec assigns. Expected: no warning.
#guard_msgs (warning) in
def boundEverywhere (a b : CLUint64) : Checked CLUint64 := do
  let total ← a + b
  pure total

-- Dead code, not the hazard: no path uses it. Expected: no warning.
#guard_msgs (warning) in
def deadBinding (a b : CLUint64) : Checked CLUint64 := do
  let _total := a + b
  pure 0

end EthCLLib.Tests.DroppedCheckedLint
