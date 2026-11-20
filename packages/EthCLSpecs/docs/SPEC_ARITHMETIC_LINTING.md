# Spec arithmetic linting, deferred

Status: deferred until after the arithmetic transition. This document records future
work and does not schedule implementation as part of that transition.

[SPEC_ARITHMETIC.md](SPEC_ARITHMETIC.md) defines the authoring rules. In particular,
fork bodies bind local checked computations immediately and preserve short circuits.
Authors follow those rules during the transition through source review and behavior
tests. The later linter adds automated enforcement.

## 1. Goal and scope

Detect authored local bindings that retain an unexamined checked computation where a
fork body must bind it immediately. Cover `forkdef` bodies and their inherited replay.
Allow a direct checked result at a function's return and the documented framework
combinators that compose checked values with fault-propagation laws.

Prefer a narrow check of the agreed authoring rule. A general path analysis is a
separate problem. A use of a variable does not prove that a computation examined its
fault. Short-circuit placement still needs source review and behavior tests.

This work must not change arithmetic semantics, silently insert binds, move a bind
across a branch, or replace the safe construction rules in the arithmetic types.

## 2. Evidence from the spike

Source: `specs-arithmetics-spike` at `ff520aa5003804601bc72985f8429cce676d1b5b`,
`packages/EthCLLib/EthCLLib/Spec/DroppedCheckedLint.lean` and its tests.
The local Stage 6 report and review give the experiment history.

The prototype's documented limitations include:

- It is off by default. A successful build can therefore omit the check entirely.
- Its type filter can miss aliases and some lifted computations.
- Opaque helpers can hide a path that drops a fault.
- A use inside a loop body can count as a use even when the loop runs zero times.
- Its analysis tracks references, which can differ from binding and propagating a fault.

Two implementation lessons also matter:

- A pure `let` in do-notation can elaborate as `letFun` with a continuation, rather
  than `Expr.letE`. Recovering the value's type may require the local context.
- User modules register linters with `initialize`. The spike's `builtin_initialize`
  attempt left the linter absent when imported.

The production design must account for these facts. The prototype is a reference
experiment, and its passing fixtures do not establish complete enforcement.

## 3. Later plan

Start this work only after the arithmetic transition is complete and a follow-up
explicitly selects it. All tasks below are pending.

### L0: specify the accepted authoring forms

- [ ] Enumerate local checked bindings, direct returns, nested do-blocks, matches,
  loops, and framework-combinator uses in the completed migration.
- [ ] Define exactly which forms the checker rejects and where it reports the error.
- [ ] Choose the check location using real elaborated examples: the authoring DSL,
  elaboration information, or a linter over declarations.
- [ ] Document framework exceptions and any unsupported forms without broad exemptions.

**Done when:** accepted and rejected examples define a precise, reviewable contract.

### L1: implement a narrow checker

- [ ] Detect immediate-bind violations without claiming complete path analysis.
- [ ] Handle both `letE` and `letFun`, aliases, local contexts, and supported monad lifts.
- [ ] Apply the rule to inherited fork declarations as well as new declarations.
- [ ] Keep the checker independent of the arithmetic semantic core and its proof imports.

**Done when:** the checker diagnoses the specified forms at their source locations.

### L2: test failures and allowed forms

- [ ] Test a dropped fault on one branch, a wholly unused computation, an empty loop,
  an early return, and a value passed to an opaque helper.
- [ ] Test nested binds, aliases, state/store lifts, and the inherited replay path.
- [ ] Test allowed immediate binds, direct checked returns, and framework combinators.
- [ ] Test registration through an importing module with a deliberately bad declaration.
- [ ] Measure checker costs separately from the arithmetic implementation's baseline.

**Done when:** rejected and accepted fixtures behave as specified, and costs are recorded.

### L3: enable enforcement

- [ ] Run the checker over all consensus-spec code and review each finding.
- [ ] Enable it for the intended authored declarations and make violations fail CI.
- [ ] Verify the CI invocation actually rejects the importing-module failure fixture.
- [ ] Document how contributors run it and what remains a source-review obligation.

**Done when:** the automated check enforces its stated rule across all intended forks.
Update this document's status when that separate work completes.
