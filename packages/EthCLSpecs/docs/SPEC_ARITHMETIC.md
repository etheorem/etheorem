# Spec arithmetic

The required arithmetic behavior and authoring rules for all consensus-spec code in
`EthCLSpecs`, supported by the arithmetic layer in `EthCLLib`.

This document defines the implemented arithmetic contract. It governs future additions
and spec re-pins. Sections 1 to 3 describe the pinned behavior; Sections 4 to 7 prescribe
the implementation and its use. The temporary [SPEC_ARITHMETIC_PLAN.md](SPEC_ARITHMETIC_PLAN.md)
records the transition to this contract; the final acceptance change removes it.

Pin: `v1.7.0-beta.4`, with `eth-ssz-specs` 0.1.0 as the pyspec's integer library. Line citations
(`<file>.md:NN`) resolve under `specs/` in `ethereum/consensus-specs` at the pin. Every re-pin
re-checks this document with the commands in Section 8.

## 1. The rule

For every modeled pyspec function and every input:

1. The Lean function raises exactly when the pyspec function raises.
2. When neither raises, the two results are equal.

At the consensus boundary, the rule compares success, failure, and successful results.
The runner has a further contract: its caught-exception sets distinguish range faults,
zero divisors, index faults, and assertions. Preserve those distinctions through typed
errors wherever the runner observes them. Diagnostic text does not determine behavior.

The failure point may move only when the caller observes the same outcome. This requires
discarding failed state changes, preserving the runner's exception classification, and
preserving any observable effects. Keep the pyspec's evaluation order by default.

A Lean helper with no pyspec twin is free in its own behaviour. The modeled functions that call
it must still hold the rule.

The rule covers every raise. This document covers the arithmetic sources: range, zero divisors,
and casts. Asserts and index reads follow the error model, `FRAMEWORK_ARCHITECTURE.md` §6.

## 2. Why the pyspec raises

The spec text makes a raise part of validity. A state transition that triggers an unhandled
exception is invalid, and a transition that causes a `Uint64` overflow or underflow is invalid
too (`phase0/beacon-chain.md:1815-1819`). Gloas repeats both sentences for payloads
(`gloas/beacon-chain.md:1590-1603`). Fork choice says the same of its handlers, and an invalid
call must leave `store` unchanged (`phase0/fork-choice.md:97-99`).

The functions of the built Heze module hold 177 `assert` statements, and the module holds no
`try` block. Thirteen more asserts run at module level and check the configuration at import.
Every raise ends the call that started it. The test wrappers still catch selected exception
classes, so their classification remains part of the runner contract in Section 1.

## 3. What the pyspec does

### 3.1 Two integer kinds

The pyspec has two kinds of integer, and each site uses one of them.

- **Checked.** `Uint8`, `Uint16`, `Uint32`, `Uint64`, `Uint128`, `Uint256`, and their
  subclasses (`Slot`, `Epoch`, `Gwei`, `ValidatorIndex`, and the others). Every operator
  computes in Python's unbounded `int`, then tests the result against `[0, 2**BITS - 1]`. A
  result outside the range raises. No operator wraps.
- **Plain.** Python's `int`, unbounded and signed. It comes from `len`, from a `range` or
  `enumerate` variable, from a literal, from `sum` of an empty sequence, and from
  `int.from_bytes`. Arithmetic on two plain values never raises on range.

An operator with one checked operand and one plain operand gives a checked result. The side
the plain operand is on makes no difference.

`int(x)`, `-x`, `~x`, and `/` return plain values. The in-scope text uses `~` once
(`validator_index & ~BUILDER_INDEX_FLAG`) and never uses `/`.

### 3.2 Checked operators

Each row is a result from the built Fulu module at the pin. `MAX` is `2**64 - 1`.

| Expression | Result |
|---|---|
| `Uint64(MAX) + 1`, `1 + Uint64(MAX)` | raises |
| `Uint64(0) - 1`, `0 - Uint64(1)` | raises |
| `Uint64(2**63) * 2` | raises |
| `Uint64(1) << 64`, `Uint64(2) ** 64`, `2 ** Uint64(64)` | raises |
| `Uint64(1) // Uint64(0)`, `Uint64(1) % Uint64(0)` | raises (`ZeroDivisionError`) |
| `sum([Gwei(MAX), Gwei(1)])` | raises, inside the `sum` |
| `state.balances[0] += 1` at `MAX` | raises |
| `sum([])` | `0`, a plain `int` |
| `max(Gwei(1), Uint64(5))` | `Uint64(5)`, the operand itself |
| `int(Uint64(MAX)) + 1` | `2**64`, a plain `int` |

Three properties follow from the mechanism.

- **The test runs per operation.** `a * b // c` raises when `a * b` passes `2**64`, even if the
  quotient fits.
- **Evaluation is lazy.** Only the executed branch is tested. `a - b if a > b else a - a` never
  raises.
- **Two checked operands of the same width divide safely when the divisor is nonzero.**
  Mixed signed or unbounded operands still need the result range test.

### 3.3 Casts and stores

| Expression | Result |
|---|---|
| `Uint64(2**64)`, `Uint64(-1)` | raises |
| `Uint8(Uint64(300))` | raises |
| `Slot(epoch)` | a `Slot` with the same value |
| `state.balances[0] = 2**64` | raises |
| `checkpoint.epoch = 2**64` | raises |
| `state.balances[7]` on a shorter list | raises (`IndexError`) |
| `append` on a full list | raises |
| `bytes_to_uint64(b)` for up to 8 bytes | always in range |

A cast is a range test. So is a store into a container field or a list element.

### 3.4 Unit types

`Slot`, `Epoch`, `Gwei`, and `ValidatorIndex` are distinct subclasses of `Uint64`.

- `Slot(1) + Epoch(1)` and `Slot(1) < Epoch(2)` raise `TypeError`.
- A unit combined with a bare `Uint64` or a plain `int` keeps the unit.
- `SLOTS_PER_EPOCH` has type `Slot`, so the text writes `Slot(epoch) * SLOTS_PER_EPOCH`.

A unit error depends on the code path alone. It is a rule for the spec authors, and no input
value can trigger it in a body that upstream tests pass. The rule in Section 1 asks nothing of
the model here.

### 3.5 Guards the spec text writes out

The text never depends on modular arithmetic. Where a raise would be wrong, it states the guard.

| Guard | Sites |
|---|---|
| `saturating_sub(a, b)`, floors at zero (`phase0/beacon-chain.md:1035-1042`) | `decrease_balance`, `get_previous_epoch`, the inactivity scores, the builder balance sweep; 13 call sites in Heze |
| Add before subtract | `get_seed` (`phase0/beacon-chain.md:1502`) |
| Divide by `EFFECTIVE_BALANCE_INCREMENT` first | `process_slashings`, the reward and penalty code (`phase0/beacon-chain.md:2061`, `:2257`, `electra/beacon-chain.md:1089`) |
| Special case at the maximum | `integer_squareroot` (`phase0/beacon-chain.md:993`), `seconds_to_milliseconds` (`phase0/fork-choice.md:550-557`) |
| Explicit reset to zero at the maximum | `get_custody_groups` (`fulu/das-core.md:220-224`) |
| Floor against a zero divisor | `get_total_balance` returns at least `EFFECTIVE_BALANCE_INCREMENT` |

Two functions accept the raise in their own text. `get_total_balance` is "safe up to ~10B ETH,
after which this overflows" (`phase0/beacon-chain.md:1563`). `compute_time_at_slot` is "unsafe
with respect to overflows and underflows" (`phase0/beacon-chain.md:1289`).

### 3.6 What the vectors test

One upstream test expects a range raise: `invalid_large_withdrawable_epoch`
(`test/phase0/epoch_processing/test_process_registry_updates.py:409-434`). The shared helper
`expect_assertion_error` catches `AssertionError` and `IndexError` only (`test/context.py:451`),
so no block-level `invalid_*` vector can depend on a range raise.

Conformance therefore cannot hold the model to the rule. The model must hold it by construction.

### 3.7 Indexing

Any integer indexes a list. The index has no unit test: `state.balances[Gwei(1)]` returns an
element.

| Index into a list of three elements | Result |
|---|---|
| `ValidatorIndex(1)`, `Uint8(1)`, plain `1` | the element |
| `Uint64(3)` | raises (`IndexError`) |
| plain `-1` | the last element |
| plain `-4` | raises (`IndexError`) |
| a write at `Uint64(3)` | raises (`IndexError`) |

A negative plain index counts from the end. SSZ lists, SSZ vectors, and Python lists agree on
all five rows. The built Heze module has two negative literal indices, both `withdrawals[-1]`.

## 4. The design

The model gives each pyspec integer kind its own Lean type. The operators of those types raise
where the pyspec raises, so a fork body writes the same expression the pyspec writes.

### 4.1 The types

| pyspec | Lean | Role |
|---|---|---|
| `Uint64` and its subclasses | `CLUint64` | A `structure` over `UInt64`. No core operator instance applies to it. |
| `int` | `CLInt` | A `structure` over `Int`. Unbounded and signed. |
| a raise | `Checked α` | `Except ArithFault α`: a value or a fault. The type of an arithmetic expression. |
| a range fault or a zero divisor | `ArithFault` | A typed cause, `.range` or `.zeroDivision`, with the operator, width, and signed operands available for diagnosis. A negative shift count is a `.range` fault. |

`Slot`, `Epoch`, `Gwei`, `ValidatorIndex`, and the other unsigned 64-bit consensus units
are abbreviations of `CLUint64`. Unit aliases share the checked operators. `CLUint64`
has the `SSZRepr` instance of `uint64`, so fields retain their bytes and roots.
`ParticipationFlags` uses the corresponding checked 8-bit type.

Keep the semantic core separate from operator elaboration, indexing, and SSZ instances.
Proofs import the semantic core without requiring authoring elaborators. The 64-bit and
8-bit types use native-backed wrappers. Share laws and instance generation where useful.
Every width with a consensus arithmetic consumer must have an explicit operation
matrix and conversion laws. The implemented arithmetic widths are 64 and 8 bits.
The 32-bit uses are codec conversions; the 256-bit uses are data representations.
Those data-only widths retain their codec rules. An arithmetic consumer at either
width requires a checked surface and its operation matrix before use.

Use exact type names in the Lean API and its documentation. Python `int` is the source
type; `CLInt` is its spec-facing Lean model; Lean `Int` is the underlying signed type.
Lean `Nat` is the underlying nonnegative type. Conversion names identify the actual
result: `toCLInt` returns `CLInt`, `toPlainNat` returns `Nat`, and `toPlainInt` returns
Lean `Int`. A checked conversion to `CLUint64` is named `toCLUint64?`.

### 4.2 Operator result types

`U` is `CLUint64` and `I` is `CLInt`. A `Checked` operand is an expression that is not bound
yet.

| Operands | Operators | Result | Raises |
|---|---|---|---|
| `U`, `U` | `+ - *` | `Checked U` | outside `[0, 2^64)` |
| `U`, `U` | `/ %` | `Checked U` | zero divisor |
| `I`, `I` | `+ - *` | `I` | never |
| `I`, `I` | `/ %` | `Checked I` | zero divisor |
| `I`, `Nat` or Lean `Int` in either order | `/ %` | `Checked I` | zero divisor |
| `I`, `U` in either order | `+ - * / %` | `Checked U` | outside `[0, 2^64)`, or zero divisor |
| `Nat`, `U` in either order | `+ - * / %` | `Checked U` | outside `[0, 2^64)`, or zero divisor |
| `Nat`, `I` in either order | `+ - *` | `I`, the `Nat` coerces | never |
| `Nat`, `Nat` | all | core Lean | total, but subtraction and zero division differ from Python |
| supported numeric pairs with a `Checked` operand | same | `Checked` of the same type | the operand's fault, then the operator's |

The other operators use the Lean operator names. Python's `**` is `^`, `<<` is `<<<`, `>>` is
`>>>`, and `&`, `|`, `^` are `&&&`, `|||`, `^^^`.

| Operands | Operators | Result | Raises |
|---|---|---|---|
| `U`, `U` | `&&&`, `\|\|\|`, `^^^` | `U` | never |
| `U`, `Nat` | `>>>` | `U` | never; zero for a count of 64 or more |
| `Nat`, `U` | `>>>` | `Checked U` | outside `[0, 2^64)` |
| `U`, `Nat` | `<<<` | `Checked U` | outside `[0, 2^64)` |
| `U`, `Nat`; `Nat`, `U`; Lean `Int`, `U` | `^` | `Checked U` | outside `[0, 2^64)` |
| `I`, `U` in either order | `&&&` | `Checked U` | outside `[0, 2^64)` |
| `U`, `PositiveDivisor` | `/ %` | `U` | never |
| `CLUint8`, `CLUint8` | `&&&`, `\|\|\|` | `CLUint8` | never |

Python's `~x` on a checked value is `x.invert`, a `CLInt`. `CLUint8.addFlag` and
`CLUint8.hasFlag` return `Checked`, because the mask `2**flag_index` raises past index 7.

Three properties follow.

- **Each step is tested.** In `a * b / c` the product raises when it passes `2^64`, even if the
  quotient fits.
- **Division floors as Python does.** `CLInt` uses `Int.fdiv` and `Int.fmod`.
- **A plain expression needs no bind until it divides.** `len xs + len ys * 2 - 1` has type
  `CLInt`. `(len xs + 1) / len ys` has type `Checked CLInt`.

The mixed route computes on the original operands, then checks the result. Do not narrow
the plain operand first. For example, `Uint64(0) * (2**64)` succeeds with zero.

Use `Nat` for structural lengths, termination measures, and positions already checked by
the framework. Use `CLInt` for Python plain-integer formulas. An operation between two
`Nat` values does not become Python arithmetic because a later operand is checked.
Record the numeric kind of constants from the pinned pyspec. Checked constants stay
checked in executable formulas, even when their values also serve as type-level sizes.

#### Total operations with a proof

`PositiveDivisor` carries a natural divisor and a proof that it is positive. Division
and modulo of a bound `CLUint64` value by that wrapper return `CLUint64` directly.
Both results fit because they are at most the dividend. A named constant view such as
`Const.slotsPerEpochDiv` carries the proof once, so `computeEpochAtSlot` can remain pure.

Keep the ordinary divisor routes checked. Do not add overlapping instances selected by
a hidden `NeZero` premise. Give the wrapper no automatic literal instance or coercion.
Bind a checked dividend before using the total route:

```lean
let product ← a * b
let quotient := product / Const.slotsPerEpochDiv
```

The wrapper must refer to the original constant, with no repeated value. Tier inheritance
must carry its proof through Fulu, Gloas, and Heze, including child overrides.
A runtime configuration value uses checked division unless its accepted domain supplies
the positivity proof. Arbitrary configurations retain their checked behavior. Shipped
preset values alone cannot justify a total operation over a generic configuration.

Total same-width bitwise operations and right shifts by nonnegative counts also have
range proofs. Keep their routes distinct from mixed signed operations that can raise.
Other arithmetic retains its `Checked` result even when a particular call cannot fail.

### 4.3 Binding

An arithmetic expression that can fail has a `Checked` result. A `do` block binds it
with `←`, once for the whole expression.

```python
reward_numerator = base_reward * weight * unslashed_participating_increments
rewards[index] += reward_numerator // (active_increments * WEIGHT_DENOMINATOR)
```

`getFlagIndexDeltas` in `Fulu/EpochProcessing.lean` writes these lines:

```lean
let rewardNumerator ← baseReward * weight * unslashedIncrements
-- `rewards[index] += …` reads the element before it forms the right side.
let previousReward ← liftErr (getAt rewards vi)
let rewardDelta ← rewardNumerator / (activeIncrements * Const.weightDenominator)
let updatedReward ← previousReward + rewardDelta
rewards ← liftErr (setAt rewards vi updatedReward)
```

A bind is required in two places:

- **Where the pyspec assigns a fallible computation.** The corresponding `let` takes `←`.
- **Where a bound value is needed.** A comparison, a branch condition, a store, and an argument
  typed `CLUint64` all take a value: `if (← a + b) > c`.

An unbound `Checked` value can contain a fault that no code has examined. If one path never uses it, the
model returns a value where the pyspec raises:

```lean
let total := a + b                    -- unbound
if useIt then total else return 0     -- the `else` path drops the fault
```

In fork bodies, bind every local checked computation immediately. A layout split uses
another `let x ← …`. Return a `Checked` expression directly only when it is the function's
result. Framework combinators may compose checked values internally and must prove their
fault-propagation laws.

Split a checked conversion from the arithmetic that follows it:

```lean
let amount ← CLUint64.ofNat? count
let total ← amount + delta
```

A cast must appear here only when the pyspec performs that cast; a mixed operator does
not imply one. The separate binds give each expression an explicit value boundary.

The pyspec's `and` and `or` short-circuit. A second operand that contains arithmetic must be
bound inside its own branch, so it is formed only when the pyspec forms it.

Authors and reviewers check bind placement against the source, including empty loops,
early returns, and inherited declarations. Behavior pins cover dropped faults and
short-circuit cases. A reference to a checked value does not establish that a bind
examined it.

### 4.4 The lift and the signatures

One instance lets `←` take an arithmetic expression in any monad whose error accepts a
`StateTransitionError`:

```lean
instance {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] : MonadLift (Except ArithFault) m
```

The lift preserves arithmetic causes in the state and store error channels. Typed
payloads carry every distinction the runner's caught sets observe. A range error and a
zero divisor need distinct classification under a wrapper that catches `ValueError`
alone. Never recover that distinction by parsing diagnostic text.

A function's result type states whether it can raise:

| A function that | Returns |
|---|---|
| uses only operations proved total over its accepted inputs | `α` directly |
| does arithmetic only | `Checked α` |
| also reads an index or asserts | `Except StateTransitionError α` |
| reads or writes the state | `StateTransition α` |

`Checked` is a monad, so a pure loop keeps its `for` and its `let mut`. A caller binds a
`Checked` function like any other action.

### 4.5 Conversions and literals

| pyspec | Lean | Raises |
|---|---|---|
| `Uint64(n)` from Python `int`, modeled by `n : CLInt` | `n.toCLUint64? : Checked CLUint64` | negative, or past `2^64 - 1` |
| `int(x)` for `x : CLUint64` | `x.toCLInt : CLInt` | never |
| `len(xs)` | `len xs`, a `CLInt` | never |
| a plain literal | an unbounded literal until an explicit checked construction | never |
| a literal typed as a checked width | a bound-checked literal | compilation fails if out of range |
| `max(a, b)`, `min(a, b)` of the same numeric kind | `max a b`, `min a b` | never |
| `saturating_sub(a, b)` | `a.saturatingSub b` | never |
| `sum(xs)` | `xs.foldlM (fun acc x => acc + x) (0 : Gwei)`, with the element type's zero | as `+` |
| a store into a checked field | checked conversion if needed, then the store | range failure at conversion; index failures remain separate |

`x.toCLInt` models Python's `int(x)` and returns `CLInt`. For `x : CLUint64`,
`x.toPlainNat` exposes its value as a Lean `Nat`, for proofs and framework boundaries.
For `n : CLInt`, `n.toPlainInt` exposes its signed value as a Lean `Int`.
Each executable use of these underlying-type conversions must cite the conversion or
bound that permits it. Indexing goes
through the size-aware interface in Section 4.6; a negative index must retain its sign.

Keep the checked constructors private. Supply checked conversions from Lean `Nat`,
Lean `Int`, `CLInt`, and other widths, plus proof-carrying construction from a value
with a range proof. Namespace-qualified constructors such as `CLUint64.ofNat?` name
their result through the namespace and their input through the method name.
Raw machine-word wrapping belongs in the framework's codec and proved-total operations.
A public trusted constructor must never repair an operator elaboration error.
`trustedOfUInt64 (UInt64.ofNat n)` loses overflow information before the wrapper sees it.
Audit raw projections and trusted constructors as well as `toPlainNat` and `toPlainInt`.

Literal safety belongs in the `OfNat` construction itself. The `CLUint64` instance carries
the premise `NeZero (2^64 - n)`, and the `CLUint8` instance carries `NeZero (256 - n)`.
Core instance search discharges the premise only for an in-range `n`, so an out-of-range
instance cannot be synthesized. A scoped elaborator may improve diagnostics but cannot be
the only gate.
Test direct `OfNat` use, reducible and non-reducible aliases, delayed expected types,
and a module that never opens `EthCLLib.Spec`.

Mixed `min`/`max` select an operand and retain its numeric kind in Python. `sum([])`
starts as a plain zero. Audit those sites before choosing a homogeneous Lean encoding.
The fork bodies start each checked `sum` at the checked zero of the element type. The
pyspec's plain `0` meets a checked element at the first add, so both forms raise at the
same element; only the kind of an empty sum differs.
Any normalization must preserve subsequent raises, including the first addition of a
nonempty sum. Do not cast a large plain operand merely to satisfy an instance.

### 4.6 Indexing

An index class in `EthCLLib` says how an integer type names a position:

```lean
class ToIndex (ι : Type) where
  pos? : ι → Nat → Option Nat      -- `none` where the pyspec raises `IndexError`
  idx? : ι → Nat                   -- the rejected index, for diagnostics only
```

It has instances for `Nat`, `CLUint64`, and `CLInt`. The `CLInt` instance counts a negative
index from the end. Its `idx?` gives `0` for a negative index, because the `IndexError`
payload holds a `Nat`. The pure read `getAt`, the pure write `setAt`, and the raising read
`sszGetIdx` take any index type with an instance. `SizzLean` keeps `Nat` indices.

The raising read stays in the ambient monad. Its failure remains `IndexError`-shaped,
mapped to `outOfBounds` by the error conversion.

`getAt` returns `Except IndexError α`. A state-free helper that also performs arithmetic
or assertions returns `Except StateTransitionError α` and lifts the read with `liftErr`.
Apply the same rule to arrays, SSZ collections, bit lists, and writes. Moving an index
fault into a pure helper does not change its exception class. A pure indexed read must
preserve that typed error.

Test `-1`, `-size`, an index below `-size`, `size`, and empty collections for reads and
writes. Keep available index and bound information in diagnostics. Do not use a default
value, discard the sign with `Int.toNat`, or silently map an invalid index to zero.

### 4.7 Operator elaboration

Core Lean's operator elaborator reads the expected type. Under `let x ← a / b + 1` that type is
the transition monad. No operand type compares with a monad, so core skips the step that types
a literal operand, and the instance search then fails.

An explicit `(expression : Checked _)` ascription supplies the result type without
changing the operands. This is the supported baseline when ordinary inference fails.
A scoped elaborator may remove ascriptions when it preserves the same elaborated
behavior. Keep retries bounded. Unknown operand types require postponement rather than
premature literal defaults. The authoring surface must handle:

- Literals on either side, non-literal `Nat` and `CLInt` operands, nested expressions,
  and nested binds.
- Lambda binders whose types arrive from later arguments, whole-definition results,
  and `else if` conditions.
- State-free `Checked`, state, store, and inherited fork contexts.
- Unchanged elaborated terms for unrelated `Nat`, `Int`, and `UInt64` arithmetic.
- Errors reported at the offending expression, including a prior do-bound operand
  combined with a non-literal `Nat`.

Never change operand types to make elaboration succeed. Keep the `Checked` ascription
available when automatic elaboration is incomplete. Record cold and incremental build
costs when changing this layer. Correct behavior is required at any compilation cost.

### 4.8 SSZ representation and cached updates

Every layer that decides basic-element packing must inspect the `SSZRepr` shape.
Checked wrappers with `.uintN` shape have the same packing as the corresponding SSZ
integer. A Lean type-name whitelist is insufficient. An unresolved shape must produce
a clear failure or use a proved-correct generic route; it must never guess composite.

Regression tests must use a custom wrapper independent of `EthCLLib`.
Cover packed lists and vectors, chunk boundaries, repeated indexed writes, and a root
cached before the write. Compare the updated
cached root with fresh merkleization of the plain value. Check serialization separately.

Codec equivalence alone cannot establish cache correctness. A cached root must describe
the updated value after every supported indexed write.

### 4.9 Proof interface

Provide success conditions and returned-value laws for each primitive.
Provide chain lemmas that expose every intermediate range test, plus laws for casts,
positive divisors, lifts, and index conversion. Keep a focused arithmetic simp set.
Move reusable checked-fold lemmas into the framework before duplicating them across forks.

A transition characterization states successful results and failure behavior through
`runPure` over a plain state. An `.ok` hypothesis must name a real arithmetic obligation. Keep a
separate characterization of failure when a successful-case theorem needs that hypothesis.
State theorems about each fork's own re-elaborated declarations.

Preserve characterization tags and audit axioms on repaired theorems. General arithmetic
laws need kernel proofs. Handle an impossible `Except` equality with constructor reasoning
or `exfalso` before arithmetic tactics.
Regenerate coverage after proof changes; raw theorem counts alone do not show preservation.

## 5. Rationale

### 5.1 The checked kind, operation by operation

Each cell says what the operation does at the edge of the range. The first column is the
behaviour to match.

| Operation | pyspec `Uint64` | Lean `UInt64` | `CLUint64` |
|---|---|---|---|
| `a + b` past the maximum | raises | wraps modulo `2^64` | raises |
| `a - b` below zero | raises | wraps modulo `2^64` | raises |
| `a * b` past the maximum | raises | wraps modulo `2^64` | raises |
| `a // 0`, `a % 0` | raises | `0`, `a` | raises |
| `a ** n` past the maximum | raises | wraps modulo `2^64` | checked power |
| `a << n` past the maximum | raises | drops the high bits; shift taken modulo 64 | checked left shift |
| `a >> n`, nonnegative count | in range; count is unbounded | count taken modulo 64 | total; returns zero for `n ≥ 64` |
| same-width bitwise operators | in range | in range | total |
| a comparison | a `bool` | a `Bool` | a `Bool` |
| a cast from an out-of-range `int` | raises | `UInt64.ofNat` wraps | raises |
| the operator on a plain `int` operand | checked, result is `Uint64` | no instance; `UInt64.ofNat` wraps | checked, result is `CLUint64` |
| the result of an expression | a `Uint64` | a `UInt64` | a `Checked CLUint64` |

Core `UInt64` differs from the pyspec in every row that can raise. No setting changes that: the
operators are total functions, and a total function has no way to raise.

Signed counts need their own behavior: a negative shift count raises. A plain left operand followed
by a checked right-shift count still requires a result range test. For example,
`(2**64) >> Uint64(0)` raises. Do not generalize the total unsigned route to that case.

Use early range decisions for checked power and left shift. Avoid constructing enormous
unbounded intermediates to discover an overflow. Prove those decisions against the
unbounded definition, including zero bases and `0 ** 0`. Supply signed and mixed-width
operations wherever the consensus-spec code uses them.

### 5.2 The plain kind, operation by operation

| Operation | pyspec `int` | Lean `Nat` | Lean `Int` | `CLInt` |
|---|---|---|---|---|
| `a + b`, `a * b` | unbounded | unbounded | unbounded | unbounded |
| `7 - 9` | `-2` | `0` | `-2` | `-2` |
| `-7 // 2`, `-7 % 2` | `-4`, `1` | no negative values | `-4`, `1` | `-4`, `1` |
| `7 // -2`, `7 % -2` | `-4`, `-1` | no negative values | `-3`, `1` | `-4`, `-1` |
| `7 // 0`, `7 % 0` | raises | `0`, `7` | `0`, `7` | raises |
| `-5 >> 1` | `-3` | no negative values | `-3` | `-3` |
| used as an index | yes; negative counts from the end | yes | no; needs `Int.toNat`, which maps a negative number to `0` | yes, through `ToIndex` |
| the operator on a `Uint64` operand | checked, result is `Uint64` | none in core | none in core | checked, result is `CLUint64` |

`Nat` fails on subtraction and on a zero divisor. `Int` fails on a zero divisor and on a
negative divisor when using core Euclidean division. `Int.fdiv` and `Int.fmod` supply the
flooring behavior; `CLInt` adds the zero check and the signed indexing interface.

### 5.3 Why operators, when named helpers exist

Named checked helpers can implement the same semantics. Three reasons favor an operator
surface on checked types.

- **The code reads as the pyspec.** A reviewer compares `a * b / c` with `a * b // c` at a
  glance. `checkedDiv (← checkedMul a b "…") c "…"` needs a second reading.
- **The type enforces the rule.** A helper is a choice the author makes at each site, and a
  missed site compiles. With `CLUint64`, the wrapping `+` does not exist.
- **Vectors have sparse arithmetic coverage.** The type boundary, operator laws, and targeted
  pins cover failures absent from the upstream vectors.

### 5.4 Why a new type, when scoped instances on `UInt64` exist

An `abbrev` of `UInt64` is definitionally equal to `UInt64`. It retains the raw operator,
literal, and conversion instances. Instance search cannot distinguish the alias from
the raw type. A high-priority scoped checked `HAdd` can handle `a + b` while `a + 1`
still resolves to wrapping arithmetic. Oversized literals also retain the raw wrapping
instance, and closing the scope restores the raw operators.

Changing a default instance can affect unrelated arithmetic in importers. A custom
syntax layer would need to prevent every raw route and preserve fork replay behavior.
An abbreviation with scoped instances alone therefore cannot provide this contract.
A distinct type provides the required operator boundary in its signatures.

### 5.5 Why `CLInt`, when `Nat` fits most sites

Many plain integers in the spec are nonnegative sizes, counters, and indices.
`CLInt` is chosen for two reasons.

- **The operators stay the pyspec's.** With `Nat`, a zero divisor needs a named helper, and
  `(last + 1) % len(validators)` becomes `checkedMod (last + 1) validators.size`. With `CLInt`
  it is `(last + 1) % len validators`.
- **A negative intermediate is represented.** `Nat` floors `7 - 9` at zero with no error.

Measure instance synthesis cost and generate only a documented matrix of operand pairs.
Generating instances does not establish their laws.

Lean's `Nat` remains useful for structural work. Its use for a preset constant or loop
variable requires the numeric-kind audit in Section 4.2. A fork body writes `len xs - 1`
when the source is a Python plain-integer subtraction.

### 5.6 Why three small restrictions

- **No `default_instance` on any operator.** The attribute is global (Section 5.4). Without it
  the authoring layer must resolve literals through the documented operand matrix.
- **No coercion from `CLUint64` to `Nat`.** Lean's operator elaborator would use it to turn
  `a + n`, with `n : Nat`, into unchecked `Nat` arithmetic.
- **An explicit conversion to `Nat`.** The name `toPlainNat` makes unchecked arithmetic
  easy to search for. It supplies no range proof. Review each executable use, including
  equivalents written through raw projections or machine-word conversions.

### 5.7 Why the index class sits in `EthCLLib`

`SizzLean` could own the class, and its path forms `sszGet state f[i]` could then take a checked
index. Those forms exist to hide the state box and to drive the cached tree update. A state
held as a plain value does not need them: a read is a projection and a write is a structure
update. `sszGetIdx` is a function in `EthCLLib` with no reference to the box, so the class
belongs beside it.

## 6. What the rule allows and forbids

The rule fixes when the model raises. It leaves the form of the test open.

Allowed:

- **One outer arithmetic error arm with a typed cause.** Its mapping must preserve the
  runner's caught-exception distinctions.
- **A test before the operation.** `seconds_to_milliseconds` compares against `UINT64_MAX // 1000`
  first, and the product then cannot leave the range.
- **A raw operator behind a proof.** An index reduced modulo a positive preset length needs no
  test. The site must carry the proof, as `vmodGet` does through `ValidModulus`.

Forbidden:

- **A `Nat` intermediate where the pyspec holds a checked value.** In `a * b // c` the product
  can pass `2^64` while the quotient fits. `a.toPlainNat * b.toPlainNat / c.toPlainNat` hides
  that raise.
- **A default on a zero divisor.** `x % 0` raises in the pyspec, and a helper that returns `0`
  breaks the rule.
- **An unbound expression that a path drops** (Section 4.3).
- **A bind above the branch that uses it.** The model then raises on a path where the pyspec
  computes nothing.
- **`xs[i]!` where the pyspec can raise.** That form returns a default on a bad index.
- **An unchecked literal instance behind a scoped check.** Every construction route must
  preserve the value, including modules that never open the authoring namespace.
- **A trusted conversion used to fix elaboration.** Keep the operands and add an explicit
  result ascription, or fix the elaborator.
- **A default-zero result for an invalid configuration.** Either reject it at a documented
  configuration boundary or preserve the operation's raise.
- **A passing vector count as the only correctness criterion.** Compare case identities,
  outcomes, skips, exception classification, and successful state results.

## 7. Rules for future additions

These rules apply to new functions, inherited bodies, overrides, containers, constants,
and configuration fields throughout `EthCLSpecs`.

1. **Identify the source numeric kind.** Read the pinned pyspec declaration and its
   operators. Distinguish checked values, Python plain integers, and Lean structural
   counts. A small constant value does not establish its numeric kind.
2. **Use the checked surface.** Keep every intermediate test, cast, and zero-divisor
   failure. Use the explicit result ascription when inference needs help. Bind fallible
   local computations immediately and preserve short-circuit branches.
3. **Justify total operations.** Supply the bound or positivity premise in the API.
   Test arbitrary accepted configurations, including zero divisors. A shipped preset
   cannot silently restrict a generic function's domain.
4. **Preserve errors and stores.** Keep typed causes through pure helpers and state or
   store lifts. Use size-aware indexing and checked writes. Verify that a failed call
   discards state changes at its observable boundary.
5. **Extend the framework once.** A new width or operator needs its operation matrix,
   construction rules, SSZ instance, and success/value laws. Keep raw word operations
   inside proved framework implementations. Audit every executable raw projection.
6. **Check behavior at the boundaries.** Pair an intended failure with a nearby success.
   Cover intermediate overflow, signed division, casts, empty collections, and branch
   laziness where relevant. Compare with the pinned Python behavior.
7. **Check inheritance and representation.** Exercise affected forks at both presets.
   New numeric field types need serialization and cached-root tests. Test tier premises
   through child overrides and keep theorem statements over each fork's declarations.
8. **Maintain proofs and documentation.** Update characterization statements, audit
   axioms, and regenerate proof coverage. Record known differences in the project records.
   Recheck Section 3 when the upstream integer library or spec pin changes.

Source review and behavior tests establish adherence to the bind rules. Changes to the
arithmetic framework also record build and run-time costs. Prefer a cheaper equivalent
implementation when measurements support it; preserve the semantic contract at any cost.

## 8. Checking this document against a pin

The claims in Section 3 are observations, and a re-pin can change them. Install the built
pyspec in a scratch environment and evaluate the expressions directly:

```bash
uv venv /tmp/pyspec-venv
VIRTUAL_ENV=/tmp/pyspec-venv uv pip install "eth-consensus-specs[test]==1.7.0b4"
```

```python
from eth_consensus_specs.fulu import mainnet as spec

spec.Gwei(2**64 - 1) + 1                              # raises SSZValueError
spec.Slot(1) + spec.Epoch(1)                          # raises TypeError
spec.compute_start_slot_at_epoch(spec.Epoch(2**60))   # raises SSZValueError
spec.saturating_sub(spec.Gwei(1), spec.Gwei(5))       # Gwei(0)
```

The operators live in `ssz/uint.py` of `eth-ssz-specs`, in the class `BaseUint`. Each one ends
in `cls._wrap(...)`, the range test.
