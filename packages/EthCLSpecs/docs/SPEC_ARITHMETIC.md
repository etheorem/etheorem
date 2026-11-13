# Spec arithmetic

How the consensus pyspec computes with integers, and the Lean 4 form that matches each case.
The document covers the fork bodies in `EthCLSpecs` and the arithmetic layer of `EthCLLib`.

Status: draft. Sections 1 to 3 state facts checked against the pin. Section 4 is the design.
Section 5 gives the reasons for it. Section 7 says which parts exist and which are open.

Pin: `v1.7.0-beta.4`, with `eth-ssz-specs` 0.1.0 as the pyspec's integer library. Line citations
(`<file>.md:NN`) resolve under `specs/` in `ethereum/consensus-specs` at the pin. Every re-pin
re-checks this document with the commands in Section 8.

## 1. The rule

For every modeled pyspec function and every input:

1. The Lean function raises exactly when the pyspec function raises.
2. When neither raises, the two results are equal.

The kind of error is free. The pyspec raises `SSZValueError`, `ZeroDivisionError`, `IndexError`,
or `AssertionError`, and the model may raise any error value in each case. One error arm can
serve every arithmetic fault.

The point where the model raises inside a function is free too. A raise discards the state, so
no caller can see how far the function ran.

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

The built Heze module holds 177 `assert` statements and no `try` block. Every raise ends the
call that started it. That fact is what makes the error kind free in Section 1.

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
- **Division and modulo cannot leave the range.** They raise on a zero divisor alone.

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
| a range fault or a zero divisor | `ArithFault` | The fault. It records the operator and the operands, for diagnosis only. |

`Slot`, `Epoch`, `Gwei`, and `ValidatorIndex` are abbreviations of `CLUint64`, as they are
abbreviations of `UInt64` today. `CLUint64` has the `SSZRepr` instance of `uint64`, so a
container field of that type has the same bytes and the same root.

### 4.2 Operator result types

`U` is `CLUint64` and `I` is `CLInt`. A `Checked` operand is an expression that is not bound
yet.

| Operands | Operators | Result | Raises |
|---|---|---|---|
| `U`, `U` | `+ - *` | `Checked U` | outside `[0, 2^64)` |
| `U`, `U` | `/ %` | `Checked U` | zero divisor |
| `I`, `I` | `+ - *` | `I` | never |
| `I`, `I` | `/ %` | `Checked I` | zero divisor |
| `I`, `U` in either order | `+ - * / %` | `Checked U` | outside `[0, 2^64)`, or zero divisor |
| `Nat`, `U` in either order | `+ - * / %` | `Checked U` | outside `[0, 2^64)`, or zero divisor |
| `Nat`, `I` in either order | `+ - *` | `I`, the `Nat` coerces | never |
| `Nat`, `Nat` | all | core Lean | never |
| any of the above with a `Checked` operand | same | `Checked` of the same type | the operand's fault, then the operator's |

Three properties follow.

- **Each step is tested.** In `a * b / c` the product raises when it passes `2^64`, even if the
  quotient fits.
- **Division floors as Python does.** `CLInt` uses `Int.fdiv` and `Int.fmod`.
- **A plain expression needs no bind until it divides.** `len xs + len ys * 2 - 1` has type
  `CLInt`. `(len xs + 1) / len ys` has type `Checked CLInt`.

### 4.3 Binding

An arithmetic expression is a `Checked` value. A `do` block binds it with `←`, once for the
whole expression.

```python
reward_numerator = base_reward * weight * unslashed_participating_increments
rewards[index] += reward_numerator // (active_increments * WEIGHT_DENOMINATOR)
```

```lean
let rewardNumerator ← baseReward * weight * unslashedIncrements
rewards := rewards.set! i (← rewardNumerator / (activeIncrements * Const.weightDenominator))
```

A bind is required in two places:

- **Where the pyspec assigns.** A `let` that mirrors a pyspec assignment takes `←`.
- **Where a plain value is needed.** A comparison, a branch condition, a store, and an argument
  typed `CLUint64` all take a value: `if (← a + b) > c`.

An unbound `Checked` value is a fault that no code has examined. If one path never uses it, the
model returns a value where the pyspec raises:

```lean
let total := a + b                    -- unbound
if useIt then total else return 0     -- the `else` path drops the fault
```

A sub-expression split out for layout may stay unbound when every path uses it.

The pyspec's `and` and `or` short-circuit. A second operand that contains arithmetic must be
bound inside its own branch, so it is formed only when the pyspec forms it.

### 4.4 The lift and the signatures

One instance lets `←` take an arithmetic expression in any monad whose error accepts a
`StateTransitionError`:

```lean
instance {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] : MonadLift (Except ArithFault) m
```

It raises through `throwArithmetic`, so the state machine sees `.arithmetic` and the store
machine sees `.transition (.arithmetic …)`. The error model needs no new arm.

A function's result type states whether it can raise:

| A function that | Returns |
|---|---|
| does arithmetic only | `Checked α` |
| also reads an index or asserts | `Except StateTransitionError α` |
| reads or writes the state | `StateTransition α` |

`Checked` is a monad, so a pure loop keeps its `for` and its `let mut`. A caller binds a
`Checked` function like any other action.

### 4.5 Conversions and literals

| pyspec | Lean | Raises |
|---|---|---|
| `Uint64(n)` from a plain `int` | `n.toUint64?` | negative, or past `2^64 - 1` |
| `int(x)` | `x.toInt` | never |
| `len(xs)` | `len xs`, a `CLInt` | never |
| a literal in an expression | the literal, typed by its neighbours | never |
| `max(a, b)`, `min(a, b)` | `max a b`, `min a b` | never |
| `saturating_sub(a, b)` | `a.saturatingSub b` | never |
| `sum(xs)` | `xs.foldlM (fun acc x => acc + x) 0` | as `+` |
| a store into a field | the store; the value passed its test when it was computed | never |

Two conversions leave the checked types, and both have long names so a reader sees them:

- `x.toPlainInt` gives a Lean `Nat`. Arithmetic on the result is unchecked.
- `n.toIndex?` gives a list position from a `CLInt`.

The constructor `CLUint64.mk` is private to the framework. `toUint64?` and `CLUint64.ofNat?`
are the only routes from a plain number to a checked one.

### 4.6 Indexing

An index class in `EthCLLib` says how an integer type names a position:

```lean
class ToIndex (ι : Type) where
  pos? : ι → Nat → Option Nat      -- `none` where the pyspec raises `IndexError`
```

It has instances for `Nat`, `CLUint64`, and `CLInt`. The `CLInt` instance counts a negative
index from the end. The raising read `sszGetIdx` takes any index type with an instance, and a
write helper takes the same class. `SizzLean` keeps `Nat` indices.

In the prototype the read returns a `Checked` value. A read is then an operand like any other,
and `balances[index] + delta` is one expression. A read of a structure needs one bind before
the field. `sszGetIdx` returns in the ambient monad today, so its result type is a choice still
to make.

### 4.7 The operator elaborator

Core Lean's operator elaborator reads the expected type. Under `let x ← a / b + 1` that type is
the transition monad. No operand type compares with a monad, so core skips the step that types
a literal operand, and the instance search then fails.

A scoped term elaborator in `EthCLLib.Spec` handles this case. It elaborates the operator tree
with no expected type. If the result is a `Checked` expression it keeps the term, and the lift
of Section 4.4 bridges to the monad. Any other tree falls through to core unchanged. When an
operand type is still unknown, as for a lambda binder that a later argument fixes, it waits.

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
| `a ** n` past the maximum | raises | wraps modulo `2^64` | not built |
| `a << n` past the maximum | raises | drops the high bits; shift taken modulo 64 | not built |
| `a >> n`, bitwise operators | in range | in range for `n < 64` | not built |
| a comparison | a `bool` | a `Bool` | a `Bool` |
| a cast from an out-of-range `int` | raises | `UInt64.ofNat` wraps | raises |
| the operator on a plain `int` operand | checked, result is `Uint64` | no instance; `UInt64.ofNat` wraps | checked, result is `CLUint64` |
| the result of an expression | a `Uint64` | a `UInt64` | a `Checked CLUint64` |

Core `UInt64` differs from the pyspec in every row that can raise. No setting changes that: the
operators are total functions, and a total function has no way to raise.

### 5.2 The plain kind, operation by operation

| Operation | pyspec `int` | Lean `Nat` | Lean `Int` | `CLInt` |
|---|---|---|---|---|
| `a + b`, `a * b` | unbounded | unbounded | unbounded | unbounded |
| `7 - 9` | `-2` | `0` | `-2` | `-2` |
| `-7 // 2`, `-7 % 2` | `-4`, `1` | no negative values | `-4`, `1` | `-4`, `1` |
| `7 // -2`, `7 % -2` | `-4`, `-1` | no negative values | `-3`, `1` | `-4`, `-1` |
| `7 // 0`, `7 % 0` | raises | `0`, `7` | `0`, `7` | raises |
| `-5 >> 1` | `-3` | no negative values | `-3` | not built |
| used as an index | yes; negative counts from the end | yes | no; needs `Int.toNat`, which maps a negative number to `0` | yes, through `ToIndex` |
| the operator on a `Uint64` operand | checked, result is `Uint64` | none in core | none in core | checked, result is `CLUint64` |

`Nat` fails on subtraction and on a zero divisor. `Int` fails on a zero divisor and on a
negative divisor, and its way back to an index hides a negative number. `CLInt` matches every
row that is built.

### 5.3 Why operators, when named helpers exist

The framework has `checkedAdd`, `checkedSub`, and `checkedMul`. They are correct, and the fork
bodies call them at about 57 sites. The built Heze module has about 500 operator sites, some of
them in helpers the model leaves out. Three reasons favour the operators.

- **The code reads as the pyspec.** A reviewer compares `a * b / c` with `a * b // c` at a
  glance. `checkedDiv (← checkedMul a b "…") c "…"` needs a second reading.
- **The type enforces the rule.** A helper is a choice the author makes at each site, and a
  missed site compiles. With `CLUint64`, the wrapping `+` does not exist.
- **No vector tests the rule.** One upstream test expects a range raise (Section 3.6), so only
  the type system can find a missed site.

### 5.4 Why a new type, when scoped instances on `UInt64` exist

Scoped instances can give `+` on `UInt64` a `Checked` result inside one namespace, with no
change to any field type. Two faults rule this out.

- **A literal operand reaches the core operator.** In scope, `a + 1` still resolves to core's
  wrapping `+`, because core's default instance types the literal first. Closing that hole
  needs a `default_instance`, and that attribute is global: it changes `1 + 1` in every module
  that imports the instance.
- **The meaning of `+` depends on an `open`.** The same line wraps in one file and raises in
  another. `UInt64.add` reaches the wrap in both.

A distinct type has neither fault. Its discipline shows in every signature.

### 5.5 Why `CLInt`, when `Nat` fits most sites

Plain integers in the spec are sizes, counters, and indices, and `Nat` represents all of them.
`CLInt` is chosen for two reasons.

- **The operators stay the pyspec's.** With `Nat`, a zero divisor needs a named helper, and
  `(last + 1) % len(validators)` becomes `checkedMod (last + 1) validators.size`. With `CLInt`
  it is `(last + 1) % len validators`.
- **A negative intermediate is represented.** `Nat` floors `7 - 9` at zero with no error.

The cost is inside the framework. `CLUint64` needs 40 operator instances, and `CLInt` adds
about 66, because each operator needs every pairing of the two types, their `Checked` forms,
and `Nat`. A macro generates them.

Lean's `Nat` stays in the fork bodies as a third plain representation. Preset constants are
`Nat`, and so are loop variables. Both work as operands (Section 4.2). `xs.size - 1` is a core
`Nat` subtraction, so a fork body writes `len xs - 1`.

### 5.6 Why three small restrictions

- **No `default_instance` on any operator.** The attribute is global (Section 5.4). Without it
  a literal operand takes the plain-integer path, which gives the same result.
- **No coercion from `CLUint64` to `Nat`.** Lean's operator elaborator would use it to turn
  `a + n`, with `n : Nat`, into unchecked `Nat` arithmetic.
- **A long name for the conversion to `Nat`.** With the name `toNat`, a formula such as
  `a.toNat * 3` compiles and never raises. With `toPlainInt` the compiler lists every use. On
  the `Gwei` values of Fulu there are three: two are correct, and one is an unchecked product.

### 5.7 Why the index class sits in `EthCLLib`

`SizzLean` could own the class, and its path forms `sszGet state f[i]` could then take a checked
index. Those forms exist to hide the state box and to drive the cached tree update. A state
held as a plain value does not need them: a read is a projection and a write is a structure
update. `sszGetIdx` is a function in `EthCLLib` with no reference to the box, so the class
belongs beside it.

### 5.8 What the migration costs

One unit was migrated to measure the cost: `Gwei` in Fulu, with the other units left as
`UInt64`.

| Measure | Value |
|---|---|
| Top-level modules of Fulu that needed an edit | 11 of 23 |
| Distinct build errors | 79 |
| Lines changed | 126 added, 111 removed |
| Functions whose result type changed | 14 |
| Modules that compiled with no edit | `Constants`, `State`, `Blocks`, `Committees`, the ten container modules, and six more |

The errors by kind, sorted by message pattern:

| Kind | Count |
|---|---|
| An operator result used as a plain value | 22 |
| A caller of a function whose result type changed | 16 |
| A `UInt64` value passed as `Gwei`, often `UInt64.ofNat` of a `Nat` formula | 15 |
| `Gwei` mixed with a raw `UInt64` operand | 12 |
| A helper typed for `UInt64` | 7 |
| Another type slip | 7 |

Most errors of the first and third kinds mark a site where the model returned a value and the
pyspec raises. A loop of four operators over 200 million passes ran in 2.0 s with raw
operators, 2.0 s with the named helpers, and 2.16 s with `CLUint64`.

## 6. What the rule allows and forbids

The rule fixes when the model raises. It leaves the form of the test open.

Allowed:

- **One error arm for every arithmetic fault.** `.arithmetic` serves range faults and zero
  divisors alike.
- **A test before the operation.** `seconds_to_milliseconds` compares against `UINT64_MAX // 1000`
  first, and the product then cannot leave the range.
- **A raw operator behind a proof.** An index reduced modulo a positive preset length needs no
  test. The site must carry the proof, as `vmodGet` does through `ValidModulus`.

Forbidden:

- **A `Nat` intermediate where the pyspec holds a checked value.** In `a * b // c` the product
  can pass `2^64` while the quotient fits. `a.toPlainInt * b.toPlainInt / c.toPlainInt` hides
  that raise.
- **A default on a zero divisor.** `x % 0` raises in the pyspec, and a helper that returns `0`
  breaks the rule.
- **An unbound expression that a path drops** (Section 4.3).
- **A bind above the branch that uses it.** The model then raises on a path where the pyspec
  computes nothing.
- **`xs[i]!` where the pyspec can raise.** That form returns a default on a bad index.

## 7. Status and open work

| Part | State |
|---|---|
| `CLUint64`, `Checked`, `ArithFault`, the five operators with value, expression, and `Nat` operands | Built in a first spike, as one module for `EthCLLib/Spec/`. Not in the tree |
| The lift, the operator elaborator, `SSZRepr CLUint64` | Built in the same module |
| `Gwei` as `CLUint64` in Fulu | Ported in the first spike, and Fulu builds with it. Not in the tree. No conformance run: the runner links all three forks |
| `CLInt` and its mixed operators | Standalone prototype |
| `ToIndex` and the raising read over it | Standalone prototype, on `Array` |
| `Slot`, `Epoch`, `ValidatorIndex`, and bare `Uint64` constants as `CLUint64` | Not started |
| Gloas, Heze, and the proofs | Not ported. With the Fulu port applied, `Gloas/EpochProcessing` and `Proofs/Fulu/Balances` fail first |

Open work, in the order it blocks:

1. **Conformance.** Port Gloas and Heze for `Gwei`, then run the vectors against the Fulu port.
2. **Proofs.** Repair `Proofs/Fulu/Balances`, which states `increaseBalance` with a raw `+`. The
   statement form is `(∃ c, a + b = .ok c) ↔ a.toPlainInt + b.toPlainInt < 2^64`; that lemma is
   proved in a standalone prototype.
3. **The other units.** Each unit left as `UInt64` forces a hand conversion where it meets a
   migrated one. Four such sites exist in the Fulu port.
4. **The remaining operators.** `**` and the shifts for `CLUint64`; the shift for `CLInt`.
5. **Widths.** `Uint8`, `Uint32`, and `Uint256` appear in the pyspec. Each needs the same
   instance set.
6. **The private constructor and the literal bound.** `CLUint64.mk` is public in the first
   spike, and a literal past `2^64` wraps.
7. **A linter for a dropped expression.** Section 4.3 states the rule for authors. A check that
   flags a `Checked` value some path never binds would enforce it.
8. **Unit types.** Distinct types for `Slot`, `Epoch`, and `Gwei` would turn a unit mix into a
   type error (Section 3.4). The rule does not need them.
9. **Harness classes.** The driver sorts model errors by the Python exception class the
   reference wrapper catches (`FRAMEWORK_ARCHITECTURE.md` §6). That section treats a full list
   as a bare `Exception`. At the pin a full list raises `SSZValueError`.

`FRAMEWORK_ARCHITECTURE.md` §10 describes the arithmetic layer as built on `main`. It assumes
that the pyspec computes in unbounded integers and that the spec text keeps every intermediate
in range. Section 3 shows both assumptions fail at the pin, so §10 changes when this design
lands.

`DISCREPANCIES.md` is the home for each known site where the model returns a value and the
pyspec raises.

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
