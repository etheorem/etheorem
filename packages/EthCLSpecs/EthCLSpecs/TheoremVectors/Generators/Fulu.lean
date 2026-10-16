import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Fulu
import EthCLSpecs.TheoremVectors.Seeds.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Generators.Fulu`: the Fulu generator file

The generator list for Fulu (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header
names the fork's binding; the named lines come before the discovery clauses
(§14.3's positional order); the `characterized` clause selects the contract
theorems and runs the search on them; the `survey` clause reads and lists
every other public theorem of the fork's proof namespace, phase A alone
(§14.3).

The five branch theorems of `Proofs/Fulu/Balances.lean` run as named lines,
four of them on seeds (two on the `Seeds.Fulu` states, two on inline
`default` terms):

- The two out-of-range theorems pin both state binders to `default`, whose
  empty balances list makes the `¬ i < size` hypothesis true at `i := 0`,
  and both sides of each equation reduce to the same `.outOfBounds` error.
  The seed source checks the author's terms and runs no search, so each
  line is cheap and runs at both presets.
- `decreaseBalance_run_no_underflow` takes `oneBalanceState` with
  `delta := 2`, and `increaseBalance_run_overflow` takes `maxBalanceState`
  with `delta := 1`. An exploratory seedless line answered `notFound` for
  the no-underflow line within its draw budget. The overflow line's
  coupled grid caps `delta` below 64. Only the wide arm of the `UInt64`
  draw can land a balance within 64 of `2 ^ 64`, about one value in
  `2 ^ 59`, so the redraw budget never meets one. The seeds write the
  lines deterministically, and the seed source is what reaches mainnet,
  where the random source caps itself over a state-typed container. It
  searches nothing, so these lines also run at both presets.
- `increaseBalance_run_no_wrap` takes no seed. The random source draws the
  two states, the coupled grid fixes `i` and `delta` at `0`, and the
  hypothesis holds at the drawn balances (§9.4). The line runs at minimal
  only: the random source caps itself at mainnet over a state-typed
  container, and stage 8's discipline spends a mainnet run only where the
  run is cheap.

The two `runOk` lines record the run's return value. The mutators are
value-style: each takes the state it writes as an argument and returns
the mutated one. The record's output is therefore the pair's first
component, read through the box's `.view` and recorded at the
container's type. The threaded `preState` is a bystander for these
statements. The store pick stays for the `Unit`-return steps, whose
mutation lives on the store (§11.3, §12.2). The pre-write balance and
`delta` appear among the inputs, and the output holds the written
balance. The three `runError` lines record the error the run returns,
which is the whole of what they state.

The two exact run equations (`increaseBalance_run_eq`,
`decreaseBalance_run_eq`) carry `@[characterizes]`, so the `characterized`
clause selects them and the report shows their outcome. Their `.eq`
reading survives the reader, but the output type is an `Except` over a
pair of boxed `State` values, and the box has neither an `SSZRepr` nor a
`ToString` instance, so the recorder skips each run with that reason. No
source choice or seed changes an output type, so the file gives the two
theorems no named line.

`modBalance_pureState` also carries `@[characterizes]`; its function-typed
input `f` has no SSZ form (§1.2), and the clause records the reader's
`unsupported` reason instead of a vector. The theorem needs no skip line.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Fulu.fulu

-- §14.3: the named lines precede the discovery clauses. A named line below
-- a clause that already ran its theorem is an error.
-- The two out-of-range theorems: `default`'s empty balances list makes
-- `¬ i < size` true at `i := 0`. The seed source checks the terms alone,
-- so both presets are cheap.
theorem_vectors decreaseBalance_run_outOfRange with
  (state := default)
  (preState := default)
  (i := 0)
  (delta := 0)
  presets minimal mainnet
theorem_vectors increaseBalance_run_outOfRange with
  (state := default)
  (preState := default)
  (i := 0)
  (delta := 0)
  presets minimal mainnet
-- The no-underflow and overflow lines carry seeds: `oneBalanceState`
-- with `delta := 2`, and `maxBalanceState` with `delta := 1`. The seed
-- source searches nothing, so both presets are cheap.
theorem_vectors decreaseBalance_run_no_underflow with
  (state := EthCLSpecs.TheoremVectors.Seeds.Fulu.oneBalanceState)
  (preState := default)
  (i := 0)
  (delta := 2)
  presets minimal mainnet
theorem_vectors increaseBalance_run_overflow with
  (state := EthCLSpecs.TheoremVectors.Seeds.Fulu.maxBalanceState)
  (preState := default)
  (i := 0)
  (delta := 1)
  presets minimal mainnet
-- The no-wrap theorem needs only an in-range index, which the random
-- source's coupled grid fixes at `0` over its drawn states; the grid
-- fixes `delta` beside it. The random source caps itself at mainnet over
-- a state-typed container, so this line stays minimal-only.
theorem_vectors increaseBalance_run_no_wrap

theorem_vectors characterized
theorem_vectors survey
