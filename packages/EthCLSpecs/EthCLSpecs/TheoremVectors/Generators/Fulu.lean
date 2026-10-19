import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Generators.Fulu`: the Fulu generator file

The generator list for Fulu (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header
names the fork's binding; the named lines come before the discovery clauses
(§14.3's positional order); the `characterized` clause selects the contract
theorems and runs the search on them; the `survey` clause reads and lists
every other public theorem of the fork's proof namespace, phase A alone
(§14.3).

The five branch theorems of `Proofs/Fulu/Balances.lean` run as named lines;
four of them take their witness terms from the `theorem_vectors_manual`
registrations under the theorems in that file
(`THEOREM_VECTORS_ARCHITECTURE.md` §14.3).

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
searcher choice or manual term changes an output type, so the file gives
the two theorems no named line.

`modBalance_pureState` also carries `@[characterizes]`; its function-typed
input `f` has no SSZ form (§1.2), and the clause records the reader's
`unsupported` reason instead of a vector. The theorem needs no skip line.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Fulu.fulu

-- §14.3: the named lines precede the discovery clauses. A named line below
-- a clause that already ran its theorem is an error.
-- The out-of-range and witness-backed lines take their terms from the
-- registrations under their theorems in `Proofs/Fulu/Balances.lean`. The
-- manual searcher checks the terms alone, so both presets are cheap.
theorem_vectors decreaseBalance_run_outOfRange presets minimal mainnet
theorem_vectors increaseBalance_run_outOfRange presets minimal mainnet
-- The no-underflow and overflow lines take their terms from the
-- registrations under their theorems. The manual searcher searches
-- nothing, so both presets stay cheap.
theorem_vectors decreaseBalance_run_no_underflow presets minimal mainnet
theorem_vectors increaseBalance_run_overflow presets minimal mainnet
-- The no-wrap theorem needs only an in-range index, which the random
-- searcher's coupled grid fixes at `0` over its drawn states; the grid
-- fixes `delta` beside it. The random searcher caps itself at mainnet over
-- a state-typed container, so this line stays minimal-only.
theorem_vectors increaseBalance_run_no_wrap

theorem_vectors characterized
theorem_vectors survey
