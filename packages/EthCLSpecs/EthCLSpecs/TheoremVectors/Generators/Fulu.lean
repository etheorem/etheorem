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
clause selects them and the search runs on them. Their `.eq` reading
survives the reader. The output type is an `Except` over a pair of boxed
`State` values, so the `.eq` face's projected output rule records the run's
return value, the pair's first component read through the box's `.view`
(§11.3). An `.ok` point records the container's bytes and its root. An
`.error` point records the error's repr, the `.runError` row's rule. The
random search won the one disjunct once, and its winner lives in the
committed hint file; a run replays that witness, so each record's
`witnessSearcher` field reads `hinted-random`. The file still gives the
two theorems no named line; the `characterized` clause runs them at its
default preset list.

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
-- The stage-6 gate theorems take one plain line each, in gate order. G1 runs
-- at both presets because it precedes the churn gate. G2 and G4 to G12 are
-- minimal-only: the queue cap is 64 at minimal and 262144 at mainnet, and a
-- churn limit above `minActivationBalance` needs a total active balance of
-- about 18.9 M ETH at mainnet.
theorem_vectors processConsolidationRequest_run_same_pubkeys presets minimal mainnet
theorem_vectors processConsolidationRequest_run_queue_full
-- The stage-5 spike: the churn gate writes the first operations cases.
-- G3's state condition, churn 0 at the genesis builders, holds at both
-- presets, so it is the easiest branch to meet.
theorem_vectors processConsolidationRequest_run_churn_too_low presets minimal mainnet
theorem_vectors processConsolidationRequest_run_unknown_pubkey
theorem_vectors processConsolidationRequest_run_source_not_authorized
theorem_vectors processConsolidationRequest_run_target_not_compounding
theorem_vectors processConsolidationRequest_run_source_inactive
theorem_vectors processConsolidationRequest_run_target_inactive
theorem_vectors processConsolidationRequest_run_source_exited
theorem_vectors processConsolidationRequest_run_target_exited
theorem_vectors processConsolidationRequest_run_shard_period_not_passed
theorem_vectors processConsolidationRequest_run_source_pending_withdrawal
-- The two success arms: the switch arm rewrites the source's withdrawal
-- credential prefix to compounding and queues the balance above the minimum,
-- and the success arm reserves churn and appends the pending consolidation.
-- The switch carries no churn hypothesis, so its line runs at both presets;
-- the success line stays minimal-only, where the churn hypothesis can hold.
-- Both searches answer notFound until the theorems carry manual terms: the
-- request's pubkeys must sit in the registry, and no draw or built state
-- puts them there.
theorem_vectors processConsolidationRequest_run_switch_to_compounding presets minimal mainnet
theorem_vectors processConsolidationRequest_run_consolidation_success

theorem_vectors characterized
theorem_vectors survey
