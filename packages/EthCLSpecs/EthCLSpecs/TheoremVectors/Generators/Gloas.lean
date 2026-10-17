import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Gloas
import EthCLSpecs.TheoremVectors.Bindings.Gloas
import EthCLSpecs.TheoremVectors.Manual.Gloas

/-!
# `EthCLSpecs.TheoremVectors.Generators.Gloas`: the Gloas generator file

The generator list for Gloas (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header
names the fork's binding; the named lines and the `skip` lines come before
the discovery clauses (§14.3's positional order); the `characterized`
clause selects the contract theorems and runs the search on them; the
`survey` clause reads and lists every other public theorem of the fork's
proof namespace, phase A alone (§14.3). The `skip` lines exclude the four
existentials over a run's result (`initiateBuilderExit_run_inRange` and
its three variants) before the clauses select them; §7.3's shape set
cannot express them and decision point A excluded them.

Each theorem's run carries its own heartbeat budget from the
`theorem_vectors.maxHeartbeats` option (§14.4); the file sets no option of
its own.

The named lines carry the stage-2 acceptance theorems and the stage-3
ones, and stage 8 runs four of them at both presets: the three stage-2
lines and `processBuilderPendingPayments_run`, whose mainnet run wins
from the built searcher and whose pyspec case the check replays through
the mainnet interface. The window theorems run `computePtcFromFulu` over
the state, and
`default`'s empty validator set drives the balance-weighted selection into
its fuel bound, so the manual term `activeState` supplies 64 active
validators instead; the window offsets pin the smallest index of the
region each hypothesis names (`IMPLEMENTATION_NOTES.md` records the
deviation from the plan's "`default` inputs" acceptance). The manual
terms are `[Preset]`-generic and
elaborate inside the theorem's telescope, so a `presets` clause can run
them at any preset.

These lines run without a `default` witness:

- `getPtcElseOffset_lt_next_slot` takes no manual term; the bit-vector
  searcher solves the slot pair.
- `canBuilderCoverBid_iff` takes no manual term; the random searcher draws
  the state, walks the coupled builder index, and the solver picks each
  side's `bidAmount` (§9.4).
- `isValidIndexedPayloadAttestation_eq_true_iff_checks` keeps its manual
  state and attestation terms, which win the true side; its false-side
  disjuncts need containers the manual terms do not vary, and the random
  searcher draws them after the manual and bit-vector handoffs fail
  (§9.2, §9.4).
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas

-- §14.3: the named lines precede the discovery clauses. A named line below
-- a clause that already ran its theorem is an error.
theorem_vectors initializePtcWindow_lt with
  (state := EthCLSpecs.TheoremVectors.Manual.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Manual.Gloas.windowZero)
  presets minimal mainnet
theorem_vectors initializePtcWindow_lt_default with
  (state := EthCLSpecs.TheoremVectors.Manual.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Manual.Gloas.windowZero)
  presets minimal mainnet
theorem_vectors getPtcElseOffset_lt_same_slot presets minimal mainnet
theorem_vectors getPtcElseOffset_lt_next_slot
theorem_vectors canBuilderCoverBid_iff
theorem_vectors isValidIndexedPayloadAttestation_eq_true_iff_checks with
  (state := EthCLSpecs.TheoremVectors.Manual.Gloas.iPacState)
  (a := EthCLSpecs.TheoremVectors.Manual.Gloas.iPacAttestation)
theorem_vectors initializePtcWindow_ge with
  (state := EthCLSpecs.TheoremVectors.Manual.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Manual.Gloas.windowEpoch)
-- The stage-8 acceptance theorem: the one characterized `.runOk` with a
-- pyspec handler, run at both presets. A named line wins over the
-- `characterized` clause, which stays minimal-only.
theorem_vectors processBuilderPendingPayments_run presets minimal mainnet

-- The builder-exit contract. The hypothesis reads the index through
-- `UInt64.toNat`, which the coupled walk and the solver's `UInt64`
-- fragment do not bridge, so the `built` grid and the random draws can
-- never fix the index against the built registry. The manual terms name
-- the `withQueue` grid step's state and the index `0`, so the assignment
-- is complete and the check decides it.
theorem_vectors initiateBuilderExit_run_eq with
  (preState := EthCLSpecs.TheoremVectors.Manual.Gloas.builderState)
  (builderIndex := (0 : EthCLSpecs.Gloas.BuilderIndex))

-- §14.3: the named lines and the skip lines precede the discovery
-- clauses. A line below a clause that already ran its theorem is an error.
theorem_vectors skip initiateBuilderExit_run_inRange
  "existential over the run's post-state; no shape expresses it (§7.3)"
theorem_vectors skip initiateBuilderExit_run_inRange_no_wrap
  "existential over the run's post-state; no shape expresses it (§7.3)"
theorem_vectors skip initiateBuilderExit_run_inRange_no_wrap_minimal
  "existential over the run's post-state; no shape expresses it (§7.3)"
theorem_vectors skip initiateBuilderExit_run_inRange_no_wrap_mainnet
  "existential over the run's post-state; no shape expresses it (§7.3)"

theorem_vectors characterized
theorem_vectors survey
