import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Gloas
import EthCLSpecs.TheoremVectors.Bindings.Gloas

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
the mainnet interface.

Two named lines run without a default witness and carry no registration:

- `getPtcElseOffset_lt_next_slot`: the bit-vector
  searcher solves the slot pair.
- `canBuilderCoverBid_iff`: the random searcher draws
  the state, walks the coupled builder index, and the solver picks each
  side's `bidAmount` (§9.4).

The window theorems, the payload-attestation theorem, and the
builder-exit contract take their witness terms from the
`theorem_vectors_manual` registrations under their theorems
(`THEOREM_VECTORS_ARCHITECTURE.md` §14.3): the window ones in
`Proofs/Gloas/InitializePtcWindow.lean`, the payload-attestation one in
`Proofs/Gloas/IsValidIndexedPayloadAttestation.lean`, and the
builder-exit one in `Proofs/Gloas/InitiateBuilderExit.lean`.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas

-- §14.3: the named lines precede the discovery clauses. A named line below
-- a clause that already ran its theorem is an error.
-- The window theorems take their terms from the registrations under
-- their theorems in `Proofs/Gloas/InitializePtcWindow.lean`. The manual
-- searcher checks the terms alone, so both presets are cheap.
theorem_vectors initializePtcWindow_lt presets minimal mainnet
theorem_vectors initializePtcWindow_lt_default presets minimal mainnet
theorem_vectors getPtcElseOffset_lt_same_slot presets minimal mainnet
theorem_vectors getPtcElseOffset_lt_next_slot
theorem_vectors canBuilderCoverBid_iff
theorem_vectors isValidIndexedPayloadAttestation_eq_true_iff_checks
theorem_vectors initializePtcWindow_ge
-- The stage-8 acceptance theorem: the one characterized `.runOk` with a
-- pyspec handler, run at both presets. A named line wins over the
-- `characterized` clause, which stays minimal-only.
theorem_vectors processBuilderPendingPayments_run presets minimal mainnet

-- The builder-exit contract takes its witness terms from the
-- registration under the theorem in `Proofs/Gloas/InitiateBuilderExit.lean`.
theorem_vectors initiateBuilderExit_run_eq

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
