import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Gloas
import EthCLSpecs.TheoremVectors.Bindings.Gloas
import EthCLSpecs.TheoremVectors.Seeds.Gloas

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
ones. The window theorems run `computePtcFromFulu` over the state, and
`default`'s empty validator set drives the balance-weighted selection into
its fuel bound, so the seed `activeState` supplies 64 active validators
instead; the window offsets pin the smallest index of the region each
hypothesis names (`IMPLEMENTATION_NOTES.md` records the deviation from the
plan's "`default` inputs" acceptance). The seed terms are `[Preset]`-generic
and elaborate inside the theorem's telescope, so a `presets` clause can run
them at any preset.

These lines run without a `default` witness:

- `getPtcElseOffset_lt_next_slot` takes no seed; the bit-vector source
  solves the slot pair.
- `canBuilderCoverBid_iff` takes no seed; the random source draws the
  state, walks the coupled builder index, and the solver picks each
  side's `bidAmount` (§9.4).
- `isValidIndexedPayloadAttestation_eq_true_iff_checks` keeps its state
  and attestation seeds, which win the true side; its false-side cases
  need containers the seed does not vary, and the random source draws
  them after the seed and the bit-vector handoff fail (§9.2, §9.4).
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas

-- §14.3: the named lines precede the discovery clauses. A named line below
-- a clause that already ran its theorem is an error.
theorem_vectors initializePtcWindow_lt with
  (state := EthCLSpecs.TheoremVectors.Seeds.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Seeds.Gloas.windowZero)
theorem_vectors initializePtcWindow_lt_default with
  (state := EthCLSpecs.TheoremVectors.Seeds.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Seeds.Gloas.windowZero)
theorem_vectors getPtcElseOffset_lt_same_slot
theorem_vectors getPtcElseOffset_lt_next_slot
theorem_vectors canBuilderCoverBid_iff
theorem_vectors isValidIndexedPayloadAttestation_eq_true_iff_checks with
  (state := EthCLSpecs.TheoremVectors.Seeds.Gloas.iPacState)
  (a := EthCLSpecs.TheoremVectors.Seeds.Gloas.iPacAttestation)
theorem_vectors initializePtcWindow_ge with
  (state := EthCLSpecs.TheoremVectors.Seeds.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Seeds.Gloas.windowEpoch)

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
