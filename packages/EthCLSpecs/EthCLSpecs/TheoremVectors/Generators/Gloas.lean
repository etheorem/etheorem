import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Gloas
import EthCLSpecs.TheoremVectors.Bindings.Gloas
import EthCLSpecs.TheoremVectors.Seeds.Gloas

/-!
# `EthCLSpecs.TheoremVectors.Generators.Gloas`: the Gloas generator file

The generator list for Gloas (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header
names the fork's binding; the `characterized` clause selects the contract
theorems and runs the search on them; the `survey` clause reads and lists
every other public theorem of the fork's proof namespace, phase A alone
(§14.3). The `skip` lines record the four existentials over a run's result
(`initiateBuilderExit_run_inRange` and its three variants), which §7.3's
shape set cannot express and decision point A excluded.

The named lines carry the stage-2 acceptance theorems:
`getPtcElseOffset_lt_same_slot` writes from `default` inputs, and the
three window theorems write from seeded inputs. The window runs
`computePtcFromFulu` over the state, and `default`'s empty validator set
drives the balance-weighted selection into its fuel bound, so the seed
`activeState` supplies 64 active validators instead; the window offsets
pin the smallest index of the region each hypothesis names
(`IMPLEMENTATION_NOTES.md` records the deviation from the plan's
"`default` inputs" acceptance). The seed terms are `[Preset]`-generic and
elaborate inside the theorem's telescope, so a `presets` clause can run
them at any preset.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas

theorem_vectors characterized
theorem_vectors survey

theorem_vectors skip initiateBuilderExit_run_inRange
  "existential over the run's post-state; no shape expresses it (§7.3)"
theorem_vectors skip initiateBuilderExit_run_outOfRange
  "existential over the run's post-state; no shape expresses it (§7.3)"
theorem_vectors skip initiateBuilderExit_run_inRange_no_wrap
  "existential over the run's post-state; no shape expresses it (§7.3)"
theorem_vectors skip initiateBuilderExit_run_inRange_no_wrap_minimal
  "existential over the run's post-state; no shape expresses it (§7.3)"
theorem_vectors skip initiateBuilderExit_run_inRange_no_wrap_mainnet
  "existential over the run's post-state; no shape expresses it (§7.3)"

theorem_vectors initializePtcWindow_lt with
  (state := EthCLSpecs.TheoremVectors.Seeds.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Seeds.Gloas.windowZero)
theorem_vectors initializePtcWindow_lt_default with
  (state := EthCLSpecs.TheoremVectors.Seeds.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Seeds.Gloas.windowZero)
theorem_vectors getPtcElseOffset_lt_same_slot
theorem_vectors initializePtcWindow_ge with
  (state := EthCLSpecs.TheoremVectors.Seeds.Gloas.activeState)
  (i := EthCLSpecs.TheoremVectors.Seeds.Gloas.windowEpoch)
