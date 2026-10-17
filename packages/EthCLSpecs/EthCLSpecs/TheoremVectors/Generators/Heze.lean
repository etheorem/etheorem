import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Heze
import EthCLSpecs.TheoremVectors.Bindings.Heze

/-!
# `EthCLSpecs.TheoremVectors.Generators.Heze`: the Heze generator file

The generator list for Heze (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header
names the fork's binding; the `skip` lines come before the discovery
clauses (§14.3's positional order); the `characterized` clause selects the
contract theorems and runs the search on them; the `survey` clause reads
and lists every other public theorem of the fork's proof namespace, phase A
alone (§14.3). The file carries no named lines, because the stage-9 run
wrote no vector for any Heze theorem.

The file stays short because Heze's corpus cannot reach a searcher today.
Phase A reports nearly every theorem `unsupported` at the `FcMap` /
`ExecutionEngine` instance seams, whose binder the reader cannot bind.
Nearly all of those theorems also take block inputs, such as `Store` or
`SignedExecutionPayloadEnvelope` (§1.2). Opening the corpus takes both: a
reader that binds the seams, and a block-input path (a builder that
produces well-formed blocks, or a store a named line supplies) for the
`shouldExtendPayload` and `onExecutionPayloadEnvelope` theorems.

The two `getInclusionListCommittee` theorems read past the seams, and the
`skip` lines exclude them with the reason the run observed: their third
input `runnerStore : σ` has a type-variable type, which the command can
neither fix nor draw. The probe rejects such a statement at phase B1 with
`the command cannot fix the type parameters #[σ] yet`. The reader's input
rules carry no entry that names a type-variable input, so the skip lines
supply that reason.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Heze.heze

-- §14.3: the skip lines precede the discovery clauses. The two committee
-- theorems bind `runnerStore : σ`, a type-variable input the command can
-- neither fix nor draw; the probe rejects the statement at phase B1.
theorem_vectors skip getInclusionListCommittee_run_eq
  "the run's input `runnerStore : σ` has a type-variable type; the command \
   can fix no type parameter and draw no value for it"
theorem_vectors skip getInclusionListCommittee_run_error_of_empty
  "the run's input `runnerStore : σ` has a type-variable type; the command \
   can fix no type parameter and draw no value for it"

theorem_vectors characterized
theorem_vectors survey
