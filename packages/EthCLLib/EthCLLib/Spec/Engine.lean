/-!
# `EthCLLib.Spec.Engine`: the `[ExecutionEngine]` seam

The spec's `ExecutionEngine` predicates are Engine-API calls answered by an
external execution layer (EL), so their verdicts are EL-implementation-defined
and cannot be modeled as fixed values without hiding the trust boundary. Like
`[CryptoBackend]` one file over, this is an injection seam, a typeclass
boundary where the consumer picks the implementation (`FRAMEWORK_ARCHITECTURE.md`
§1): the default instance below is the optimistic always-`true` mock (every
conformance path stays on the accepting branch with no call-site change), and
a test supplies a local instance returning `false` to exercise the rejecting
branch.

`CryptoBackend` works on raw `ByteArray` wire buffers; the engine predicates
instead take the fork's own SSZ types. `ExecutionPayload` is re-declared per
fork namespace, each fork's copy a nominally distinct type; `Transaction` is
today a single shared abbrev, parameterized here anyway so a fork that ever
re-declares it needs no seam change. The class is generic over both; the optimistic instance
is generic too, so every fork resolves it without per-fork glue, and a local
`letI` at one fork's concrete types overrides it where a test needs the
refuting branch.

One deliberate difference from `CryptoBackend`: that seam ships named backends
(`ffi` / `verifyOff` / `symbolic`) a consumer must inject, so a forgotten
injection is a compile error; this one registers the optimistic mock as a
global instance, so every conformance path works with zero wiring. The cost is
that a consumer wiring a real EL verdict must remember the local override,
nothing forces it.

Heze's FOCIL gate (`is_inclusion_list_satisfied`) is the first consumer.
Gloas's engine predicates (`verify_and_notify_new_payload`,
`is_data_available`) are still modeled as inline constants and can migrate
here as a follow-up.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The execution-layer seam: `ExecutionEngine` predicates whose verdict an
external EL owns. Generic over the fork's payload / transaction types (they are
fork-namespaced or shared types a framework class cannot name concretely). -/
class ExecutionEngine (Payload : Type) (Tx : Type) where
  /-- `is_inclusion_list_satisfied(execution_payload, inclusion_list_transactions)`
  (EIP-7805): whether the payload includes the required inclusion-list
  transactions. Body is EL-implementation-defined. -/
  isInclusionListSatisfied : Payload → Array Tx → Bool

/-- The default engine: the optimistic always-`true` mock, the residual EL trust
boundary of every engine-gated spec branch. Generic, so it serves every fork; a
consumer wanting a real (or refuting) verdict overrides `[ExecutionEngine]`
locally with a `letI` at the concrete fork types. -/
instance instExecutionEngineOptimistic {Payload Tx : Type} : ExecutionEngine Payload Tx where
  isInclusionListSatisfied _ _ := true

end EthCLLib.Spec
