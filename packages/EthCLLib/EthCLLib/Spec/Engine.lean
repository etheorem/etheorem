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

## Two classes, one boundary

Three spec predicates cross the execution layer, and they do not all cross it
the same way. `is_inclusion_list_satisfied` and `verify_and_notify_new_payload`
are literal `execution_engine.*` calls, Engine-API methods on the object the
spec threads as an argument. `is_data_available` is a free function whose body
calls `retrieve_column_sidecars_and_kzg_commitments`, which the spec's own
comment marks "implementation and context dependent". Same trust class, two
different origins, so `ExecutionEngine` holds the Engine-API pair and
`DataAvailability` holds the retrieval predicate. Filing the third under a
class named for the Engine API would misname it at the one place a reader
checks what the spec actually calls.

Both live here, both default to the optimistic mock, and both are overridden
the same way. That is the single execution-layer trust boundary; the split is
in what the members are called, not in where they live.

Fulu is the exception worth naming: its `is_data_available` takes the column
sidecars the runner supplies and checks them for real (KZG proofs and all), so
it stays a spec function there and does not read this seam. Gloas *modified*
the signature to take a beacon block root and retrieve the columns itself
(`gloas/fork-choice.md`), which is the part no harness can answer, which is
why the Gloas-and-later form is here.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The execution-layer seam: `ExecutionEngine` predicates whose verdict an
external EL owns. Generic over the fork's payload / transaction / execution-request
types (they are fork-namespaced or shared types a framework class cannot name
concretely).

The two byte-shaped arguments below stay raw (`Vector UInt8 48` for a KZG
commitment, `Vector UInt8 32` for a root) rather than becoming further class
parameters. Every fork spells those the same way, and `CryptoBackend` already
takes its buffers raw for the same reason. -/
class ExecutionEngine (Payload : Type) (Tx : Type) (Requests : Type) where
  /-- `is_inclusion_list_satisfied(execution_payload, inclusion_list_transactions)`
  (EIP-7805): whether the payload includes the required inclusion-list
  transactions. Body is EL-implementation-defined. -/
  isInclusionListSatisfied : Payload → Array Tx → Bool
  /-- `verify_and_notify_new_payload(new_payload_request)`: whether the EL accepts
  the payload, and the notification that it exists. The spec bundles the arguments
  into a `NewPayloadRequest`; they arrive here unbundled, in the order the
  constructor lists them.

  One argument is not what the spec passes. `NewPayloadRequest.versioned_hashes`
  is `[kzg_commitment_to_versioned_hash(c) for c in bid.blob_kzg_commitments]`,
  and that mapping (a SHA-256 of the commitment with the version byte replaced)
  is not modeled in the tree, so the commitments arrive unmapped and a consumer
  wiring a real EL applies the map. No information is lost, since the map is a
  pure per-commitment function. Recorded rather than hidden: the seam is the one
  place a real consumer reads, so a difference in what it is handed belongs in
  its docstring. -/
  verifyAndNotifyNewPayload :
    (payload : Payload) → (blobKzgCommitments : Array (Vector UInt8 48)) →
    (parentBeaconBlockRoot : Vector UInt8 32) → (executionRequests : Requests) → Bool

/-- The default engine: the optimistic always-`true` mock, the residual EL trust
boundary of every engine-gated spec branch. Generic, so it serves every fork; a
consumer wanting a real (or refuting) verdict overrides `[ExecutionEngine]`
locally with a `letI` at the concrete fork types. -/
instance instExecutionEngineOptimistic {Payload Tx Requests : Type} :
    ExecutionEngine Payload Tx Requests where
  isInclusionListSatisfied _ _ := true
  verifyAndNotifyNewPayload _ _ _ _ := true

/-- The data-availability seam: `is_data_available(beacon_block_root)` from Gloas
onward, whose body retrieves column sidecars through a function the spec marks
implementation-dependent. Not an Engine-API call, hence its own class; same trust
class as `ExecutionEngine`, hence the same file and the same optimistic default.

Takes no fork types, so it needs no parameters: the argument is a root, and every
fork spells that `Vector UInt8 32`. -/
class DataAvailability where
  /-- `is_data_available(beacon_block_root)` (`gloas/fork-choice.md`): whether the
  block's column sidecars can be retrieved and all verify. Retrieval is
  implementation-defined, so no harness can answer it from the vector alone. -/
  isDataAvailable : Vector UInt8 32 → Bool

/-- The default availability oracle: optimistic, as `ExecutionEngine`'s is. A test
overrides it with a `letI` to drive the unavailable branch. -/
instance instDataAvailabilityOptimistic : DataAvailability where
  isDataAvailable _ := true

end EthCLLib.Spec
