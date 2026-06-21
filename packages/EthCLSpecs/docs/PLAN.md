# EthCLSpecs: Implementation Plan

This document sequences the work that the three design documents describe.
`SPEC_AUTHORING_MODEL.md` is the contract between author and framework,
`FRAMEWORK_ARCHITECTURE.md` builds the framework from below, and
`SPECS_ARCHITECTURE.md` ports the Fulu and Gloas specs on top. This plan is their
sibling. It turns those decisions into ordered phases, each with concrete
deliverables and an acceptance criterion that says the phase is done.

The work splits across three Lake packages. `EthCLLib` is the framework and DSL:
the capturing declaration forms, the header macros, the effect monad, the error
types, the tier system, the container front-end over SizzLean, the crypto and
arithmetic layers, the finite-map and fork-choice store, the fork-interface
typeclass, and the generic `PySpecTests` driver. `EthCLSpecs` is the spec body
for `EthCLSpecs.Fulu` and `EthCLSpecs.Gloas`, plus the `pyspec_server` runner exe
that instantiates the generic driver at a fork, plus the `pytest-xdist` harness
and the Lean unit-test library. `EthCLProofs` is the deferred proof package, a
standalone library at the pure configuration, held out of the umbrella the way
the repository holds `LeanPoseidonProofs` out, so mathlib never reaches the
framework, the specs, the runner, or the conformance path.

The phase order follows one rule from `SPECS_ARCHITECTURE.md`: a later fork is a
diff over its parent, so Fulu must exist whole before Gloas can diff it. Inside
that rule, the sequence is de-risk first, validate on the smallest surface, then
broaden. Phase 0 de-risks the unverified machinery and lands the prerequisites.
Phase 1 builds a walking skeleton that proves the framework, the harness, the
crypto seam, and the inheritance mechanism on one green format. Phase 2 completes
the framework and ports all of Fulu in staged green gates. Phase 3 adds Gloas as
the diff. Phase 4 hardens to both presets, the full vector suite, and CI. Phase 5
is the deferred proof package, listed so the constraints that keep it reachable
stay visible. The driving principle is the one SizzLean's own plan used: validate
against the upstream vectors before investing in proofs, because proving a wrong
implementation right is the most expensive failure mode.

No time estimates. These depend on developer capacity and on how much of the
toolchain (the deriving-handler internals, the per-worker Lean server, the
`pytest-xdist` fixtures) needs discovery versus is already familiar.

---

## Background for the implementor

This section is the context an implementer needs who has not followed the design
discussion. Read the three design documents first; they are the design of record
and this plan only sequences them. Read `SPEC_AUTHORING_MODEL.md` for the
author/framework contract, the canonical glossary, and the boundary table, then
`FRAMEWORK_ARCHITECTURE.md` for the framework, then `SPECS_ARCHITECTURE.md` for the
per-fork specs. `CLAUDE.md` at the repository root binds the writing and code style.

**The repository.** A Lake monorepo of packages under `packages/`, coordinated by an
umbrella `lakefile.toml` that pulls each in with a `[[require]]` block. The toolchain
is pinned in `lean-toolchain` (Lean v4.29.1); CI reads it. Build with `lake build`
from the root (the umbrella), `lake build <Lib>` for one library, or
`cd packages/<Name> && lake build` per package. Add `EthCLLib` and `EthCLSpecs` to
the umbrella requires; keep `EthCLProofs` out, the way `LeanPoseidonProofs` is kept
out, so mathlib stays off the main build.

**The dependency graph.** `EthCLLib` requires `SizzLean` (the SSZ machinery; it
transitively pulls in `LeanHazmatSha256`, the FFI SHA-256), `LeanHazmatBls`, and
`LeanHazmatKzg`. `EthCLSpecs` requires `EthCLLib`. `EthCLProofs` (deferred) requires
`EthCLSpecs` and mathlib, standalone.

**What SizzLean provides.** The `SSZRepr` class and its `deriving SSZRepr` handler;
`Box`, the cache, `hashTreeRoot`; the generic `sszGet` / `sszUpdate` access macros;
the `Hasher` class with the `Sha256` (FFI) and `Sha256Spec` (pure-Lean) tags; and the
box flavour constructors. The flavour constructors are `CachedBox H` (cached) and
`UncachedBox H` (uncached), generic over the hasher tag; `FastBox` and `PureBox` are
the `Sha256`-pinned aliases (`FastBox = CachedBox Sha256`). The preset-resolved
symbolic-cap derive (Phase 0.1) is already landed in SizzLean.

**What the crypto packages provide.** `LeanHazmatBls` exposes BLS `verify`,
`fastAggregateVerify`, and aggregation. `LeanHazmatKzg` exposes the KZG primitives;
the PeerDAS cell verifier is `verifyCellKzgProofBatch`, a batch over arrays of
commitments, cell indices, cells, and proofs, not a single-cell call. The framework
wraps both behind the `[CryptoBackend]` seam.

**The vectors and the spec source.** Conformance runs against the upstream
`consensus-spec-tests`, downloaded per `pyspecPinnedVersion`. The repository's
existing `scripts/run_conformance.py` pins `v1.7.0-alpha.10`; the implementation bumps
to the current latest release at start and confirms the tag carries Gloas vectors.
The archive layout is `tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>/`; the
preset and fork live in the path, and each case carries a `meta.yaml`
(`bls_setting`, `blocks_count`, the `transition` format's `fork_epoch`). The spec
behavior comes from the consensus-specs build, which flattens the layered markdown
into a generated `fulu` (and `gloas`) Python module; port from that generated Python
as the authoritative executable form, reading the markdown for intent. Fulu is the
accumulated spec through Electra plus EIP-7594 PeerDAS; Gloas is EIP-7732 ePBS as a
diff over Fulu. Two presets exist: `minimal` (small, for fast iteration) and
`mainnet` (large, slow, on demand). The hand-written `GloasSpec` package is a design
reference only; it ran `minimal` against a local checkout, never a downloaded
archive, and never had the framework, inheritance, or the long-lived server.

---

## How to record implementation findings

The implementor does not edit the four design documents (`SPEC_AUTHORING_MODEL.md`,
`FRAMEWORK_ARCHITECTURE.md`, `SPECS_ARCHITECTURE.md`, and this `PLAN.md`) during
implementation. They are the design of record and stay stable, so a reviewer can
compare what was planned against what happened.

Instead, the implementor keeps an `IMPLEMENTATION_NOTES.md` in this directory and
records there:

- **Every deviation from this plan**, with the reason: a phase resequenced, a
  deliverable dropped or added, an acceptance gate that had to change.
- **Every place reality diverged from the design docs**: a decision that had to be
  revised, an assumption that proved wrong (a spike that failed, an FFI signature
  that differed, a Lean idiom that did not behave as the docs expected), and how it
  was resolved.
- **Remarkable findings**: a mainnet performance surprise, an upstream vector that
  contradicts the spec text (which also goes in `DISCREPANCIES.md`), a tricky
  elaboration or termination issue, a framework gap a fork surfaced.

At the end of the milestone, `IMPLEMENTATION_NOTES.md` is reviewed and its confirmed
changes are folded back into the design docs in one controlled pass. This keeps the
docs from drifting under in-flight edits and gives a single audit trail of plan
versus reality.

---

## Cross-phase dependencies

These dependency edges shape the whole sequence. State them once here; the phases
reference them rather than re-deriving them.

| Dependency | Why | Gates |
|---|---|---|
| The SizzLean preset-resolved symbolic-cap derive blocks `forkcontainer` | a container is `[Preset]`-parameterized and its field widths are `Const.*` projections that stay symbolic until the preset resolves; `SSZRepr` has to derive over those caps and reduce once `[Preset]` is concrete | the container front-end (Phase 1) |
| The three spikes gate building on the mechanisms they confirm | the fork-inheritance replay, the `[CryptoBackend]` instance, and vector acquisition plus SSZ decode are load-bearing pieces chosen but not yet exercised; a wrong assumption found after the framework is built is expensive to unwind | `forkdef` / `forkcontainer` / `inherit`, every crypto-gated step, and the whole harness input edge (Phase 1 onward) |
| The walking skeleton must be green before Fulu broadens | one green format end-to-end through the per-worker Lean server proves the framework, the harness, the crypto seam, and the inheritance on the smallest surface; broadening onto unproven plumbing multiplies debugging cost | the full Fulu port (Phase 2) |
| Mainnet performance is smoke-tested once the core transition is green | "both presets from day one" is true at the type level; performance is not, mainnet states are far larger and exercise the cache and FFI hasher on bigger trees | the mainnet hardening (Phase 4) |

The package each phase touches:

| Phase | Primary package | Also touches |
|---|---|---|
| 0, foundations and spikes | SizzLean (the prerequisite), `EthCLLib` (the spikes) | the spike fixtures, the Python acquisition |
| 1, the walking skeleton | `EthCLLib` and `EthCLSpecs` | the `pytest-xdist` harness, the `pyspec_server` exe |
| 2, full Fulu | `EthCLLib` and `EthCLSpecs` | the harness for the broadened format set |
| 3, the Gloas diff | `EthCLSpecs` | `EthCLLib` only if a Gloas need surfaces a framework gap |
| 4, hardening | `EthCLSpecs` and the CI config | the harness, `DISCREPANCIES.md` |
| 5, proofs (deferred) | `EthCLProofs` | nothing in the shipping path |

---

## Phase 0: Foundations and spikes

De-risk the machinery that is chosen but not yet exercised, and land the
prerequisite the container front-end needs, before building anything on top. Four
pieces of work, independent of each other and parallelizable.

### 0.1 The SizzLean preset-resolved symbolic-cap derive

**Goal.** Make SizzLean's `deriving SSZRepr` handler accept a
`[Preset]`-parameterized container whose collection caps are `Const.*` projections
rather than `Nat` literals, and reduce those caps once the preset instance is
concrete. This is the one substantive dependency-side piece the container front-end
calls out, and it blocks `forkcontainer`.

**Acceptance.** The SizzLean derive accepts a symbolic-cap container, the fixture
builds, and its root plus an `sszUpdate` reduce at a concrete preset by `rfl` or
`native_decide`.

**Status.** Landed in SizzLean ahead of this plan; the design docs refer to it as the
already-landed change. Listed as the explicit prerequisite so the dependency edge is
on the page.

### 0.2 The fork-inheritance replay spike

**Goal.** Confirm the one remaining unverified piece of the inheritance mechanism:
that capturing an author's raw body syntax and re-elaborating it in a child namespace
makes the body's unqualified sibling calls late-bind to the child's overrides,
reading the current namespace and the lineage recorded at the `inherit` site.

**Deliverables.**
- A minimal `fork Base` / `fork Child from Base` pair with a captured `forkdef`
  caller that calls a sibling, the sibling overridden in `Child`, and an `inherit` of
  the caller into `Child`.
- A `#guard` that the inherited caller in `Child` dispatches to `Child`'s override,
  the open-recursion case the design says a copy or an alias would get wrong.
- A note recording what the replay reads and that no blanket hygiene override was
  needed.

**Acceptance.** The toy compiles and the `#guard` confirms late binding: `Child`'s
inherited caller resolves the sibling to `Child`'s override, not `Base`'s. The result
is documented.

### 0.3 The `[CryptoBackend]` instance spike

**Goal.** Confirm the `[CryptoBackend]` seam binds cleanly over the committed crypto
FFI, for both the signature and the commitment primitives, so the signatures, the
byte-buffer types, and the instance resolution are known good before the spec calls
the backend through the seam.

**Deliverables.**
- A `[CryptoBackend]` instance whose `verify` and `fastAggregateVerify` delegate to
  `LeanHazmatBls` and whose `kzgVerifyCellProofBatch` delegates to `LeanHazmatKzg`'s
  `verifyCellKzgProofBatch` (the batch array shape, not a single-cell call).
- A toy step that calls `CryptoBackend.verify` through the instance, never the FFI
  directly, with a `#guard` over a known BLS vector and a `#guard` over a known KZG
  cell-proof-batch vector, so both arms of the seam are exercised.
- A note on the buffer marshalling at the seam (pubkey, message, signature in, `Bool`
  out; the array shapes for KZG) and on the `bls_setting: 2` verify-off mode the
  audit needs.

**Acceptance.** The spike compiles, the toy step resolves the instance, and both a
known BLS vector and a known KZG cell-proof-batch vector verify through the seam. The
marshalling is documented.

### 0.4 The vector-acquisition and decode spike

**Goal.** Confirm the harness input edge that everything downstream depends on:
download a real `consensus-spec-tests` archive at the candidate pin, walk the case
layout, and decode a real case into a SizzLean box.

**Deliverables.**
- A script step that fetches the archive at the candidate `pyspecPinnedVersion`
  (bumped to the current latest release) and confirms a Gloas archive exists at that
  tag, falling back to a documented dev commit if not.
- A decode of one real `sanity/blocks` minimal Fulu pre-state, and one Gloas case,
  from `.ssz_snappy` into a container through SizzLean's `SSZRepr`, confirming the SSZ
  round-trips and the `meta.yaml` (`bls_setting`, `blocks_count`, `fork_epoch`) parses.

**Acceptance.** A real pre-state decodes into a box, the SSZ round-trips, and the
case layout plus `meta.yaml` parse as expected. The chosen pin is confirmed to carry
both forks' vectors, or the fallback is documented.

### Phase 0 exit gate

The SizzLean derive accepts a symbolic-cap container; the inheritance-replay spike
confirms late binding; the crypto-backend spike verifies a BLS and a KZG vector
through the seam; the acquisition spike decodes a real vector. Each result is written
down, so the assumptions the framework builds on are confirmed rather than presumed.

---

## Phase 1: The walking skeleton

Build just enough framework and the thinnest Fulu slice to take one vector format
green end-to-end, through the per-worker Lean server, at the minimal preset. This
phase validates the framework, the harness, the crypto seam, and the inheritance
mechanism on the smallest surface, so Phase 2 broadens onto plumbing that already
works.

### 1.1 The framework skeleton (`EthCLLib`)

**Goal.** Stand up the framework's load-bearing core: the parts every later step and
container depend on, and nothing more.

**Deliverables.**
- The namespace layout: the `EthCLLib` top namespace, the `EthCLLib.Spec`
  author-facing sub-namespace with the `fork*` forms and `inherit` as `scoped`
  syntax, the header macros, `assert` and the step primitives, the `Const` surface,
  and the spec-facing helpers; the generic driver under `EthCLLib.PySpecTests`; the
  internals under `EthCLLib.Internal`.
- The capturing declaration forms over the one capture base: `forkdef`,
  `forkcontainer`, `forkstruct`, the `fork … from …` lineage environment extension,
  and `inherit` as the single consumer.
- The header macros: `state_preamble` (declaring the `State` abbrev and the
  concrete-domain `modifyState`, once per fork) and `state_section` /
  `fork_choice_section` (each opening its own `section` and emitting the selector
  classes, the monad variable, and the three raw `Monad` / `MonadStateOf` /
  `MonadExceptOf` constraints over `State` or `Store map`).
- The two error types: `StateTransitionError` (`assert`, `todo`, `outOfBounds`) and
  `StoreTransitionError` (`assert`, `todo`, `missingKey`, `transition`).
- The tier system: `Preset` and `Config` as instance-implicit classes, the universal
  tier, all three unified under one `Const` namespace.
- The state representation: `State := Box HasherTag.H BeaconState`, the `[HasherTag]`
  selector class, the flavour anchor using `CachedBox HasherTag.H` (the fast config's
  `FastBox`) and `UncachedBox HasherTag.H` (the pure config's `UncachedBox Sha256Spec`),
  and the access primitives `sszGet` / `sszUpdate` / `modifyState` / `getStateRoot` over
  SizzLean's generic macros.
- The fork-interface typeclass, defined whole here. It is framework-owned and
  fork-agnostic, so the full set of entry-point signatures is fixed in this phase; a
  fork satisfies it by implementing the driven entries and stubbing the rest as
  documented `todo`s. Defining it whole now makes the Phase 2 sub-phases additive
  (fill stubs) rather than interface-editing.
- The generic `PySpecTests` driver written against that interface: the
  fold-compare-root driver and the single-step runner, decoding through `[SSZRepr]`,
  dispatching by format, comparing by root, classifying by error constructor.

**Acceptance.** `lake build EthCLLib` is green; the header macros put the right things
in scope; the capture/replay resolves to a child's override in a self-test that
graduates the Phase 0.2 spike into `EthCLLib`; and a scratch step written through
`state_section` actually *runs* at the fast config `EStateM StateTransitionError
(Box Sha256 BeaconState)`, round-tripping one `sszGet` / `sszUpdate` / `assert`, so
the generated header plus `[HasherTag]` plus `EStateM`-over-a-box composition is shown
to execute, not merely typecheck.

### 1.2 The thinnest Fulu slice (`EthCLSpecs`)

**Goal.** Author the smallest spec surface one format can drive: a couple of
containers, the foundations they need, and one operation handler.

**Deliverables.**
- `EthCLSpecs.Fulu` foundations: the `Types` aliases and the `Constants` the slice
  references, with `minimal` as an injected `@[reducible]` `[Preset]`.
- Two or three containers through `forkcontainer`, enough to type the handler's input
  and the state field it touches.
- One operation handler as a `forkdef` over `StateTransition`, implemented (not a
  `todo`), with a crypto gate that calls `CryptoBackend.verify` through the seam.
- The fork-interface instance for `EthCLSpecs.Fulu`, satisfying the whole interface:
  the driven handler implemented, every other entry a documented `todo`.
- `pyspecPinnedVersion` for Fulu, at the current latest release.

**Acceptance.** `lake build EthCLSpecs` is green, the fork-interface instance
typechecks, and the driven handler is exercised by a Lean `#guard` over one hand-built
input before the Python harness exists, so behavior is confirmed independently of the
harness plumbing.

### 1.3 The runner exe and the harness

**Goal.** Wire the Python side and the long-lived Lean server so a vector flows from
disk to a green result.

**Deliverables.**
- The request/result protocol design between the Python worker and the Lean server:
  the wire framing, the request encoding (the vector bytes plus `bls_setting`,
  `blocks_count`, and the `transition` `fork_epoch`), the result encoding (the
  classify bucket and the reject reason), and the crash-recovery contract, a server
  that dies on a malformed request re-spawns and the in-flight case reports failed
  rather than hanging the worker.
- The `pyspec_server` exe in `EthCLSpecs`, instantiating the generic driver at `Fulu`
  and running the request/result loop, keeping its crypto cache warm across requests.
- The Python harness: acquisition of the archive for `pyspecPinnedVersion`, the
  case-tree walk, `meta.yaml` parsing, and a `pytest-xdist` runner where each worker
  holds one server through a `session`-scoped fixture.
- The classify-bucket reporting: passing, expected rejection, out-of-scope `todo`,
  likely-bug (`outOfBounds` / `missingKey`).

**Acceptance.** One format, the single-operation handler the slice implements, is
green end-to-end at the minimal preset, driven through a per-worker Lean server.
At least two requests flow through one warm server (proving the loop and the warm
cache, not just a single round-trip), and a deliberately malformed request exercises
the crash-recovery path (the server re-spawns, the case reports failed). A `todo` that
a vector reaches fails loudly rather than passing silently, proving the deferral
safety net works.

### Phase 1 exit gate

One format runs green end-to-end at minimal through the per-worker Lean server, with
warm-server reuse and crash recovery exercised. The framework skeleton builds, the
fork-interface instance typechecks and the driven handler runs, the crypto seam
verifies through the backend, and the inheritance replay resolves to a child's
override in a self-test. The four things this phase validates, framework, harness,
crypto seam, and inheritance, are confirmed on the smallest surface.

---

## Phase 2: Full Fulu

Complete the framework and port the whole accumulated Fulu spec. Fulu is the heavy
lift: the entire accumulated state transition and fork choice as of Fulu, Phase 0
through Electra's machinery plus Fulu's PeerDAS. Because it is the bulk of the work,
it lands in staged sub-phases, each with its own green gate and its own
reject-faithfulness audit, rather than one terminal "all green" gate. The port is
driven off the generated `fulu` Python, with the markdown read for intent. The
`todo` work-queue runs throughout: author a step, leave its not-yet-wired branches as
`todo`, run the subset, and let classify mode point to the `todo`s a vector hits.

### 2.1 Complete the framework (`EthCLLib`)

**Goal.** Build out the framework parts the skeleton did not need, so the full spec
has every primitive it calls.

**Deliverables.**
- The arithmetic layer: `UInt64` operations transcribing the pyspec's operation order
  faithfully, `umax`, `umin`, `isqrt`, the type-directed `uintToBytes` width, and the
  `Nat`-narrowing path for the rare intermediate above `2^64`.
- The crypto layer: the hashing-based primitives `computeForkDataRoot`,
  `computeDomain`, `computeSigningRoot`, and `isValidMerkleBranch`; the full
  `[CryptoBackend]` class with the caching FFI backend (keyed by the full serialized
  input per primitive), the symbolic backend, the `bls_setting: 2` verify-off mode,
  and the batch KZG cell verifier.
- The control-flow combinators: the `Step` done/next type with `fuelLoop` (monadic) and
  `fuelIterate` (the pure walk for linear DAG descents), with the per-loop decision rule
  documented.
- The finite-map and fork-choice store: `MapKind`, the `FcMap` operation class
  (`insert`, `lookup`, `contains`, `fold`, `keys`), the `treeMap` and `hashMap`
  instances, and the `Store` over `forkstruct`.
- The full `PySpecTests` driver set: the step/check interpreter for `fork_choice`
  alongside the fold-compare-root and single-step drivers; the `runStateTransition`
  nested-machine bridge.
- The forms' edge cases: an inherited container whose field type or capacity cap
  names an overridden symbol, the preamble-in-scope behavior, and legible
  author-error reporting.

**Acceptance.** `lake build EthCLLib` is green with the full primitive set, and the
framework self-tests pass: map-backing equivalence (`hashMap` equals `treeMap` on
`FcMap` results), crypto-cache transparency, and inheritance-macro dispatch.

### 2.2 Core transition green (the fold formats)

**Goal.** Port the spine, foundations, the component containers, `BeaconState`, the
state-operation concern files in dependency order, and the `Transition` pipeline, then
take the fold-driver formats green.

**Deliverables.** The `Types` / `Constants` foundations; the component-container files
in topological order with their pure predicates colocated; `BeaconState`; the
state-operation concern files split by concern with no `Base` catch-all, resolving the
read/write seam so the import graph stays acyclic; the `Transition` pipeline. A
mainnet performance smoke run: one `sanity/blocks` mainnet case through the warm
server, measuring wall-time and memory and confirming the `@[reducible]` mainnet
widths reduce without blowing up compile time, so any performance cliff is found here,
not in Phase 4.

**Acceptance.** `sanity/slots`, `sanity/blocks`, `finality`, and `random` are green at
minimal. The reject-faithfulness audit for these formats holds (no `outOfBounds` on a
valid vector, every invalid vector rejected by `assert` at the pyspec's rejection
point). The mainnet smoke run is measured and either acceptable or its fallback
(sharding, a shared cache, `Task` parallelism) is identified.

### 2.3 Single-step formats green

**Goal.** Take the formats that drive one handler in isolation green.

**Deliverables.** The full `EpochProcessing` substep set in the generated-`fulu`
order; the `Operations` handlers including `processSyncAggregate` (which exercises
`fastAggregateVerify` through the seam); the reward and penalty delta functions of the
`Rewards` concern.

**Acceptance.** `epoch_processing/*`, `operations/*`, and `rewards/*` are green at
minimal, and their reject-faithfulness audit holds. Every `todo` in this slice is
documented as unreachable in scope.

### 2.4 Genesis and data availability green

**Goal.** Port the genesis lifecycle and the PeerDAS data-availability surface, which
is the first real use of the KZG backend through the seam.

**Deliverables.** `Genesis` (`initializeBeaconStateFromEth1`, `isValidGenesisState`);
`DataAvailability` (`isDataAvailable`, the KZG cell-verify glue over the batch
verifier), authored after the core transition so the transition passes vectors while
the KZG backend comes online behind the seam.

**Acceptance.** `genesis` is green at minimal and the KZG cell-verify paths are
exercised through the seam, with the audit holding for these paths.

### 2.5 Fork choice green

**Goal.** Port the second state machine: the `Store` accessors, the recursive read
layer, and the handlers.

**Deliverables.** The fork choice (`Store` accessors, `Weight`, `Head`, `Handlers`),
with the read layer pure and the `on_*` handlers monadic, `onBlock` running the state
transition through `runStateTransition`, and the recursive walks given their
per-loop termination strategy.

**Acceptance.** `fork_choice` is green at minimal, exercising the step/check
interpreter and the nested-machine bridge, with the audit holding.

### Phase 2 exit gate

Every in-scope format for Fulu is green at minimal: `sanity/blocks`, `sanity/slots`,
`finality`, `random`, `epoch_processing/*`, `operations/*`, `rewards/*`, `genesis`,
and `fork_choice`. The reject-faithfulness audit, run incrementally per sub-phase,
confirms the spec rejects for the same reason the pyspec does, not by a coincidental
downstream bounds error. The `todo`s are documented as unreachable in scope. The
mainnet smoke run has cleared the performance unknown or identified its fallback.
Fulu is the whole base Gloas will diff.

---

## Phase 3: The Gloas diff

Add Gloas as a diff over Fulu through the inheritance mechanism. The Gloas manifest of
inherited, overridden, and new declarations is derivable by diffing the generated
`fulu` and `gloas` Python modules. This phase touches `EthCLSpecs` almost entirely; it
reaches into `EthCLLib` only if a Gloas need surfaces a framework gap.

**Deliverables.**
- `fork Gloas from Fulu` in the Gloas root module, recording the lineage edge.
- The inherit-or-rewrite container manifest: `inherit` for every unchanged container;
  full `forkcontainer` redeclarations for `BeaconState` (replacing
  `latestExecutionPayloadHeader` with `latestBlockHash` in place, then the ePBS
  fields) and `BeaconBlockBody` (dropping `executionPayload`); fresh declarations for
  the ePBS containers (`Builder`, `BuilderPendingPayment`, `BuilderPendingWithdrawal`,
  `ExecutionPayloadBid`, `PayloadAttestation`, and the rest).
- The ePBS steps and helpers: the builder-registry accessors, the
  payload-timeliness-committee (`ptcWindow`) accessors, `processPayloadAttestation`,
  the `executionPayloadAvailability` tracking, and the restructured `processBlock`
  override whose step order changes because the payload is revealed separately.
- The inherited declarations through `inherit`, with the section header and constants
  in scope at the `inherit` site; the payload-aware fork-choice `Store` fields through
  a full `forkstruct` redeclaration.
- `upgradeToGloas : Fulu.State → Gloas.State`, the single sanctioned cross-fork
  reference, living in Gloas and importing Fulu.
- The Gloas tier additions: `PTC_SIZE` to the preset tier, `BUILDER_REGISTRY_LIMIT` to
  the universal tier, `GLOAS_FORK_EPOCH` to the config tier, inherited and appended.
- The fork-interface instance for `EthCLSpecs.Gloas`, with `upgradeToGloas` wired in;
  `pyspecPinnedVersion` tracking the tag while Gloas is unreleased.
- The `fork` and `transition` formats wired Fulu-to-Gloas only, the `transition`
  format applying `upgradeToGloas` mid-fold at the per-case `meta.yaml` `fork_epoch`.

**Acceptance.** The Gloas formats are green at minimal: every in-scope format Fulu
runs, plus `fork` and `transition` for the Fulu-to-Gloas upgrade. The hard inheritance
case is gated specifically: a declaration that Gloas `inherit`s unchanged, but whose
body transitively calls a sibling Gloas overrode, late-binds to Gloas's override,
confirmed by a vector that exercises it. If no such inherited-caller-over-overridden-
sibling case exists in the real Gloas diff, that is recorded, and the Phase 0.2 toy
spike stands as the only coverage.

---

## Phase 4: Hardening

Take both forks to the mainnet preset and the full vector suite, wire CI, and close
the `todo`s so no in-scope vector lands on one. The mainnet performance unknown was
smoke-tested in Phase 2.2, so this phase scales a known-feasible path rather than
discovering it.

**Deliverables.**
- The mainnet `[Preset]` instance as an injected `@[reducible]` `def`, selected per
  test, coexisting with `minimal` without clashing.
- The full vector suite at both presets for both forks: minimal on every push,
  mainnet on demand or sharded.
- The CI jobs: `lake build` over `EthCLLib` and `EthCLSpecs` (compiling everything and
  running the Lean unit self-tests at build), plus a separate `pytest-xdist`
  conformance job that can run sharded or on demand.
- The per-fork `DISCREPANCIES.md`, keyed by vector id, each entry carrying the vector
  id, the spec-text citation, and the upstream issue link.
- The `todo`s closed: every crypto-gated or unimplemented branch a mainnet or
  full-suite vector reaches is filled in, so no in-scope vector lands on a `todo`.

**Acceptance.** Both presets are green on the full in-scope suite for both forks, and
CI is green: `lake build` plus the `pytest-xdist` conformance job. The
reject-faithfulness audit holds at mainnet as at minimal. `DISCREPANCIES.md` records
any logged spec-wins divergence with a citation.

---

## Phase 5: Proofs (deferred)

Out of scope for the first milestone. Listed so the constraints that keep it reachable
stay visible, and so the earlier phases hold the proof-friendly discipline that makes
this phase reachable without rework. When proofs begin, the standalone `EthCLProofs`
package is created, requiring `EthCLSpecs` and mathlib, held out of the umbrella the
way `LeanPoseidonProofs` is, so mathlib never reaches the framework, the specs, the
runner, or the conformance path.

**The configuration.** Proofs run only at the pure configuration: `UncachedBox
Sha256Spec` (uncached, so the getter-setter laws hold by `rfl`), the pure
`StateTransition` monad (`StateT` over `Except`), and `treeMap` (deterministic key
order, relevant only to fork-choice proofs). The fast configuration is never a proof
target; conformance establishes it empirically, and the fast-versus-pure gap is closed
at the dependency level by SizzLean's cache-coherence test and the FFI-equivalence
axioms, so there is no spec-level fast-equals-pure theorem.

**The candidate theorems.** Per fork, invariant preservation and happy-path
correctness, each proved per fork because inheritance is by symbol. A theorem is itself
a declaration, so it can ride the inheritance replay into the child namespace: an
unchanged inherited chain re-checks cheaply and the proof cost concentrates on the
diff. The techniques are the gate-split on `assert` conditions and the abstract
`[CryptoBackend]`, with arithmetic lifted to `Nat` through the correspondence lemmas.

**The discipline that keeps it reachable.** The earlier phases hold this so Phase 5
needs no rework: every spec function is total, with `fuelLoop` or well-founded
recursion in place of `partial def`; the uncached box instance stays `@[reducible]`;
no `IO` lives inside `State` or `Box`; indexed access carries an explicit bound proof
rather than `arr[i]!`; `native_decide` stays out of `@[simp]` lemmas; and the pure
path uses `treeMap`. These are the seven anti-patterns of the proof-support layer,
avoided in every definition from Phase 1 forward.

**Acceptance.** Out of scope for the first milestone. The constraints above are the
deliverable for the earlier phases: a spec body that stays proof-agnostic and
proof-friendly, so the candidate theorems can be added later without touching the
shipping path.

---

## Cross-cutting concerns (apply to every phase)

- **Literate by default** (CLAUDE.md). Every new `*.lean` file opens with a
  `/-! … -/` module docstring framing it against the spec section it implements, for
  both Lean-fluent and pyspec-fluent readers; every public declaration carries a
  *why*-docstring; each author-facing form gets an `example` block.
- **One spec body, two configurations.** The spec body stays generic over the preset,
  the hasher tag, and the monad, naming neither configuration. The runner instantiates
  `fast`; `EthCLProofs` instantiates `pure`.
- **The domain line, build-enforced.** `EthCLLib` cannot import a spec module, because
  a separate package cannot import what it does not require. No framework primitive
  names a validator, an epoch, a balance, or a `State`.
- **`set_option autoImplicit false` per file**, with `open` and `set_option` tight to
  the section that needs them.
- **No `sorry` in committed code** without a `TODO` and a tracking note. A spec `todo`
  is the typed deferral constructor, a different thing, allowed with its documented
  unreachable claim.
- **No committed `#eval` / `#check` / `#print`.** Use `example : … := by …` or `#guard`
  for build-time assertions.
- **Findings go in `IMPLEMENTATION_NOTES.md`, not the design docs** (see above).

## Status snapshot

| Phase | Package | Status |
|---|---|---|
| 0: Foundations and spikes | SizzLean, `EthCLLib` | preset-cap derive landed; the three spikes pending |
| 1: The walking skeleton | `EthCLLib`, `EthCLSpecs` | pending |
| 2: Full Fulu | `EthCLLib`, `EthCLSpecs` | pending |
| 3: The Gloas diff | `EthCLSpecs` | pending |
| 4: Hardening | `EthCLSpecs`, CI | pending |
| 5: Proofs (deferred) | `EthCLProofs` | out of scope for the first milestone |
