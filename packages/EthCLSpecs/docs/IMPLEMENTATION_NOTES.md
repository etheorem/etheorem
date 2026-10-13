# EthCLSpecs: Implementation Notes

The as-built companion to the four design documents in this directory
(`SPEC_AUTHORING_MODEL.md`, `SPECS_ARCHITECTURE.md`, `FRAMEWORK_ARCHITECTURE.md`, and
the glossary). Those four are the design of record. This file records how
`EthCLSpecs` / `EthCLLib` realize them: the current architecture, the places the code
deviates from a doc (with the reason), and the spec-faithfulness decisions worth
knowing. Everything here describes the tree as it stands against the
`v1.7.0-alpha.11` pin.

## Scope and conformance

Three forks, **Fulu**, **Gloas**, and **Heze**, against the `consensus-spec-tests` minimal and
mainnet archives at `v1.7.0-alpha.11` (the latest release with cut vectors; it is
flagged pre-release, so the harness pins the tag explicitly rather than reading `gh
release latest`). The full in-scope suite is green at both presets for all three
forks, `--subset=0`, zero failures and zero `xfail`:

| | minimal | mainnet |
|---|---|---|
| Fulu  | **5188 passed** | **847 passed** |
| Gloas | **6573 passed** | **1034 passed** |
| Heze  | **6770 passed** | **997 passed** |

Fulu's collected formats: `epoch_processing`, `operations` (including the standalone
`execution_payload`), `rewards`, `sanity/blocks`, `sanity/slots`, `finality`,
`random`, `fork_choice` (including the PeerDAS data-availability `on_block` cases and
`get_proposer_head`). Gloas adds `fork`, `transition`, and the full ePBS
`fork_choice`. `DISCREPANCIES.md` records no open vector discrepancy: every vector the
implemented formats reach matches by root or rejects faithfully. Deliberate divergences
from the spec *text* that no vector observes are catalogued per fork in this file.

**Out of scope** (deselected in `walk_cases`, not collected):

- **Fulu `fork` / `transition`** (Electra→Fulu): the upgrade and the pre-fork Electra
  blocks both need a complete Electra parent fork the library never builds. The
  **Gloas** `fork` / `transition` (Fulu→Gloas) and the **Heze** ones (Gloas→Heze)
  are in scope and green.
- **`light_client`, `networking`, `merkle_proof`, `sync`**: not state-transition or
  fork-choice formats; outside `IN_SCOPE_RUNNERS`.
- **`genesis`**: no vectors at the pin (see Genesis below).

**CI.** The `ethcl` job in `lean_action_ci.yml` runs `just ethcl-test` (builds all
four libraries, firing the framework and spec self-tests) and `just
ethcl-pyspec-smoke` (the `pytest-xdist` dev subset at minimal for all three forks
through the per-worker `pyspec_server`). It is green iff no in-scope vector hits a
bug-smell or a real mismatch. Mainnet and the full sweep run on demand
(`--preset=mainnet`, `--subset=0`).

## Inheritance and capture

The capture/replay mechanism lives in `EthCLLib.Internal.Capture` (two
`SimplePersistentEnvExtension`s: `lineageExt` for `fork … from …` edges, `captureExt`
for the raw declaration bodies), `EthCLLib.Spec.Forms` (the `fork` / `forkdef` /
`forkabbrev` / `forkinstance` / `forkcontainer` / `forkstruct` / `inherit` command
elaborators), and `EthCLLib.Spec.Tiers` (the four `Preset` / `Config` forms).
`inherit Foo` walks `lineageExt` from the current namespace strictly upward and
replays the nearest ancestor's captured `Foo` in the current namespace, re-emitting
whichever declaration kind the capture recorded. The body is the
author's own un-stamped syntax, spliced by quotation, so its sibling identifiers
late-bind at the child site by ordinary name resolution. Antiquoting pre-existing
syntax adds no macro scopes, so no blanket hygiene override is needed.

- **The `fork` keyword reserves the token `fork`.** A `scoped syntax "fork " …` makes
  `fork` a keyword in every module that opens `EthCLLib.Spec`, so a binding named
  `fork` fails to parse. The captured-declaration field is `forkNs`, and elaborators
  use `forkNs` locals. Spec authors must not name a binding `fork`.
- **`fork` identity is the current namespace; the parent is the sibling.** `fork Gloas
from Fulu` records `(currNamespace, currNamespace.getPrefix ++ Fulu)`, which assumes
  both forks share a prefix (`EthCLSpecs.Fulu`, `EthCLSpecs.Gloas`), as
  `SPECS_ARCHITECTURE.md` §3.4 mandates. The `Name` argument is documentation; identity
  comes from the namespace.
- **`inherit` is a pure consumer** and never re-captures, so a grandchild walks past an
  unchanged intermediate fork to the nearest ancestor that captured the symbol.
- **Capture keys split the namespace at the nearest registered fork.** Constants sit
  inside `namespace Const` within the fork, so keying on the raw `currNamespace` would
  file them under `EthCLSpecs.Fulu.Const`, which is no fork and which no lineage walk
  reaches. `captureKey` walks the namespace's prefixes against `lineageExt`, nearest
  prefix winning, and stores the residual path as the name, so a `forkabbrev` written
  in `Const` keys as `(EthCLSpecs.Fulu, Const.slotsPerEpoch)`.
- **Three elaborator properties the constant tiers rest on**, each pinned by
  `EthCLLib/Tests/ForkScoping.lean` rather than assumed:
  1. A composite `declId` scopes its body. `def Const.foo` written inside
     `namespace Gloas` lands at `Gloas.Const.foo` *and* resolves its body's
     unqualified names as if inside `Gloas.Const`, so late binding reaches into the
     sub-namespace and a replayed `Const.payloadTimelyThreshold` divides Gloas's
     `ptcSize`.
  2. Section-variable auto-binding survives a replay. `inherit` runs `elabCommand`
     from inside a command elaborator, and the surrounding `section variable
     [Preset] [Config]` is still picked up by the ordinary used-variable rule, so a
     child's inherited constants bind to the child's classes with nothing restated.
  3. Abbrev-ness survives replay, which is why `forkabbrev` exists at all. The test
     asserts it behaviourally, by synthesising an instance *through* an inherited
     alias: instance search unfolds a reducible definition and not a `def`, so a
     demotion would fail there rather than silently degrade SSZRepr synthesis.
- **`forkinstance` requires a name**, unlike Lean's `instance`. The capture key is a
  name and `inherit` has nothing else to spell. Its binders ride inside the captured
  `declSig` (`bracketedBinder* >> ": " term`), so no separate binder slot is needed;
  `forkstruct` is the one kind that fills one, since `structure` takes its parameters
  beside the field block.
- **Tier declarations merge instead of replaying.** A `Preset` / `Config` class or one
  of their value sets is a single declaration, so `inherit` cannot fuse two of them and
  refuses a tier capture outright. The child's own `forkpreset` / `forkconfig` /
  `forkpresetvalues` / `forkconfigvalues` collects the ancestors' captured blocks along
  the lineage, merges by entry name (child-most-wins, ancestor order preserved), and
  emits one flat declaration. A fork that adds no field still writes the bare form, so
  the class it emits is its own.
- **The downgrade bridge needs its own namespace, not just `scoped`.** A fork's body
  files sit *inside* the fork's namespace, where a `scoped` instance is already active,
  so `scoped instance … : Fulu.Preset` in `EthCLSpecs.Gloas` would be reachable from
  every Gloas module. The generated bridge lands in `EthCLSpecs.Gloas.Downgrade`
  instead; `Upgrade.lean` and `Interface.lean` write `open scoped Downgrade`, and
  nothing else can satisfy a parent-class constraint. The instances still resolve
  `Preset` and its projections, since the fork's namespace encloses the sub-namespace.
- **Gloas re-declares Fulu's unchanged component containers with `inherit`**
  (`Gloas.Inherited`, 28 types in dependency order: `Checkpoint`, `Validator`,
  `Attestation`, the slashing / deposit / exit evidence, the sync structures, the
  pending-queue records) rather than reaching across the fork boundary for them. Each
  replays Fulu's field block in the `EthCLSpecs.Gloas` namespace, so `Gloas.Validator` is
  a fresh structure with Fulu's exact fields, hence Fulu's exact SSZ encoding and Merkle
  root, and the fork is a complete, flat namespace (`SPECS_ARCHITECTURE.md` §3.4). The
  price falls at the upgrade boundary: `upgradeToGloas` converts each Fulu component value
  to its Gloas twin field-by-field (`cvValidator`, `cvCheckpoint`, …, with SizzLean's
  `SSZList.mapCap` for the list-typed fields), since `Gloas.Validator` is a distinct type from
  `Fulu.Validator`. Dependency order (a field's type inherited before the container that
  uses it), this fork's own constants and aliases from `Gloas/Types.lean` and
  `Gloas/Constants.lean`, and current-namespace priority for the types together make
  each replayed body bind its siblings to the Gloas-local copy. A plain `def` that the capture mechanism can't replay (`addressOf`) is
  restated for the Gloas validator, the same way `balanceAfterWithdrawals` is. `inherit`
  creating a fresh type is also the right tool for declarations a fork genuinely changes
  (`BeaconState`, `BeaconBlockBody`).

## Container and struct macros

`forkcontainer` (`Forms.lean` `emitContainer`) derives `Inhabited`, `DecidableEq`,
`BEq`, `Ord`, `Hashable`, and `SizzLean.SSZRepr`. `forkstruct` (`emitStruct`) is the
plain-structure variant. It also captures and replays arbitrary bracketed binders, so
a parameterized `forkstruct Store (map : MapKind) [HasherTag]` (with the auto
`[Preset]` first) is expressible. Both take `declModifiers` so a `/-- … -/` docstring
can precede them without derailing the parse, and both emit the `deriving` in a
_separate_ `deriving instance … for` command. `Forms.lean` `import SizzLean`, so the
class names resolve as globals rather than hygiene-stamped `SizzLean.SSZRepr✝`.

`Ord` / `Hashable` derive universally now that SizzLean carries them for the collection
types (`SSZList` / `Bitvector` / `Bitlist`), so the design docs' §5 "every container"
wording holds and a map-key container (`Checkpoint`) needs no hand-written derive. The
Gloas `ForkChoiceNode` is a `forkstruct` (no SSZ derive), so it keeps its own
`deriving instance BEq, Inhabited for …`. `Root`-keyed maps still need an explicit
`Ord (Vector UInt8 32)` (`instOrdBytes32` in `Fulu/ForkChoice.lean`) for `MapKind`.

`forkstruct`'s bracketed-binder capture has two practical notes the fork-choice structs
rely on: `emitStruct` puts `[Preset]` first then the extra binders (so `Store map`
resolves with `map` the only explicit parameter), and it emits no `deriving`, so a
struct's `Inhabited` (and the map-key `Ord` / `BEq` / `Hashable`) is added by a
following `deriving instance … for …`.

## Crypto seam

`EthCLLib.Spec.Crypto` defines `CryptoBackend` (BLS `verify` / `fastAggregateVerify` /
`ethFastAggregateVerify` / `aggregatePubkeys`, KZG `kzgVerifyCellProofBatch`) over raw
`ByteArray` of the wire sizes (sk 32, pubkey 48, signature 96, blob 131072, commitment
48, cell 2048, proof 48). The class carries no SSZ dependency. `aggregatePubkeys` is a
deterministic aggregation rather than a verify gate, so it is its own member.

The single-value wire conversion is a coercion. SizzLean provides
`CoeOut (Vector UInt8 n) ByteArray` (`Repr/Instances.lean`, the canonical `⟨v.toArray⟩`),
so a `Root` / pubkey / signature is usable wherever the seam wants `ByteArray` with nothing
written at the call site. `CoeOut` is the source-keyed coercion class (the same one core
Lean uses for `Fin n → Nat`); a plain `Coe` fails here because its source is a semi-out-param
and the parametric `Vector UInt8 ?n` leaves a metavariable. The conversion fires for function
arguments, `++`, and `!=`, which covers the hashing concatenations and the fork-choice root
checks. It deliberately does not lift through `Array`, so a pubkey/commitment set keeps an
explicit `.map vecToBytes`; and the reverse direction (`bytesToVec` / `bytesToRoot`) stays an
explicit function, since it picks a length and truncates.

The spec does not call the seam directly. It calls the vector-typed wrappers: `blsVerify` /
`blsFastAggregateVerify` / `blsEthFastAggregateVerify` / `blsAggregatePubkeys` in `Crypto`
(beside the seam), and `blsVerifySigned` in `SigningRoot` (it folds in `computeSigningRoot`,
so it lives beside the helper it composes; `SigningRoot` imports `Crypto` for `blsVerify`).
Each is a thin definitional wrapper, so a wrapper call reduces to the exact seam call it
replaces. The KZG batch is called inline (its arguments are different-width vector arrays).
A gate then reads `assert (blsVerifySigned pubkey obj domain sig)`, naming the values, with
the wire-byte conversion out of the spec body.

Four backends: `ffi` (production), `verifyOff` (`bls_setting: 2`, BLS gated, KZG kept
real), `symbolic` (proofs; returns a zero 48-byte point for aggregation, never
executed), and `caching`. `caching` memoizes BLS `verify`, the repeated hot path, keyed
by the exact `(pubkey, message, signature)` wire bytes behind an `@[implemented_by]`
swap: the logical definition stays the `ffi` primitive (transparency is `rfl`, in
`Spec/Crypto.lean`), and only the compiled code consults the global memo. The runner
injects `caching`. `CryptoBackend.forBlsSetting blsSetting` is the single home for the
per-case selection (`2` → `verifyOff`, else the real backend), so a `PySpecTests` entry
point writes `CryptoBackend.forBlsSetting cmeta.blsSetting` rather than re-spelling the test.

- **Backends are `@[reducible]`.** A `def` whose result type is a class trips a lint
  unless reducible, and reducibility is what lets `native_decide` reduce the record to
  expose the FFI calls. The hasher tags (`fastHasherTag` / `pureHasherTag`) carry it
  too.
- **Inject by `@`, not a named instance argument.** `[CryptoBackend]` is an anonymous
  instance binder, so a call site picks the backend with `@f CryptoBackend.ffi …` or
  `letI`, not `(CryptoBackend := …)`.

The sync-aggregate participant set is computed one way: the bit-selected committee
pubkeys are passed to `ethFastAggregateVerify`, which aggregates whatever list it is
given. This matches the spec result for all three of its cases (all-participate,
majority-subtract, full list) and keeps the seam to `ethFastAggregateVerify` alone,
with no G1 add/neg and no precomputed-aggregate dependency.

## Engine seam

`EthCLLib.Spec.Engine` is the execution-layer sibling of the crypto seam: a spec
function whose answer belongs to an external execution client routes through a
typeclass. Unlike `CryptoBackend` these ship a global default, the optimistic instance
answering the constant `true` (the seam table in `FRAMEWORK_ARCHITECTURE.md` §1). A
local `letI` overrides it.

Three predicates cross the boundary, split across two classes by what the spec calls
them. `[ExecutionEngine]` holds the two literal `execution_engine.*` methods,
`is_inclusion_list_satisfied` (Heze) and `verify_and_notify_new_payload` (Gloas).
`[DataAvailability]` holds `is_data_available` in its Gloas-and-later form, which is a
free function whose sidecar retrieval the spec marks implementation-dependent.
Fulu's `is_data_available` predates that change and takes the columns the runner
supplies, so it checks them for real and reads no seam.

Each has a refuting pin over the branch no vector reaches: `pinRecordRefuted`
(`Heze/ForkChoice.lean`) for the inclusion-list gate, `pinEngineRefuted`
(`Gloas/ForkChoice.lean`) for the other two.

## State, presets, and the header macro

`State` is the boxed `SSZ.Box _ BeaconState`. Hashing runs through the `[HasherTag]`
seam (`sha`). The `Preset` / `Config` / `Const` three-tier constant system carries the
per-fork values; the fork interfaces are preset-parameterized (`fuluInterfaceFor (P :
Preset) (C : Config)`, `gloasInterfaceFor (P) (C) (forkVersion)`) so `minimal` and
`mainnet` instances coexist (the preset is a parameter, not a global instance), and the
runner selects fork × preset (`pyspec_server [fork] [preset]`).

- **The section header is two macros: `state_preamble` declares, `state_section` opens.**
  The split follows the seam that declarations persist across modules while `variable`s
  do not. `state_preamble BeaconState` runs once in the `State` module and declares
  `abbrev State` plus the concrete-domain `modifyState` (`State → State`); `state_section`
  opens each operation file's `section` and re-establishes the
  `[Preset] [HasherTag] [Config] [CryptoBackend]` selectors plus the monad /
  `MonadStateOf` / `MonadExceptOf` line (`[Config]` / `[CryptoBackend]` are
  instance-implicit, so they attach only to the substeps that use them). Because `State` is declared
  once in a module everyone imports, the declaration is unconditional and needs no guard;
  the variables re-emit per file because they do not persist. The fork-choice counterpart
  is `fork_choice_section map`, which emits the same selectors plus the store variables
  (`{map} [FcMap map]`, `MonadStateOf (Store map)`).
- **`modifyState` carries no binder annotation.** Its concrete `State → State` domain (the
  preamble emits it per fork, since `State` is per-fork) flows the expected type into a
  step's lambda, so `modifyState fun state => …` types `state : State` with no
  `(state : State)`. A generic framework `modifyState` could not do this: its `S` would
  be a metavariable when the `sszUpdate` macro in the body fires.

## State access, indexing, and the error model

Reads and writes go through `sszGet` / `sszUpdate`. The index accessor is chosen by three
questions: is the index _data-derived_ (supplied by a data field and not otherwise bounded), has a
validation already proved it in range, and is a reject channel in scope (a monadic step or
an `Except` query) at the read.

- **A data-derived index with a reject channel** uses `sszGetIdx` / `bitlistGetIdx`
  (`Spec/State.lean`), which build an `Except IndexError` and hand it to `liftErr`,
  surfacing `outOfBounds i xs.size` with the real index and bound (the audit's `likelyBug`
  bucket) rather than masking as a default. This covers the operation reads in a state step
  (`process_attestation`'s participation reads, `process_withdrawal_request`'s balance read,
  the pending-consolidation source reads) and the pure queries that return `Except IndexError`
  because their index is untrusted or a parameter (`get_base_reward`, `get_attesting_indices`,
  the reward-delta helpers), whose monadic callers bind them through `liftErr`.
- **An index a spec validation checks** is read through `assertH (i < size)`
  (`Spec/Assert.lean`): the assert returns the witness, so the read is the proof-carrying,
  reject-free `vs[i]'h.down`, with no default fallback, the bad index having rejected at the
  `assertH`. Plain `assert` stays the Unit-returning form for validations whose proof nothing
  downstream needs. `process_voluntary_exit`, `process_proposer_slashing`, the block-header
  proposer read, and the Gloas withdrawal sweep take this form, ten sites in all.
- **A structurally-bounded index** uses the total bang `vs[i]!` / `vget v i`, or `vmodGet`
  for a `% LEN` ring-buffer read (proof-carrying via the preset length bound). The index is
  provably in range, a `Fin n` iterating a length-`n` vector, a `for i in [0:xs.size]` loop,
  or a constant, so an out-of-range value is impossible. Making the still-total ones
  proof-carrying is the residual recorded in `FUTURE_WORK.md`.
- **A data-derived index in a pure query with no reject channel and a valid-by-construction
  index** reads total `vs[i]!`, resting on the invariant the query assumes (validators /
  balances / participation share a length; the input is well-formed). `getWeight`,
  `computeCommittee`, and the builder-registry queries keep this shape. Making it reject
  means either an `Except` return, when the index is genuinely untrusted (the first case
  above), or the proof-carrying form once the length invariants are proved (`FUTURE_WORK.md`).

`vs[i]?` is the faithful option read (`none` past the end); the `GetElem` instance uses
the real validity `i < vs.size`, so `vs[i]!` and `vs[i]?` behave like `Array`'s.

An `SSZList` carries its own collection surface, so spec bodies stay off the subtype's
`.val` projection. `vs.size`, `vs.foldl`, `vs.map`, `vs.any`, `vs.all`, `vs.findIdx?`,
`vs.contains`, `vs.toList`, and `for x in vs` read the list directly. `vs.toArray` hands
back the underlying `Array` for the operations the surface does not cover (`.filter`,
`.qsort`, or passing the buffer to an `Array`-typed helper). `Bitlist` mirrors the list:
`bits[i]!` / `bits[i]?` read a bit, `bits.size` the length. These live in SizzLean
(`Repr/Instances.lean`), next to `SSZList` itself.

`outOfBounds` carries the real index and bound: `sszGetIdx` reads the underlying array,
builds SizzLean's `IndexError (idx, bound)` (a payload-carrying constructor) on a miss, and
hands it to `liftErr`, which converts it to the context monad's reject via `[ErrorConv
IndexError E]`, reporting `i` / `size` directly. Decode failures no longer borrow
`outOfBounds`: deserializing a vector's bytes is the runner's job, not the spec's, so an
`Interface` deserializer's `.error` becomes `RunError.decode` (the runner error type below),
not a fabricated index.

`StoreTransitionError.missingKey` carries the 32-byte root (`Vector UInt8 32`).
`StateTransitionError` and `StoreTransitionError` classify by constructor into the
driver's pass / expected-rejection / out-of-scope / bug-smell buckets.

`RunError E` (`EthCLLib/Spec/Errors.lean`) is the runner-level error one layer above a spec
reject: `decode what` is a wire-deserialization failure (always a bug-smell, a well-formed
vector decodes), `spec e` carries a spec reject of type `E` through unchanged. Every
`ForkInterface` method returns `Except (RunError …) …`; `RunError.classify` (via the
`Classify` class over the two spec error types) sends `decode → likelyBug` and
`spec e → e.classify`, and `RunError.ofSpec` lifts a spec-level `Except` into it once a
method leaves decoding and runs spec code. This removed the old decode hacks (the
`outOfBounds 0 0` fabrication on the state path and the `assert "… decode failed"` on the
fork-choice anchor path), so a decode failure is named for what it is and never masquerades
as a consensus reject.

**Element writes: infallible `[i]!` vs checked `[i]`.** SizzLean's `sszUpdate` element
index comes in two forms. The checked `field[i] := v` is _fallible_ (`Except
IndexError`, matching the pyspec's `IndexError`), for a write that should reject an
out-of-range index. The bang `field[i]! := v` is _total_: it returns the bare `State`,
an out-of-range write being a silent no-op that mirrors `Array.set!`, and it emits the
same spine address and root as the checked form. The reset / caching writes
(`process_slot`'s root caching, the slashings / randao resets, the builder-payment
slots) key an index that is in range by construction (`idx = … % VECTOR_LENGTH`), so
they use `field[i]!`: total (it fits the `modifyState fun state => State` contexts with
no reject path) and, for the composite-element fields (`Vector Bytes32`, the
builder-payment vector), the cached O(log n) single-leaf update rather than an O(field)
rebuild. Both forms work over a preset-resolved (symbolic) cap (the derive's
`capToShapeSyntax` mirror in SizzLean).

**Root caching: `getStateRoot` threads the warm box.** `Box.hashTreeRoot` returns
`(root, warm-box)`, the warm box holding the committed intermediate-node tree, so taking
a root is `modifyGet`-shaped. `getStateRoot` (`Spec/State.lean`) is the primitive that
encapsulates it: it reads the boxed state, takes the root, and writes the warm box back
through `MonadState`, so a later root reuses the tree instead of rebuilding it. It pins
the state type `S` from the section's `MonadState S m` (the state type is an `outParam`),
then recovers the box through the `StateRoot` class, so the box's hasher and value type
need not be inferred as metavariables. The `state_transition` spine and the monadic
interface folds call it. The non-monadic sites use the pure `stateRoot` (root plus warm
box, `Spec/State.lean`), which keeps spec bodies off `Box.hashTreeRoot`: `process_slot`
calls it inside its `Id.run` block, since it needs both halves while it keeps mutating,
and `onExecutionPayloadEnvelope` calls it and returns the warm box, which the handler
stores back into `blockStates`. The pure `stateRoot!` (`Spec/State.lean`) is the discard
form, its `!` marking that it drops the warm box (the convenient-but-lossy variant, like
`Array.get!`). It is reserved for the terminal `Interface` sites, where the root is the
function's return value and the box dies with the call. Whether retention actually caches
is the box flavour's call (a cached box keeps the tree, a pure box does not), so the spec
threads unconditionally and the runner picks the flavour. Memory: the warm tree scales with state size, so at mainnet under high
`pytest-xdist` parallelism the retained trees can exhaust memory and crash workers; the
runner caps `-n` accordingly (mainnet runs at `-n 4`, Gloas mainnet at `-n 2`, until
per-test cleanup lands). That is a runner concern, not a reason to drop the threading
from the spec.

`CaseRequest` renames the pyspec metadata field to `caseMeta`, since `meta` is a
section-modifier keyword that fails to project.

## Authoring conventions

State binders are readable. The threaded state is `state`; where a step's previous state
is not reused, the next binding shadows it (`fun state => Id.run do let mut state :=
state`). Where a `← get` snapshot is read alongside a separate mutable (so two bindings
are live at once), the snapshot keeps `state` and the mutable is `stateAcc`. Element reads
spell out `validator` / `builder`, and the domain abbreviations are expanded:
`latestHeader`, `committeesPerSlot`, `epochsPerVector`, `indexedAttestation`,
`pendingDeposit`, `builderIndex`, `randomBytes`, `syncCommittee`, `prevStateRoot`. The
runner-glue binders follow suit: a post-state is `post`, the fork-choice interpreter's
threaded store is `storeAcc` / `store'`. The terse names that stay are the ones
`SPEC_AUTHORING_MODEL.md` §2.3 does not target: a loop index `i`, a type variable (`H`),
the monad variable, the `acc` of a fold, and one-line record-update callbacks
(`fun b => { b with … }`) whose binder is obvious within its single line.

Spec bodies carry a single `open EthCLLib.Spec`. The module re-exports the SSZ
collection vocabulary (`export SizzLean.Repr (SSZList Bitvector Bitlist)`, plus the
byte / collection / hasher helpers), so a pure spec body needs nothing more (Gloas adds
`open EthCLSpecs.Fulu` for the shared constants and primitive aliases; its component
_types_ are inherited into the Gloas namespace, not opened from Fulu). The residual `open SizzLean.Cache` /
`Hasher` survive only in the interface / fork-choice / upgrade glue, which name the box
representation (`SSZ.Box` / `Sha256` / `HasherTag`) directly; re-exporting those into
the author surface would defeat the `sszGet` / `sszUpdate` encapsulation.

## Module layout

**EthCLLib** (`SPECS_ARCHITECTURE.md` §3.6). §3.6 sketches an `EthCLLib/Forms/{…}` tree
that names concerns rather than a mandated layout. The realized layout is finer: the
author surface under `EthCLLib/Spec/` (`Arith`, `Assert`, `Crypto`, `Errors`,
`FiniteMap`, `Forms`, `Hasher`, `Header`, `Loop`, `SigningRoot`, `State`, aggregated by
`Spec.lean`), the pyspec driver under `EthCLLib/PySpecTests/` (`Driver`,
`Interface`), and the capture base under `EthCLLib/Internal/` (`Capture`). The §3.6
concerns map on: `Preset` / `Monad` / `Box` → `Spec.State` + `Spec.Header`; `Map` →
`Spec.FiniteMap`; `Crypto` / `Arith` / `Loop` → the same-named `Spec.*`; `Interface` /
`PySpecTests` → `PySpecTests.Interface` + `PySpecTests.Driver`. The names `FiniteMap` /
`Errors` / `Header` read better than the sketch, so §3.6 is reconciled by this mapping.

`Spec.Arith` carries `umax` / `umin` / `isqrt`, type-directed `uintToBytes`, byte
conversions, `vget`, `vecSliceEq` (fixed-window byte-slice equality), `vmodGet` /
`umodIdx` (ring-buffer read / write index), `sszDrop` / `sszOfArray`, `bitGet` / `bitSet`,
and `hasFlag` / `addFlag`. The cap-clamping append moved to SizzLean (`SSZList.push`,
with `sszAppend` / `appendState` on top), so the old `sszPush` is gone. `Spec.State`
carries `getStateRoot` / `stateRoot` / `stateRoot!`. `Spec.RunState` carries
`MonadRunState`, the class saying a state-machine monad can be run from a starting state,
and `runToRoot` (run a boxed-state action to its post-root, generic over that class, the
state-machine twin of `runOn`). `Spec.NestedMachine` carries `NestedStateMachine` and the
`runNestedStateTransition` / `evalNestedStateTransition` bridges. `Spec.SigningRoot` carries
`htr`, `computeForkDataRoot`, `computeDomain`, `computeSigningRoot`, `isValidMerkleBranch`,
and the signing-root verify combinator `blsVerifySigned`, over `[HasherTag]`. `Spec.Loop`
carries `Step` / `fuelLoop` / `fuelIterateM` / `fuelIterateM!`. `Spec.FiniteMap` carries
`MapKind`, `FcMap` (with `lookupD` / `getOrThrow` / `getOrThrowKey` / `values` /
`filterKeys`), `treeMap`, `hashMap`, and `Hashable (Vector …)`.

**EthCLSpecs** is split by concern within each fork (`SPECS_ARCHITECTURE.md` §3.1); no
`Helpers` / `Base` / `Misc` / `Util` catch-all exists. Fulu component containers are
one file each under `Fulu/Containers/` in topological order (`Fork`, `Checkpoint`,
`Validator`, `Eth1Data`, `BeaconBlockHeader`, `Sync`, `Execution`, `Deposit`,
`PendingOps`, `Withdrawal`); `Containers.lean` re-exports them; `BeaconState` is its own
`Fulu/State.lean`; the block-body / attestation / execution-payload containers stay in
`Fulu/Blocks.lean`. Pure-on-`Validator` predicates (`isActiveValidator`,
`isSlashableValidator`, `isEligibleForActivationQueue`, the credential predicates,
`getMaxEffectiveBalance`) sit in `Containers/Validator`; `isEligibleForActivation` reads
the finalized checkpoint, so it lives in the operation layer.

The Fulu operation layer, by concern in load order: `Time` (epoch/slot conversions,
`computeActivationExitEpoch`, the pure `currentEpochOf` / `previousEpochOf`), `Signing`
(`getDomain`), `Randao`, `Balances`, `Registry` (the read accessors), `Committees`
(with `getBeaconProposerIndex`), `Accessors` (the derived float-ups
`getTotalActiveBalance`, `getUnslashedParticipatingIndices`, block-root reads,
`getPendingBalanceToWithdraw`), `RegistryUpdates` (churn limits, the lifecycle mutators
`initiateValidatorExit` / `slashValidator`, the consolidation / compounding mutators,
`modValidator`, and `isEligibleForActivation`), `Rewards`, `Deposits`. `Committees`,
`Withdrawals`, `EpochProcessing`, `Operations`, `Transition`, `ForkChoice` round it out.

**The read/write seam** (§3.3) splits the Registry concern across the `Committees` row:
the read accessors (`getActiveValidatorIndices`) sit below `Committees` in `Registry`
(because `getBeaconCommittee` needs the active set), the mutators (`slashValidator`) sit
above it in `RegistryUpdates` (because `slashValidator` calls `getBeaconProposerIndex`).
The derived `getTotalActiveBalance` straddles `Balances` and `Registry`, so it floats up
into `Accessors`. This is a split by concern forced by the seam, not a by-kind
`Accessors.lean` / `Mutators.lean` grouping. §3.2's tiny-concern merge allows the
single-predicate `Predicates` row (`isEligibleForActivation`) to fold into
`RegistryUpdates`.

**Naming.** The runner is _PySpecTests_ on both sides: the Lean exe at
`EthCLSpecs/PySpecTests/Server.lean` (the `lean_exe` root), the Python harness at the
package-level `packages/EthCLSpecs/PySpecTests/`. Test libraries are `EthCLLib/Tests/`
and `EthCLSpecs/Tests/` (namespaces `EthCLLib.Tests.*` / `EthCLSpecs.Tests.*`), each its
own `lean_lib`, excluded from the shipped library for free (Lake's default lib glob is
`roots.map Glob.one`, so the main lib never reaches `Tests/`). The
`packages/<Pkg>/<Pkg>/` doubling is forced by namespace-equals-library-name.

The per-fork `ForkInterface` instance and its decode / run glue (`fuluInterfaceFor`,
`stateRootImpl`, the dispatchers, `pyspecPinnedVersion`) live in
`EthCLSpecs.<Fork>.Interface` (`Fulu/Interface.lean`, `Gloas/Interface.lean`), a
sub-namespace kept out of the bare `EthCLSpecs.Fulu` / `EthCLSpecs.Gloas` spec namespace.
The interface is the seam to the pyspec harness, not consensus logic, so it does not
sit among the spec helpers; it reaches the spec's `forkdef`s through the enclosing fork
namespace, and the `Server` selects `EthCLSpecs.<Fork>.Interface.<fork>Interface`.

## Fork choice

Fork choice is the second monadic state machine (`SPEC_AUTHORING_MODEL.md` §3.2,
`FRAMEWORK_ARCHITECTURE.md` §6–7, §9). `Store` (with `map : MapKind` and `[HasherTag]`,
plus the auto `[Preset]`), `LatestMessage`, and the Gloas `ForkChoiceNode` are
`forkstruct`s. The section opens with `fork_choice_section map`; the handlers are `forkdef
on* : StoreTransition Unit` over the typed `StoreTransitionError`. They write the same
`assert` / `todo` the state machine uses (resolved to `StoreTransitionError` through
`SpecReject` from the section's monad), `missingKey` for `FcMap` misses, and the inner
`state_transition` runs through `runNestedStateTransition` (`Spec/NestedMachine.lean`, converting an inner
failure as `StoreTransitionError.transition`). `ForkInterface.runForkChoice` returns `Except (RunError
StoreTransitionError) Unit`, and `Server` classifies the typed reject (`.spec (.todo _)
→ todo`, everything else, a `decode` or any other spec reject, `→ bug`), so no `"TODO:"`
string convention is involved. The `FcStep` wire
protocol the harness builds from `steps.yaml` carries the per-step block / attestation
files; a `block` step also feeds the block's own attestations and attester-slashings.

The interpreter does not own the valid/invalid policy. It runs each step to an `Except
StoreTransitionError (Store)` outcome (`runOn` projects the handler's `EStateM` result),
then pipes it through the framework `checkStepValidity before expectedValid outcome`,
which is the runner's per-step check, fork-agnostic over the store type. The snapshot is
the pre-step store (free, since stores are immutable values): a step expected valid that
succeeds threads its new store; one expected invalid that is rejected rolls back to the
snapshot and continues (the rejection is the expected result); the two mismatches, a valid
step rejected or an invalid step accepted, are returned as the run's failure (the first the
step's own error, the second a typed `assert`). The fork interpreters only run steps and
thread the store; the policy lives in `checkStepValidity`. A step that carries a `valid`
flag is `block`, the standalone `attestation` / `attester_slashing`, and in Gloas the
`execution_payload` envelope and `payload_attestation_message`; a step with no flag (`tick`,
the block's own `is_from_block` sub-attestations) is implicitly `valid := true`. The
harness then reports a returned error by its constructor (a `.todo` as out-of-scope, any
other as a bug-smell test failure). The `valid` flag on the standalone `attestation` /
`attester_slashing` steps matters for the `validate_on_attestation` vectors, where the wire
`valid: false` marks an attestation `on_attestation` is meant to reject.

`on_block` reads the current head before inserting the block and applies the proposer
boost only when the block is timely, no boost is already set, and the block shares the
head's dependent root (`get_dependent_root`, gated by `MIN_SEED_LOOKAHEAD`), the v1.7
rule.

The linear DAG walks route through fuel-bounded combinators (§12). `getAncestor` and the
`getHead` descent read `store.blocks` as they go, so they thread the store monad through
`fuelLoop`. The one tree walk, `filterBlockTree`, recurses over every child inside a fold,
which a linear combinator cannot express, so it keeps a local fuel-bounded `where` helper.
The totality the doc wants is met either way.

The fork-choice weight path still runs on raw `UInt64` where the pyspec's `uint64` ops
raise, and it is deferred as one piece because it rests on one root: `getTotalBalance`
(`phase0/beacon-chain.md:1130-1140`), whose `sum(...)` accumulates in `Gwei` and raises,
while this fold wraps. `committeeWeight` is `getTotalActiveBalance / SLOTS_PER_EPOCH`,
`calculateCommitteeFraction` and `getProposerScore` are its products, and `getWeight`'s
proposer-boost add takes one operand from them, so checking any of those while the total
underneath still wraps would only move the wrong number around.

The conversion is larger than the fork-choice layer. `getTotalBalance` and
`getTotalActiveBalance` are pure `forkdef`s with 15 call sites across epoch processing,
rewards, registry updates, the transition spine, and fork choice; making them throwing
propagates upward through every pure caller (§7.1's rule, one layer over). The remaining
independent site is `getAttestationScore`'s own balance fold, which sums
`state.validators[i].effective_balance` directly and could be checked on its own; it stays
with the rest so the weight path converts in one go rather than half-guarded. Reaching any
of them takes a total active balance within a factor of the `uint64` bound, which no
preset's validator set approaches.

The reference catches different exceptions per step kind, so what satisfies a
`valid: false` step varies too. `expect_assertion_error` (`context.py:424-435`) catches
`IndexError` for the attestation, attester-slashing, envelope, and PTC-message steps.
`add_block` catches `AssertionError` and `BlockNotFoundException` alone
(`fork_choice.py:389`). `FcStepKind` carries that table, and `checkStepValidity`
(`PySpecTests/Interface.lean`) reads it.

The Gloas fork choice is the node-based (`ForkChoiceNode = (root, payload_status)`)
ePBS rewrite: `get_ancestor` / `is_ancestor` / `get_weight` / `get_node_children` /
`get_head` thread the payload status, with the ePBS handlers
`on_execution_payload_envelope` (envelope verification) and
`on_payload_attestation_message` (PTC vote recording) and the payload-status / vote
checks; the `FcStep` protocol grows the envelope / PTC-message steps. EIP-7732 genuinely
differs here, so Gloas overrides most handlers rather than inheriting them, and the
`forkstruct` / `inherit` reuse pays off less than it does for the state transition.

## Fulu state transition

`Fulu/Transition.lean` is the spine: `process_slot` (cache state / block roots),
`process_slots` (with `process_epoch` at boundaries), `process_epoch` (the full Fulu
ordering), `process_block_header`, `process_randao`, `process_eth1_data`,
`process_sync_aggregate`, `process_execution_payload`, `process_block`,
`verify_block_signature`, `state_transition`. `Fulu/Withdrawals.lean` holds
`get_expected_withdrawals` (the EIP-7251 pending-partial queue then the Capella
validator sweep) and `process_withdrawals`. `Fulu/EpochProcessing.lean` holds every
`process_epoch` substep; `Fulu/Committees.lean` holds the swap-or-not shuffle and
everything built on it (`get_seed`, `compute_committee` / `get_beacon_committee`, the
balance-weighted sampler, `compute_proposer_indices` / `get_beacon_proposer_indices`,
`get_next_sync_committee`), pure functions of the boxed state. `getBeaconProposerIndex`
reads the precomputed `proposerLookahead` (Fulu EIP-7917), so the proposer needs no
runtime shuffle; only committees and building the lookahead / sync committee do.

Spec-faithfulness facts worth knowing:

- **`process_pending_deposits` resets `deposit_balance_to_consume` by stop reason.** An
  eth1-bridge / not-finalized / per-epoch-limit stop resets it to zero; a churn-limit
  stop carries `available_for_processing − processed_amount` forward. `ppdLoop` returns
  the `churnLimitReached` flag so the caller writes the right value.
- **`apply_pending_deposit` is signature-gated.** A new pubkey joins the registry only
  when `is_valid_deposit_signature` passes (the proof-of-possession the deposit contract
  does not check). The domain is fixed (`compute_domain(DOMAIN_DEPOSIT)`, genesis fork
  version, zero `genesis_validators_root`), so the check is one `[CryptoBackend].verify`.
- **`initiate_validator_exit` bounds the withdrawable epoch.** It asserts `exit_epoch +
MIN_VALIDATOR_WITHDRAWABILITY_DELAY < 2^64` before the write, so an over-range case
  rejects faithfully (matching the pyspec's `uint64` serialization `ValueError`) instead
  of wrapping silently on Lean's `UInt64`. Valid exits never approach the bound. Gloas
  inherits the substep with no Gloas-side change.
- **`process_execution_payload` takes the execution engine as valid.** It checks
  parent-hash / prev-randao / timestamp consistency and caches the header;
  `verify_and_notify_new_payload` is the consumer's responsibility, which is valid for
  `sanity/blocks`. The timestamp is `compute_time_at_slot(state, state.slot)`, the
  millisecond form every other clock site in the tree reads, and the standalone
  `operations/execution_payload` format threads the
  test's `execution.yaml` engine answer via `CaseMeta.executionValid` to model an
  engine rejection. The blob-parameter bound is enforced where the operation format
  supplies it. The skip is safe for the in-scope corpus by audit, not just by
  assumption: every invalid `sanity/blocks` / `finality` / `random` case (82, across
  both presets and both forks) rejects through a consensus `assert` the in-block
  pipeline models, signatures, blob-count limits, payload-attestation checks, the
  execution-requests root, slot / parent consistency, duplicate operations, the state
  root, so none reaches a clean run that an engine answer alone would have rejected.
  An invalid block that depended on the engine answer would run clean and surface as a
  `likelyBug` "expected a rejection but ran clean", not a silent pass.

`CryptoBackend.aggregatePubkeys` exists because `get_next_sync_committee` needs BLS
pubkey aggregation (the `ffi` / `verifyOff` backends delegate to
`LeanHazmat.Bls.ethAggregatePubkeys`; the `symbolic` backend returns a zero point).

## Gloas diff

`EthCLSpecs.Gloas` is `fork Gloas from Fulu` plus the EIP-7732 ePBS diff. The
`BeaconState` is the 46-field ePBS shape: `latestExecutionPayloadBid` replaces
`latestExecutionPayloadHeader`, `latestBlockHash` sits after `nextSyncCommittee`, and
the ePBS tail appends `builders`, `nextWithdrawalBuilderIndex`,
`executionPayloadAvailability`, `builderPendingPayments`, `builderPendingWithdrawals`,
`latestExecutionPayloadBid`, `payloadExpectedWithdrawals`, `ptcWindow`. The containers
are declared in-spec, tracking `specs/gloas/beacon-chain.md` (and `fork.md` for
`upgradeToGloas`). Gloas extends Fulu's three constant tiers with the
ePBS values: `ptcSize` / `maxBuildersPerWithdrawalsSweep` (preset);
`builderRegistryLimit` / `builderPendingWithdrawalsLimit` / `maxPayloadAttestations` /
the builder-payment threshold and builder prefixes and domains (universal); and
`gloasForkVersion` / `churnLimitQuotientGloas` / `consolidationChurnLimitQuotient` /
`maxPerEpochActivationChurnLimitGloas` / `minBuilderWithdrawabilityDelay` (config).

`upgradeToGloas` copies the carried-over fields, initializes the ePBS fields, builds the
PTC window from the Fulu pre-state's committees (`initialize_ptc_window` / `compute_ptc`,
called on the boxed Fulu state since the committee helpers are Fulu's), and onboards
builders from the pending-deposit queue (`onboard_builders_from_pending_deposits`). It
takes `GLOAS_FORK_VERSION` as a parameter and sets `fork := {previous :=
pre.fork.current, current := GLOAS_FORK_VERSION, epoch := currentEpoch}`.

**Epoch inheritance is the framework's reason to exist.** `Gloas.EpochProcessing`
`inherit`s the Fulu epoch substeps and their ~50 helper / time / RANDAO `forkdef`
dependencies verbatim. Each captured Fulu declaration re-elaborates in the Gloas
namespace against `Gloas.State`, sibling calls rebinding to the Gloas copies, no substep
body restated. EIP-7732 changes none of these substeps and `Gloas.BeaconState` carries
every field they read, so the replay typechecks and runs. A short module of `inherit`
statements turns the entire Fulu epoch transition into a green Gloas one; the `inherit`
order is the Fulu load order, so each body's dependencies are already in scope when it
replays.

The churn substeps are the exception: EIP-8061 gives Gloas its own
`CHURN_LIMIT_QUOTIENT_GLOAS` / `CONSOLIDATION_CHURN_LIMIT_QUOTIENT` /
`MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`, so `getExitChurnLimit`,
`getActivationChurnLimit`, `getConsolidationChurnLimit`, `computeExitEpochAndUpdateChurn`,
and `processPendingDeposits` are Gloas `forkdef` overrides ahead of the inherited
exit / registry / consolidation handlers. The Fulu committee helpers are `forkdef`s
inherited into Gloas, which carries `process_sync_committee_updates`,
`process_proposer_lookahead`, the new `process_ptc_window`, the EIP-8045
slashed-proposer filter in `get_beacon_proposer_indices`, and `compute_ptc`.

`Gloas.Operations` inherits the handlers EIP-7732 leaves unchanged (`attester_slashing`,
`bls_to_execution_change`, `withdrawal_request`, `consolidation_request`,
`sync_aggregate`) verbatim. The ePBS-modified handlers are Gloas `forkdef`s:
`process_proposer_slashing` (Fulu's logic plus the builder-payment cleanup),
`process_voluntary_exit` and `process_deposit_request` (each fronted by a builder-index
branch over the builder registry). The builder-registry helpers (`is_builder_index`,
`is_active_builder`, `get_pending_balance_to_withdraw_for_builder`,
`initiate_builder_exit`, `apply_deposit_for_builder`, `add_builder_to_registry`,
`get_index_for_new_builder`, and the rest) land here and feed
`onboard_builders_from_pending_deposits`. The payload-aware `process_attestation` (the
`data.index < 2` payload bit and the same-slot builder-payment weight accounting), the
new `process_payload_attestation`, the bid (`process_execution_payload_bid`),
`process_parent_execution_payload`, and the PTC read helpers complete the surface. The
builder-aware `process_withdrawals` is the four-phase sweep (builder queue, pending
partials, builder sweep, validator sweep) with the running-list cap that composes across
phases. `Gloas/Transition.lean` reshapes `process_block` (drop
`process_execution_payload`, prepend `process_parent_execution_payload`, add
`process_execution_payload_bid`, payload-free `process_withdrawals`, the in-body
`process_payload_attestation`s), `process_slot` (clear the next slot's
payload-availability bit), and `process_epoch` (builder-pending-payments and
`process_ptc_window` last). The `transition` format folds pre-fork Fulu blocks, applies
`upgradeToGloas` plus onboarding at the boundary, then folds post-fork Gloas blocks.

## Heze diff

EIP-7805 changes no state-transition substep, so Heze inherits the Gloas spine whole
and the diff is confined to the fork-choice inclusion-list layer. FOCIL ships no
behavioral conformance vector at the alpha.11 pin, so the divergences below are anchored
to the pinned spec text and the `EthCLSpecs/Heze/ForkChoice.lean` pins.

- **`is_inclusion_list_satisfied`** (`heze/fork-choice.md:54-62`) defers its answer to
  `ExecutionEngine.is_inclusion_list_satisfied`, an Engine-API call against an external
  execution client. This harness has no execution layer, so the call goes through the
  `[ExecutionEngine]` typeclass (the Engine seam above), whose default instance answers
  the constant `true`. That default is the execution-layer trust boundary of the FOCIL
  gate. No conformance vector reaches the discriminating `false` branch.

- **The `InclusionListStore` is a field of the fork-choice `Store`.** The
  spec keeps it as a process-lifetime singleton reached through
  `get_inclusion_list_store()` (`heze/inclusion-list.md:28-38`), and this framework has no
  ambient singleton to hang it off. Behavior is identical. The rationale lives on the
  `InclusionListStore` declaration (`EthCLSpecs/Heze/ForkChoice.lean`).

## Tier membership follows the upstream file

A value's tier is decided by the upstream file that declares it, never by whether
the two presets currently agree on it. Everything under
`presets/{minimal,mainnet}/*.yaml` is a `Preset` field, everything under
`configs/{minimal,mainnet}.yaml` a `Config` field, and a value the spec lists in a
constants table (weights, flag indices, domain tags, sentinels, prefix bytes)
stays flat in `Const`.

Reading that rule off the documents has one trap worth naming, because it is the
one that bit. The beacon-chain documents write `## Constants` and `## Preset`; the
fork-choice documents write `### Constant`, singular, one heading level deeper. A
sweep that matches only the beacon-chain shape drops every fork-choice constant
and comes back clean.

The rule earns its keep on the preset side, where a value shapes a type. A flat
literal for a preset-file value looks right for as long as the two files agree,
and the day one of them moves it produces a wrong cap, a wrong Merkle root, and a
green build. Config values never shape a type, so a wrong one shows up as a wrong
number and conformance catches it.

`scripts/check_constant_tiers.py` (`just check-constants`) is the standing check,
over both the tier and the fork that introduces each name. It moved 58 entries
when it was first run against the pinned `v1.7.0-alpha.11` documents: 47
preset-file values and 10 config-file values that were flat literals, plus one
constant filed under the wrong fork (below).

Two constants have no upstream table, so the attribution the check relies on
cannot place them. `G2_POINT_AT_INFINITY` is defined in the BLS document, and
`MAX_RANDOM_VALUE` is a local inside Electra's
`compute_balance_weighted_selection`. Both are ordinary flat `Const` entries,
placed by reading the spec text; the check lists them by name each run so a
re-pin re-examines them.

Two entries carry the phase 0 caps `MAX_ATTESTATIONS` (128) and
`MAX_ATTESTER_SLASHINGS` (2) beside their Electra successors (8 and 1). Nothing
at this fork reads the phase 0 pair; the Electra block body reads
`maxAttestationsElectra` / `maxAttesterSlashingsElectra`. They are kept because
they are distinct upstream keys, and set to the upstream values so the tier reads
as a faithful transcription of the file.

## A constant can arrive later than the function that reads it

`CONSOLIDATION_CHURN_LIMIT_QUOTIENT` sat in Fulu's `Config` and belongs to Gloas.
Electra has `get_consolidation_churn_limit`, but it computes a difference of two
churn limits and names no quotient; EIP-7732 rewrites the function to divide the
total active balance by a quotient of its own, and the constant arrives with it.
The name appears in no pre-Gloas document.

The trap generalizes: a fork can keep a function's *name* while replacing its
body, so "Electra already had this function" is not evidence that Electra had its
constants. Attribution has to come from the document that tables the constant,
not from the call site.

## Config-tier values that bite

Three config values differ enough between presets to be worth flagging, because each one
was a real reject-faithfulness gap until set per preset:

- **`MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`** is `128000000000` Gwei at minimal,
  `256000000000` at mainnet. It only binds in `consolidation_request`, where a
  large-balance state pushes the balance churn between the two maxima, so
  `get_consolidation_churn_limit = balance_churn − activation_exit_churn` needs the right
  minimal value. The exit / registry vectors floor at `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA`
  below both maxima, so the cap never binds there.
- **`GLOAS_FORK_VERSION`** is `0x07000001` at minimal, `0x07000000` at mainnet.
  `upgradeToGloas` takes it as a parameter so the gloas `fork` format matches at both
  presets.
- **`MIN_BUILDER_WITHDRAWABILITY_DELAY`** is `2` at minimal, `8192` at mainnet. It bites
  only on the builder-exit branch at mainnet (minimal's `2` is correct), where
  `initiate_builder_exit` sets the builder's `withdrawable_epoch`. The full mainnet sweep
  is what exercises it.

## Harness

`pyspec_server` is a long-lived, crash-tolerant loop (a malformed request reports failed
and the loop continues), one per `pytest-xdist` worker via the `conftest.py` session
fixture (re-spawn on death). `harness.py` does acquisition / walk / snappy / request
encoding; `test_pyspec.py` is the reject-faithfulness check. The server emits one
tab-separated line per case, so two detail sources that could embed a newline and
desync the worker are flattened at the chokepoint: `EthCLLib.Spec.sanitizeDescr` takes
the first trimmed line of an `assert` descriptor, and `CaseResult.render` flattens any
newline / tab in the detail to a space (the detail is diagnostic only). The
`ServerClient` drains non-protocol lines (lake / startup stdout) and retries once on a
desynced or dead server, so the parallel run is deterministic.

## Genesis

`SPECS_ARCHITECTURE.md` §10.1 marks `genesis` in scope and §6.1 names
`initializeBeaconStateFromEth1` / `isValidGenesisState`. The pytest corpus carries no
`genesis` vectors for Fulu, Gloas, or Heze at the `v1.7.0-alpha.11` pin, so there is nothing to
drive; both stay a `todo` stub in `Interface.lean`.

## Proofs

Consensus proofs currently live in `EthCLSpecs.Proofs`
(`EthCLSpecs/EthCLSpecs/Proofs/`), colocated with the consensus specifications
and remaining mathlib-free, following the `SizzLean.Proofs` pattern. The
standalone `EthCLProofs` package described in `SPECS_ARCHITECTURE.md` and
`PLAN.md` remains reserved for proofs that require mathlib, following the
conditional design described in `SPECS_ARCHITECTURE.md` §11.3 and the
`LeanPoseidonProofs` containment pattern. No current proof requires that
separation.

- **`Proofs/Gloas/BuilderIndex.lean`** establishes three `bv_decide` theorems over
  `isBuilderIndex`, `toBuilderIndex`, and `convertBuilderIndexToValidatorIndex`,
  proving the builder-index flag round-trip and tagging properties.

- **`Proofs/Gloas/GetPtc.lean`** proves `getPtc`'s `else`-branch offset into
  `ptcWindow` stays in range for its two guarded call sites:
  `getPtcElseOffset_lt_next_slot` under `process_payload_attestation`'s guarantee
  (`data.slot + 1 == state.slot`), and `getPtcElseOffset_lt_same_slot` under
  the fork-choice replay callers' exact-equality guarantee (`slot ==
  curSlot`). Both via `UInt64`/`Nat` bridging lemmas and `omega`, no mathlib.

- **`Proofs/Gloas/BuilderPendingPayments.lean`** proves `processBuilderPendingPayments`'s
  local before/after behavior for one call: the withdrawals loop reduces to a
  bounded `SSZList.push` fold over the qualifying previous-epoch payments' withdrawals,
  in slot order, and the payment window shifts down by `SLOTS_PER_EPOCH`. A
  capacity-guarded corollary derives the full, unclamped append under an explicit
  headroom hypothesis. It does not prove protocol-wide exactly-once settlement or say
  anything about `settleBuilderPayment` / `processProposerSlashing`, the other paths
  that clear a `BuilderPendingPayment`.

- **`Proofs/Gloas/CanBuilderCoverBid.lean`** characterizes `canBuilderCoverBid`'s
  `Bool` result exactly: `canBuilderCoverBid_iff` states the guard in the
  implementation's own `UInt64` `builderBalance` / `minBalance` terms;
  `canBuilderCoverBid_iff_toNat_add_le` restates it over `Nat` as a single
  non-wrapping addition-fits-in-balance fact. Both hold unconditionally under
  total/default indexing semantics, including fallback behavior for an
  out-of-range `builderIndex`.

- **`Proofs/Gloas/InitializePtcWindow.lean`** establishes three `simp`-closed theorems
  over `initializePtcWindow`: its two index regions (the empty first-epoch
  placeholder and the remainder computed via `computePtcFromFulu`), plus a
  `default` corollary for the first region.

- **`Proofs/Gloas/InitiateBuilderExit.lean`** gives the whole-transition
  `initiateBuilderExit_run_eq` contract at the box: the run on `pureState preState` returns
  `pureState` of a value whose `builders` carries one unconditional `SSZList.set!`
  write. The in-range and out-of-range theorems state the `runPure` form of that
  contract and read it through `SizzLean.Proofs.SSZListSet`, so the range split happens
  at the read rather than in a second transition proof; out of range the run returns
  the pre-state value itself. It also proves that the
  withdrawability-delay addition does not wrap for the shipped minimal and
  mainnet configurations.

- **`EthCLLib/Proofs/Run.lean`** (framework package) names the `StateT`-over-`Except`
  bind, throw, and
  `Except` facts every pure runner rewrites with (`run_bind`, `run_pure`,
  `run_throw`, `except_bind_ok`, `except_bind_error`). They are stated at an
  arbitrary state and error type, so they apply to `GloasRun` and
  `ForkChoiceStoreRun`. The same module pins the box:
  `pureState v` is the uncached box of the plain value, `runPure act v` runs an
  action on it and returns the result as a value. A contract theorem states the
  run at the box level, `act.run (pureState v) = .ok (a, pureState w)`, which
  the nested-machine bridge consumes by application, and `runPure_of_run_ok`
  derives the `runPure` form from it. `runPure_eq`, `runPure_pure`,
  `runPure_throw` are the remaining `rfl` facts proofs rewrite with. There is
  no `runPure_bind`: a bind law would have to know every intermediate box is
  uncached, so a composite body goes through `runPure_eq` to the box level.
  The module lives in the framework's generic proof toolkit,
  because the facts belong to no fork.

- **`Proofs/Gloas/Run.lean`** names `GloasRun`, the pure `StateT`/`Except`
  state-transition monad the Gloas proofs pin their `forkdef` bodies to.
  `StateTransition` is a parameter of a fork body, so every run theorem has to fix
  it; this fixes it once. Gloas call sites use the `EthCLLib/Proofs/Run.lean` facts
  (`run_bind` and friends) directly, as Heze does.

- **`EthCLLib/Proofs/StoreRun.lean`** (framework package) names `ForkChoiceStoreRun`, the shared pure
  store-machine runner every fork's fork-choice proofs pin at that fork's
  `Store`. It also holds `ForkChoiceStoreRun.throwArithmetic_run`, the
  store-specific equation for `throwArithmetic` under the store machine's
  `.transition` wrapper. The generic `StateT`/`Except` equations live in
  `EthCLLib/Proofs/Run.lean`. The module lives in the framework's generic
  proof toolkit because the runner is a monad over an arbitrary store type
  and so belongs to no fork.

- **`Proofs/Gloas/IsValidIndexedPayloadAttestation.lean`** proves a two-layer,
  backend-generic characterization of `isValidIndexedPayloadAttestation`. Layer 1
  mirrors the implementation's literal validation gates, `validators[i.toNat]!`
  included. Layer 2 restates them semantically and binds the in-range proof in an
  `∃`, so its pubkey array reads the registry through `Array.attach` and no
  panicking index survives into the public statement. No mathlib.

- **`Proofs/Gloas/ProcessOperations.lean`** places its public declarations in
  `EthCLSpecs.Proofs.Gloas`. It characterizes Gloas `processOperations` at
  `GloasRun`; handlers and later failure postconditions remain opaque.

- **`EthCLLib/Proofs/LawfulFcMap.lean`** places its public declarations in
  `EthCLLib.Proofs`. It defines the key-indexed `LawfulFcMap map K` interface
  and generic same-key insertion theorems, with concrete instances for
  `treeMap` and `hashMap`. The FOCIL handler postconditions that use those
  laws remain tracked by the `onExecutionPayloadEnvelope` entry in
  `PROOF_LEDGER.md`.

- **`Proofs/Heze/IsPayloadInclusionListSatisfied.lean`** places its theorems in
  `EthCLSpecs.Proofs.Heze`. `isPayloadInclusionListSatisfied_run` is the
  complete `.run` equation at `ForkChoiceStoreRun (Store map)` and carries
  `@[characterizes]`. A missing satisfaction key is the membership assert. A
  recorded value is returned only when the payload is verified, otherwise
  `false`. The four corollaries name the missing-record reject, an unverified
  recorded value, a recorded `false`, and a recorded `true` with a verified
  payload. Success leaves `runnerStore` unchanged. Verdict production and
  payload/verdict pairing remain later handler work, tracked by the
  `onExecutionPayloadEnvelope` entry in `PROOF_LEDGER.md`.

- **`Proofs/Heze/ShouldExtendPayload.lean`** places its theorems in
  `EthCLSpecs.Proofs.Heze` because `shouldExtendPayload` exists in both Gloas
  and Heze. `shouldExtendPayload_run` is the complete `.run` equation at
  `ForkChoiceStoreRun (Store map)` and carries `@[characterizes]`. The
  right-hand side is the evaluation order: block lookup, `getCurrentSlot`,
  the slot increment and assertion, `isPayloadVerified`,
  `isPayloadInclusionListSatisfied`, then the inherited Gloas tail. Named
  corollaries cover the prefix rejects, the FOCIL gate, the vote membership
  asserts, and the inherited Gloas accept and reject arms. Successful binds
  keep the intermediate runner states. A reject returns the error alone.
  `shouldExtendPayload_run_eq_false_of_recorded_unsatisfied` survives as a
  corollary: if the initial block lookup and slot checks succeed, Heze
  rejects a verified payload when the queried root has a recorded `false`
  inclusion-list satisfaction result, and the runner state remains
  unchanged. The bind lemmas it cites are the fork-neutral `run_throw`,
  `except_bind_ok`, and `except_bind_error` in `EthCLLib/Proofs/Run.lean`, plus
  `ForkChoiceStoreRun.throwArithmetic_run` in `EthCLLib/Proofs/StoreRun.lean`. They
  are stated at an arbitrary state type, so they apply to
  `ForkChoiceStoreRun`. The successful path that records
  the result of `isInclusionListSatisfied` is proved in
  `Proofs/Heze/RecordPayloadInclusionListSatisfaction.lean`. The successful
  handler path that writes `blockStates`, `payloads`, and
  `payloadInclusionListSatisfaction` at the same
  `signedEnv.message.beaconBlockRoot` is proved in
  `Proofs/Heze/OnExecutionPayloadEnvelope.lean`. Handler postconditions
  that pair `payloads[root]` with the satisfaction entry, and composition of
  those writes with this read, remain tracked by the
  `onExecutionPayloadEnvelope` entry in `PROOF_LEDGER.md`.

- **`Proofs/Heze/GetInclusionListTransactions.lean`** proves the collector
  run equations used by the recorder characterization.
  `getInclusionListCommittee_run_eq` is the complete committee `.run`
  equation on the concatenated `getBeaconCommittee` indices, tagged
  `@[characterizes EthCLSpecs.Heze.getInclusionListCommittee]`.
  `getInclusionListTransactions_run_eq` is the whole-operation bind of
  that committee run to collection at the committee's stored lists, tagged
  `@[characterizes EthCLSpecs.Heze.getInclusionListTransactions]`.
  The empty array throws the exact empty-committee arithmetic error.
  `FirstReachableMissingTimeliness` names the first reachable missing
  timeliness key in the `FcMap.fold` entries array. When `onlyTimely = true`,
  that predicate implies `.error (.missingKey ilRoot)`. Committee and
  collection errors propagate through `getInclusionListTransactions`.
  Those error corollaries stay untagged.
  The successful-result characterization of
  `collectInclusionListTransactions` remains proposed in `PROOF_LEDGER.md`.

- **`Proofs/Heze/RecordPayloadInclusionListSatisfaction.lean`** proves
  `recordPayloadInclusionListSatisfaction_run` in
  `EthCLSpecs.Proofs.Heze` and tags it
  `@[characterizes EthCLSpecs.Heze.recordPayloadInclusionListSatisfaction]`.
  The equation is complete at `ForkChoiceStoreRun (Store map)`. Slot zero
  returns the checked-sub arithmetic error. Otherwise the result matches
  on `getInclusionListTransactions` at the previous slot with
  `onlyTimely := true`. A collector error is returned unchanged. A
  successful collection returns `store` with
  `payloadInclusionListSatisfaction[root]` set to
  `isInclusionListSatisfied payload ilTxs`, paired with the collector's
  runner state. Public corollaries name slot zero, an arbitrary collector
  error, an empty committee, and a missing timeliness key. The last two
  follow from `Proofs/Heze/GetInclusionListTransactions.lean`.
  `recordPayloadInclusionListSatisfaction_run_eq` restates the successful
  branch with an arbitrary `postRunnerStore`. The generic `FcMap`
  interface does not specify how insert affects a later lookup.

- **`Proofs/Heze/OnExecutionPayloadEnvelope.lean`** proves
  `onExecutionPayloadEnvelope_run` in `EthCLSpecs.Proofs.Heze` and tags it
  `@[characterizes EthCLSpecs.Heze.onExecutionPayloadEnvelope]`. The
  equation is complete at `ForkChoiceStoreRun (Store map)`. Missing
  `blockStates` and failed data availability are `.assert` errors.
  Verification and recorder errors propagate unchanged. On recorder
  success the handler's final `set` writes `blockStates` and `payloads`
  on the recorder's explicitly returned store and discards the
  recorder-produced runner state. `.error err` contains no post-state.
  `onExecutionPayloadEnvelope_run_eq_of_successful_checks` restates the
  successful branch as the original store updated by three same-root
  `FcMap.insert` expressions. `recordPayloadInclusionListSatisfaction_run`
  characterizes the recorder's slot-zero and collector outcomes. The
  `proposed` `onExecutionPayloadEnvelope` row in `PROOF_LEDGER.md` lists
  lookup-after-insert and composition with the read-side theorems.

- **`Proofs/Gloas/UpdateCheckpoints.lean`** rewrites Gloas's `updateCheckpoints` as a
  single record update, which doubles as the frame condition that no other Store
  field moves. On top of it sit unchanged-or-advances characterizations for the
  justified and finalized checkpoints, plus monotonicity corollaries proving that
  neither recorded epoch decreases. The proofs use ordinary case analysis and
  core `UInt64` ordering lemmas. Their theorems live in `EthCLSpecs.Proofs.Gloas`
  rather than the flat `EthCLSpecs.Proofs`, since Fulu declares the same function.

- **`PROOF_LEDGER.md`** tracks candidate consensus proof targets and their status.

## Theorem vectors

Deviations found while building the generator's scaffolding and its stage 1,
against `THEOREM_VECTORS_ARCHITECTURE.md`. The section references below follow
the same file.

- **`WitnessSourceTag.reused` names its field `preset`.** The §5.4 sketch
  writes `reused (from : PresetId)`, and `from` is a Lean keyword, so the
  identifier cannot parse. The field carries the same fact.

- **The lakefile's outDir option carries the `weak.` prefix.** §2.3's
  snippet sets `theorem_vectors.outDir` directly, and the `lean` front end
  rejects that `-D` at startup, before any module registers the option.
  Lake passes the lakefile name to the flag verbatim, so the lakefile sets
  `weak.theorem_vectors.outDir`, the form Lean adopts once the registering
  module is imported. The value and the mechanism are the design's; the
  prefix exists because the option registers inside the library.

- **The outDir option registers in `EthCLLib.TheoremVectors.Types`, and
  the repository-root path stands in two places.** §4.1 assigns the
  options to `Command.lean`, which the reader stage adds. The registration
  lands in Types for now, because the lakefile's weak setting applies when
  the option's module is imported, and Types is the one module every
  generator module reaches. The lakefile pins the path, and the spec-half
  root's `outDir` constant reads the option and fails the build on any
  other value, so the build keeps the two equal. `Main` takes its `--out`
  default from the constant, because an exe root builds under the exe's
  own configuration and never sees the lib's `leanOptions`. The path is
  relative to the repository root, so a per-package invocation resolves it
  against the subpackage directory and lands under
  `packages/EthCLSpecs/packages/`, which `.gitignore` carries; the
  lakefile comment states the root-only assumption.

- **A per-package `lake` run can adopt plausible's toolchain pin.** The
  `plausible` repository pins `v4.29.0`, one patch behind the root
  toolchain. On a per-package invocation that fetches the dependency into
  an empty manifest, Lake writes a `packages/<pkg>/lean-toolchain` with
  that pin, and the subpackage then builds under it. Root and CI
  invocations read the root pin and never write the file. `.gitignore`
  carries the path for the two packages that reach the dependency, so a
  stray file cannot be committed; the tracked pins of `LeanSha256` and
  `LeanPoseidonProofs` belong to those packages' standalone releases and
  stay committed. This is the §2.4 version-drift risk seen from the
  subpackage side.

- **`ShapeTag.tag` and `PresetId.ofTag?` sit in `Types.lean` beside the
  sketches.** The record and outcome writers need the wire strings of a
  shape, and the exe's `--preset` flag needs the reader side of
  `PresetId.tag`; §5 sketches only `PresetId.tag`. The type stays the one
  canonical home of its wire form.

- **`Yaml` carries a `raw` leaf.** §5.6 stores a scalar as its pre-rendered
  literal, and the function format writes that literal into an inputs map,
  where the quoting rules would wrap a decimal literal in quotes to keep a
  consumer's parser from coercing it. The `raw` arm marks a leaf the
  caller already shaped, and the writer emits it verbatim. The record
  layer decides whether a literal is raw or quoted.

- **Stage 1 adds the `probe` discovery clause, and a fifth origin value
  `probe` beside it.** §14.3's discovery grammar has `characterized` and
  `tagged` only, and no clause selects the whole corpus. The plan's stage
  1 reads, classifies, and lists every public theorem of the three forks
  (its goal, its acceptance, and decision point A all need that), so
  `Command.lean` adds `theorem_vectors probe`: it selects every public
  theorem under the fork's proof namespace that no other clause or line
  selects, and the outcome lines carry origin `probe`. The generator
  files drop the clause when stage 2 wires the search; the origin value
  goes unused with it.

- **`Statement.readIn` folds over the statement instead of returning
  it.** §7 reads a theorem type into a `Statement`; the sketch implies a
  plain function. `forallTelescope` declares the theorem's free
  variables with a local context it restores once its callback returns,
  so a `Statement` carried out of the walk would name free variables no
  later step can see (`whnf` inside `Scope.classify` fails with
  `unknown free variable`). The reader takes a continuation and every
  consumer folds to its wire form inside it.

- **Target discovery keeps fork ownership, adds "callable definition,
  not a projection", and skips type and instance arguments.** §7.2 says
  the target is the first left-side application whose head
  `Capture.isSpecFunction` answers true for. Three corpus facts widen
  and narrow that test. The fork-upgrade file declares its boundary
  functions as plain `def`s (`initializePtcWindow` among them), and
  §7.2's own example names one as the target, so the `forkdef`-only test
  loses real targets; ownership by the fork plus a definition kind keeps
  them. The fork's `State` abbreviation is a plain definition too, and
  pre-order over `@StateT.run σ m α act s` reaches it through the
  `σ` argument before the action, so type arguments stay out of the
  walk; the same spine carries the fork's `GetElem` instance for
  `(x)[i]`, so instance arguments stay out too. And a monotonicity
  bound over `store.justifiedCheckpoint.epoch` would name the field
  accessor `Checkpoint.epoch`, so projection accessors stay out.

- **`Outcome`'s theorem field carries French quotes.** `theorem` is a
  keyword; the field is `«theorem»`, and the derived JSON instances
  keep §16.1's wire spelling.

- **The exe's `render`, `check`, and `list` answer over the records tree
  from stage 1.** §15 stages their real bodies at stage 2 (`render`,
  `list`) and stage 7 (`check`), and the plan's rule lets the
  `theorem-vectors` recipe stay red until stage 2. Stage 1's acceptance
  runs the same recipe, so the three subcommands walk the (empty)
  records tree, report what they find, and exit 0; the walk functions
  are the ones stages 2 and 7 fill in.

- **`EthCLLib.TheoremVectors.Tests` is a second root of its library.**
  §4.1's module map places the framework-half tests under
  `EthCLLib/TheoremVectors/Tests/`, and the plan's stage 1 adds the
  attribute test there. A `lean_lib` builds its roots, so the lakefile
  lists the test root beside the library root; the shipped `EthCLLib`
  library still globs only its own root.

- **The command reads the binding through `opaque` + `implemented_by`.**
  §6 says the command reads the binding with `evalConst`. In this
  toolchain `Lean.evalConst` is `unsafe`, and a safe elaborator cannot
  call it. The reader follows the `#eval` machinery's shape
  (`Lean.Elab.elabEvalCore`): a safe `opaque` whose body never runs,
  with an `@[implemented_by]` unsafe implementation that evaluates the
  constant. The spec-half pins reuse the same pair.

- **The reader zeta-reduces a leading `let` in the conclusion.** §7.3's
  matcher sees the conclusion as `forallTelescope` hands it over, and
  `getInclusionListCommittee_run_eq` names a scratch value (`indices`)
  between its hypotheses and its conclusion, so the matcher receives a
  `letE` and answers `unsupported: not an application` for a
  `characterizes` claim. The reader instantiates the `let`'s value into
  its body before matching; nothing else about the conclusion moves.

- **Type-parameter binders are their own `Statement` field, not inputs.**
  §5.2's `Statement` has instance binders, inputs, and hypotheses; the
  corpus also binds `{σ : Type}` and `{map : MapKind}`, implicit
  non-`Prop` binders that are neither classes nor producible values.
  §7.1's table would call them inputs, and §7.4's walk would then report
  `map` as function-typed (`MapKind` unfolds to a `Type`-level arrow),
  folding every `Store` theorem to `.unsupported` for a binder the fork
  binding fixes anyway. The reader classifies such binders (a sort, or an
  arrow into a sort, after `whnf`) into a `typeBinders` field beside the
  inputs; phase B fixes them like the instances.

- **The `.runOk` closed-post-state check allows every telescope binder,
  and `pre` must be the first value binder.** §7.3 says the match
  requires `pre` to be one of the inputs and `post` to be a closed term
  over the inputs. The box wrappers take `[SSZRepr T]` and `[HasherTag]`
  implicitly, so the post-state's `pureState` applications carry
  instance fvars; rejecting them would reject every contract in the
  corpus. The check allows all telescope binders (instances included,
  fixed per preset in phase B) and rules out only locals the theorem
  does not bind. `pre` is pinned to the first value binder, which every
  corpus contract spells `preState` or `state`, so a record update over
  a later store cannot satisfy the match by accident.

- **The command clears a fork's outcome subtree at its header.** §16.2
  folds whatever outcome files exist, and a theorem the generator lines
  no longer name would keep its stale row until someone ran
  `theorem-vectors-clean`. The header command removes
  `<outDir>/outcomes/<fork>/` before the pass runs, so `report.md`
  always reflects the current lines.

- **The report's hygienic binder names lose their macro scopes.** The
  instance binders of §7.1 arrive with generated names
  (`inst._@.…_hyg.9`), and the unknown-seam reason wrote them raw into
  the outcome and the report. `Statement.readIn` erases macro scopes on
  the names it records; the class name keeps its full spelling.

- **The generator commands reserve their keywords for files that open
  `EthCLLib.TheoremVectors`.** Lean's parser reserves the atoms of a
  command syntax (`skip`, `characterized`, `tagged`, `survey`,
  `presets`), and a file that opens the namespace cannot use them as
  identifiers. The generator files never do; `Command.lean` spells its
  own locals around the reservation (`ps`, `charSet`, `presetIds`), and
  the shipped libraries never open the namespace.

- **`meta.yaml` goes out in flow form, and hex values go out quoted.**
  §12.3 says the upstream vectors write `meta.yaml` in block style byte
  for byte, and §13.3 shows a hex value unquoted. The cached upstream
  corpus shows both wrong: a Gloas `epoch_processing` `meta.yaml` is the
  one-line flow map `{bls_setting: 1}`, and `roots.yaml` carries
  `root: '0xc292…'` in single quotes. The writer matches the corpus:
  `renderFlowDoc` writes `meta.yaml`, and the `hex` leaf renders
  single-quoted, which also keeps a consumer's parser from reading a root
  as an integer. A plain `0x…` in the function format would coerce.

## Theorem vectors, stage 2

Deviations found while building the probe, the executor, the records, the
function format, and the search wiring, against
`THEOREM_VECTORS_ARCHITECTURE.md` and the plan's stage 2.

- **The window theorems run from seeded inputs, not `default` inputs.**
  The plan's stage-2 acceptance names `initializePtcWindow_lt`,
  `initializePtcWindow_lt_default`, and `getPtcElseOffset_lt_same_slot`
  writing records from `default` inputs. The first two take a
  `Fulu.BeaconState`, and the default state's validator set is empty and
  all-inactive (its `exitEpoch` is `0`), so `computePtcFromFulu`'s
  balance-weighted selection (`Committees.lean`'s `cbwsAux`) can never
  fill its target size and burns the full 10,000,000 iteration fuel per
  empty committee, once per window slot. One evaluation ran past 25
  minutes without finishing. The seed `activeState` supplies 64
  max-balance active validators, whose committee fills the selection in
  a few dozen iterations; each evaluation then takes ~0.2 s. The two
  theorems carry named lines with `(state := …)` seeds and write with
  source `seed`; `getPtcElseOffset_lt_same_slot` still writes from
  `default` inputs with source `base`. Stage 6's `built` source inherits
  the fact: §9.2's source order runs the base source before the built
  one, so a state-input theorem whose `default` run burns the fuel bound
  would hang the search before a builder ever ran. §9.4's state rule now
  answers it: neither the base source nor the seed fill proposes
  `default` for the binding's state type, and the `FUTURE_WORK.md` entry
  on a cost guard is retired.

- **The seed grammar splits into seeded and seedless rules.** §14.3's
  grammar sketches one `theorem_vectors[!] <ident> [with …]` form. An
  `optional("with")` inside the rule shifts the child indices between
  its two spellings, so the elab cannot read the seeds and the presets
  clause at fixed positions; the parser carries two rules per strictness
  instead, with the seeds and presets at fixed indices.

- **The probe term is built as an `Expr` tree, not as source text.**
  §11.2 says the builder writes source text, parses it, and elaborates
  it under `binding.opens`. Direct construction produces the same closed
  term without a stringly-typed intermediate, and the instance-binder
  substitution is a mechanical `Expr` rewrite either way. The term still
  obeys §11.2's two rules: the `Except` matching lives in the
  precompiled helpers (`runProbeOk`, `runProbeError`, `eqRunResult`,
  `boundRunResult`), and the term is evaluated once per statement and
  preset with the case index as a runtime argument.

- **One `ScalarCodec` class fronts the wire encoding, and `Fin` uses
  the `uintN 64` little-endian encoding of `Fin.val`.** §9.1 sends every
  input across the boundary as SSZ bytes, but a `Fin`-typed input (the
  window offset of `initializePtcWindow_lt`) has no `SSZRepr` instance
  and cannot: a total decode from bytes cannot respect `Fin`'s bound.
  The codec carries `encode` / `decode` / `default` per type. Both
  decodes are strict, and the check reads a failed decode as `false`
  (§9.3), so a corrupt record cannot pass a value as in range. The
  `SSZRepr` decode answers `none` unless the shape decode consumed the
  whole side file. `Fin n`'s decode answers `none` for a value at or
  above `n`, and for any byte string that is not exactly eight wide.
  The encoding is the same scalar family §9.4's bit-vector source puts
  `Fin n` in. `default` is a codec field rather than an `Inhabited`
  instance because `Fin`'s default needs `0 < n` and no
  `NeZero (3 * slotsPerEpoch)` exists to synthesize; the codec's own
  `n` pattern match carries the proof.

- **`ProbeResult` carries the inputs' literals and splits the roots.**
  §5.5's sketch has `output`, `expected`, `agree`, and one `roots` list.
  The record layer (§12.2) writes a decimal literal for a scalar and a
  root for a container, and it needs to know which one each value is; a
  `Nat`-typed bound output (`getPtcElseOffset`) has no SSZ root at all,
  and its output file holds the literal's UTF-8 bytes. `ProbeResult`
  adds `literal`, `inputLiterals`, and `outputRoot`, and `inputRoots`
  entries are optional.

- **`Probe.defaults` is a field.** §11.1's sketch lists no defaults, but
  §9.4's base source proposes the serialized `default` of every input as
  its candidate. The base source holds no compiled code of its own, so
  the probe bakes the serialization in at build time.

- **`Probe.ofStatement` returns `Except String`, and the reason is a
  skipped run.** §18 treats the probe's own failures as build errors,
  but three of its inputs are facts about the theorem: a shape the
  stage-2 executor does not run yet (`.iffTrue` in stage 3, `.runOk` /
  `.runError` in stage 7), type parameters the command cannot fix, a
  missing wire codec or recordable output form, and a dependent input
  type the flat decode cannot express. Those answer `.error reason` and
  the command reports a skipped run; an evaluation failure still throws.

- **`Statement` hands its caller the telescope's free variables.** §11.2
  substitutes the instance binders with the binding's constants, which
  needs the instance fvars, and abstracts the value binders with
  `mkLambdaFVars`, which needs the value fvars. The reader's fold now
  passes a `StatementCtx` (statement plus both fvar arrays) instead of
  the bare `Statement`; the pins updated with it.

- **An `unsupported` outcome's shape field writes `unsupported`.** The
  §16.1 example leaves the field's value for that case unspecified;
  `Shape.wire` answers `unsupported` and the run's `reason` carries the
  reader's or executor's explanation, box lemma reasons included.

- **A survey outcome carries one run with no preset.** §16.1 says the
  survey line has one run with status `unselected` (or `unsupported`
  with the reader's reason) and no preset field, so `RunOutcome.preset`
  is an `Option PresetId` and the report prints an empty preset cell for
  it.

- **The format registry lives in `Formats/Function.lean`.** §13.1 places
  `Formats.all` in `Format.lean`, but the registry holds the formats and
  `Formats/Function.lean` imports `Format`, so the registry there would
  be circular. The registry grew where the formats live; the pyspec
  format's value stands beside the function one.

- **The exe's `check` replays through each format's own consumer.**
  §13.1's `CheckResult.noConsumer` is the function format's whole
  answer, so `check` runs the registry over the rendered vectors and
  counts only the pyspec cases, whose `runCase` replay answers
  `passed` / `failed` (§13.5).

- **The record JSON's field names differ from §12.2's sketch in two
  places.** The case index writes `case`, and the payload nests under
  `value`, because the scalar's literal and the container's root share
  one field slot (§12.2 sketches flat `ssz` / `root` / `scalar` keys
  beside the name). The record's theorem field spells `«theorem»` in Lean,
  a keyword, and the derived JSON writes the wire spelling §12.2 fixes.
  The record reader and writer agree with each other; a consumer reads
  records through neither.

- **The wrong-expected test's subject is a `def` with an
  `implemented_by` implementation.**
  The plan's stage-2 step 12 sketches a wrong expected value built through
  an `opaque`; an opaque cannot serve, because the kernel never unfolds it
  and so can prove no wrong equality about it, and a false axiom would
  put an unsound constant in the environment. The test's `toyWrongFun`
  carries the kernel body `x + 4` and an `implemented_by` implementation
  `x + 3`: the kernel proves `toyWrongFun x = x + 4` with `rfl`, and the
  compiled code the probe runs answers `x + 3`, which is the
  compiler-defect class the agreement check exists for, with no axiom in
  the environment.

- **The function format accepts only records with a target.** §13.3 says
  the format accepts every record, but its `function` field names the
  function a client exposes, and a record without a target has none to
  name; the fallback wrote the theorem's name into the field. A rejected
  record stays in `records/` (§13.2), and `getPtcElseOffset`'s bound
  records, whose target is none, render nowhere in stage 2.

- **`VectorFormat.render` takes the output's bytes.** §13.1's sketch
  passes the record and the input bytes alone, and §13.3 promises a
  container output's `ssz` as its hex; with only the input bytes the
  function format had no bytes for the output and wrote `ssz: '0x'`.
  The render seam carries the `ReadBack` output bytes beside the inputs,
  and the render and check passes hand the rendered paths over through
  `<out>/formats/manifest.json`, so §13.2's "check receives what render
  returned" holds across the two subcommands.

## Theorem vectors, stage 3

- **The base source stays out of a seeded line's source list.** §9.2's
  fixed order puts base between seed and bit-vector. A seeded line's
  `default` candidate ignores the author's chosen inputs, which is the
  very reason §9.2 gives for running seed first, so the command assembles
  seed then bit-vector for a seeded line, base then bit-vector for a
  seedless one, and base alone for a block-input theorem. §9.4's seed
  path already ends at "hands the partial assignment to the bit-vector
  source"; base was never in it.

- **A seed the check rejects answers per case, and the build error is
  line-level.** §18 makes a failing seed a build error, written when a
  theorem prepared one case. A multi-case theorem's seed may satisfy the
  case it was written for while another disjunct rejects it, so the seed
  source answers `nothing` for the cases it fails, and the command errors
  only when a fully-covering seed wins no case of the run. A partially
  covering seed carries no claim of that strength.

- **The bit-vector source's seed handoff evaluates the seeded reads in
  compiled code over a coupled-scalar grid.** §9.4 says the seed source
  "hands the partial assignment to the bit-vector source for the rest",
  and stage 4 stages `reads` for the random source's version of the same
  step. The handoff needs the reads now: a seeded hypothesis such as
  `coverBidState.builders[builderIndex]!.balance` couples a scalar with
  the seeded state, and no source can solve it while the read stays
  symbolic. The source fixes each coupled scalar (one that co-occurs
  with a seeded input in a hypothesis) over a bounded value grid, 64
  values per scalar capped at 128 fixed points per case, evaluates each
  fixed point's closed seeded reads through `evalExpr`, and hands the
  residual formula over the free scalars to `bvDecide'`. The probe's
  `reads` field stays empty until stage 4, where the random source
  reuses this module's walk. Grid values are the small values a scalar
  index into a seeded container takes in practice; a coupled scalar
  beyond the grid falls to a later source or a seed.

- **A per-grid-point `unsat` is not the case's answer.** §9.4 returns
  `Failure.unsat` when the solver proves `¬P`, which stops the search.
  Under the coupled grid, `¬P` is proven only at one fixed point of the
  coupled scalars, so the source continues the grid and answers
  `nothing` when every point fails. A seeded theorem whose residual
  formula carries no coupled scalar stays in the same position: its
  reads hold the seed's values, so an `unsat` there is a fact about one
  seed, and the source answers `nothing`. Only the seedless pure scalar
  solve, where the formula carries the whole case, returns `unsat`.
  Inside the grid the source also runs the check on each candidate
  before it returns, so a rejected point moves the walk to the next
  grid point instead of ending it.

- **The DNF split is a structural walk, not a simp pass.** §8.2 puts the
  unfolded conjunction in disjunctive normal form. The walk pushes `∨`
  outward and applies De Morgan over `∧` one `¬` at a time, and it never
  enters a quantifier, so an `Array.all` gate stays one conjunct and a
  gate-per-check theorem splits per gate, not per element.

- **The unfold's `UInt64` bridge lemmas are the pass's own restatements.**
  §8.1 orients the proofs' `Nat`-level bridge lemmas back toward
  `UInt64` form. The four restatements live in `Prepare.lean`
  (`uint64_toNat_lt_iff` and siblings) so the simp set carries the
  rewritten direction directly; `a.toNat + n = b.toNat` for `n > 1` has
  no sound `UInt64` image (the addition can overflow) and stays out of
  reach, as the plan's risk note predicts.

- **The prepare pass's `simp only` is per hypothesis and recoverable.**
  The pass unfolds with the equation lemmas of the captured spec
  functions that hypothesis names, so a theorem whose hypotheses name no
  fork function pays nothing. A simp failure leaves the hypothesis as it
  was; the split and the decidability check then answer on the ununfolded
  form, which is what the report shows.

- **The unfold only takes spec functions with a small body.** §8.1 says
  the pass unfolds every captured spec predicate the hypothesis names. A
  forkdef whose body folds over a state container (a pending-balance sum)
  unfolds into a term whose simp walk spends the command's heartbeats
  without exposing one comparison, and a `deterministic timeout` is not
  something the pass can catch. The pass therefore unfolds only
  definitions under 100 expression nodes; the big ones reach the solver
  through the bit-vector source's compiled evaluation instead, which
  grounds the whole closed call in one `evalExpr`. `computeEpochAtSlot`
  (a division) unfolds; `getPendingBalanceToWithdrawForBuilder` (two
  folds) does not. The plan's "unfolding blows up" risk names the
  phenomenon; this is the guard for it.

- **The search's read grounding covers every closed scalar subterm.**
  What began as §9.4's seeded-read substitution grew one step: preset
  constants (`UInt64.ofNat slotsPerEpoch`) and crypto gates under the
  verify-off backend ground the same way, because the solver's own
  preprocessing treats an un-reduced constant as an opaque atom and
  returns a spurious model around it (the plan's stage-3 risk note
  predicted the symptom; the constant was the cause). The grounding runs
  twice per hypothesis, before and after the unfold, so the unfold's
  products ground too. A subterm under a lambda carries loose bound
  variables and stays.

- **The bit-vector source poses its goal in a context of the fresh
  scalars alone.** §9.4 poses `¬P`. The goal is built with
  `mkFreshExprMVarAt` over a local context holding only the free
  scalars: `bv_decide` reflects every proposition it finds in the goal's
  context, and the reader telescope's own hypotheses are the
  un-substituted forms, which would hand the solver a formula about
  variables the candidate never carries.

- **Each run carries its own heartbeat budget from an option.** One
  line's search runs up to 128 solver calls and two rounds of
  compiled-read evaluations, which spends the default per-command budget
  many times over. The command sets `theorem_vectors.maxHeartbeats`
  (default 1000000) around each run by writing both `Core.Context`
  reader fields, `maxHeartbeats` times 1000 and `initHeartbeats` at the
  run's start, so the budget is per run and the generator file sets no
  `set_option`. An earlier revision raised the file's `maxHeartbeats`
  instead and claimed a reader-field change inside the run could not
  raise it; that claim was wrong, and the reader fields take the change.

- **The witness sources' `applies` reads the search context.** §9.2's
  sketch types `applies : Statement → Case → Bool`. §9.4's state rule is
  a statement of the state test over the input types, and it needs the
  binding's `stateType`, which only the `SearchCtx` carries, so the seam
  is `applies : SearchCtx → Statement → Case → Bool`. The base source's
  state test and the seed source's two tests (seeds present, no unseeded
  state input) sit there, where the search loop reads them.

- **A source's `nothing` carries a detail, and `notFound` reports it.**
  §9.2 says `notFound` names every source that ran; the reason also names
  what the sources learned: the atoms the solver abstracted when a model
  was spurious, and a `Fin`-typed input the solver's domain does not take
  yet (§9.4 stages the bridge in stage 4). `SearchStep.nothing` carries
  the detail and `Failure.notFound` collects it; the report line prints
  it beside the source list.

- **The record's `type` fields carry the rendered type.** §12.2's example
  shows constants (`EthCLSpecs.Gloas.BeaconState`), and the stage-2 build
  kept only the head constant, which writes `Fin` for the window offset
  and `Vector` for the window entry. `ProbeInfo` stores each type rendered
  with the preset's constants substituted, and `VectorValue.type` is that
  string, so the client-facing field names the spec type.

- **The generator's named lines and skip lines precede its discovery
  clauses.** §14.3's positional order: each line elaborates as its own
  command, so a discovery clause above a named line runs the theorem once
  without the seeds and warns, and the named line runs it again; above a
  skip line, the clause's pass runs the theorem and the skip can only
  replace the outcome. A named line or a skip line whose theorem a
  discovery clause already ran is an error whose message names the fix.
  A skip validates against the potential selection, the tags of §14.1
  and the fork's proof namespace. The line can sit above the clauses it
  excludes from, and a stale exclusion is still visible.

- **Each run wipes its theorem's record directory first.** §14.3's
  precedence lets a named line re-run a theorem a discovery clause
  already ran in an earlier same-file pass; the cases the override does
  not reproduce must not linger, so `runPreset` removes
  `records/<fork>/<preset>/<thm>/` before its cases search.

## Theorem vectors, stage 4

- **The generic `SampleableExt` instance fell out of SizzLean's type
  description.** This answers the plan's decision point B: no
  hand-written per-container generators and no extension to the
  description were needed. The instance maps a type with `SSZRepr` to
  its shape's `interp` image (`proxy`) through `fromRepr` (`interp`),
  and the draw and the shrink walk the description shape by shape
  (`genShape`, `shrinkShape` in `Sampleable.lean`). The wide `uintN`
  widths reduce on their literals, and Fulu's state carries one
  (`baseFeePerGas : BitVec 256`), so `128` and `256` draw, shrink, and
  print like any `BitVec`. Any other width is the one gap:
  `interp (.uintN n)` is stuck for a symbolic width, so no
  `BitVec`-typed value has the interp type there, and the draw fails
  honestly while the shrink proposes nothing.

- **The scalar draws mix small and boundary-scale values.** §9.5 hands
  the scalars to Plausible's draw, whose `UInt64` stays inside the size
  parameter, and a protocol scalar's interesting values sit on both
  sides of constants such as `minDepositAmountG`. The hand-written
  `UInt64` instance draws small most of the time and full-range
  otherwise; the other widths keep Plausible's.

- **The draw's seed is hashed before `mkStdGen`.** The generator state
  over small seeds is near-linear in the seed, and the draws' seeds are
  small integers over `theorem_vectors.seed`, the draw index, and the
  input position. Raw, they repeat values across draws: every drawn
  attestation's index list held the same length, which no honest draw
  would. The probe hashes each position's seed with `mixHash seed
  (i + 1)` and `runDrawPure` hashes again, so no two positions and no
  two draws share a generator state; the draw stays pure, and the same
  seed and size draw the same bytes.

- **The probe's `reads` takes the case index.** §11.1's sketch types it
  `Array ByteArray → Array ByteArray`; the reads are one case's
  hypotheses' subterms, and §9.2 already gave `check` the same
  parameter. The probe builds the reads per case from the same walk
  (`containerReads`) the random source substitutes with, which is what
  keeps the serialized values aligned with the subterms they replace.

- **The random source's container reads are the maximal subterms with a
  scalar literal form that mention a container input.** §9.4 says
  "every maximal subterm of the hypotheses that mentions only container
  inputs". The literal-form requirement is what makes the substitution
  a literal the solver reads, and it covers the gates that mention only
  containers (their `… = true` propositions) the same way. The walk
  never enters a lambda or a `let` body, because a term under a binder
  has no runtime value to evaluate at; the hypotheses arrive
  zeta-reduced, the same form the walk saw.

- **The random source runs on seeded lines too, and the draw wins over
  the seeds.** §9.2 places the built and random sources after the
  bit-vector source on every list, so a case the seed fails reaches the
  draws. The candidate's byte overlay therefore reads the drawn bytes
  before the probe's seeds: on a case the seed won, the loop never gets
  there, and on a case it failed, the draw is the witness and the
  record's `source` says so.

- **A point whose reads misground still cannot write a wrong vector.**
  A draw's shapes are random, so a read can index a drawn container past
  its end (a `!`-read). Lean's panic answers the read with its type's
  default and prints to the build log; the grounded formula is then
  wrong, the point's candidate fails the check, and the loop moves on.
  The cost is one wasted solve plus a panic line per misgrounded point,
  which the grid's drawn-bound cap and the drawn lists' short lengths
  bound.

- **The `Fin` stand-in's bound is a conjunct of the goal.** §9.4 enters
  a free `Fin n` input as a `UInt64` with the bound `x < n`. Spelled as
  a context hypothesis, the bound reifies as an unconnected `Bool` atom,
  because the preprocessor normalizes the goal's own formula alone, and
  the model came back unbounded. As a conjunct the bound normalizes with
  the rest, and the strict `Fin` decode refuses whatever slipped past
  (§9.3). The corpus states its `Fin` bounds at the `Nat` level
  (`i.val < slotsPerEpoch`), and the solver's fragment takes `UInt64`
  comparisons alone, so the bridge rewrites a `Nat`-form comparison over
  one `Fin.val` side to the stand-in's `UInt64` form in the same step; a
  comparison it cannot express stays, and the reflection's failure
  reports the case as `notFound` rather than solving an unbounded
  stand-in.

- **One `probe.shrink` call is walked past the first passing
  candidate.** §9.6 keeps the first candidate that passes and repeats
  by re-asking. Each repeat re-decodes the witness's containers, and
  the re-decode of a drawn state is the loop's own cost, so the loop
  keeps every passing candidate of one call before it re-asks: each
  accepted improvement still consumes one `theorem_vectors.shrinkSteps`
  step, and every candidate passed the check. The shape shrinkers also
  propose a lean candidate list per step (two length cuts and one
  element cut per list; a container's length cuts come before its fixed
  fields' element cuts), because a drawn state's forty fields would
  otherwise flood the loop with candidates. Two guards keep the walk
  honest: a candidate is accepted only when its wire size does not
  exceed the current witness's, since the list was built from the
  pre-cut witness and its later entries would otherwise walk a length
  cut straight back, and the length cuts sit first, so a smaller state
  is what the budget buys first.

- **The sources' `applies` test for a container is conservative.** The
  seam runs pure and cannot reduce the reducible aliases (`Gwei` for
  `UInt64`), so an alias reads as a container there and the search
  answers `nothing` for such a theorem: the draw face (`scalarKind`, in
  `MetaM`) classifies the alias as a scalar and no container input
  remains. `SearchStep.nothing` carries no detail for this case, since
  the source that refused is the source that misread.

- **§9.2's `SearchM` budget counter never landed.** The sketch gives the
  search monad a budget counter for the redraw loop; the loop's budget
  is the `randomDraws` option per case, the solver's fragment caps the
  grid, and the per-run heartbeat budget (§14.3) bounds the whole, so
  `SearchM` stayed `MetaM`. The stage-4 run also corrected one stale
  expectation in the pins lib (which the stage recipe does not build):
  `EthCLSpecs.Tests.TheoremVectorsPins` expected the box lemma
  `keepsUncached_getBlockRoot` to name `getBlockRoot` as its target;
  §7.2's walk reads the conclusion's left side, and a box lemma's
  conclusion names no function under test, so the reader's answer is
  `none`, and the pin now expects that.

## Theorem vectors, stage 5

Deviations found while building the hints (the schema, the fingerprint,
the hint source, the mode, the committed files, and the recipes) against
`THEOREM_VECTORS_ARCHITECTURE.md` and the plan's stage 5.

- **The committed hints root lives in the lakefile, beside
  `theorem_vectors.outDir`.** §9.8 places the committed files in the
  spec half (`EthCLSpecs/TheoremVectors/Hints/<fork>/<thm>.json`) but
  gives the hint source, which lives in the framework half, no path to
  them. The root is build metadata the lakefile already owns (the
  `outDir` precedent), so `theorem_vectors.hintsDir` registers beside
  it with the same repository-root-relative spelling and the same empty
  default, and the `ForkBinding` stays free of build paths. The empty
  default means the fork commits no hints, which is how the
  framework-half tests run: they set neither option and the hint source
  never applies.

- **`SearchStep.candidate` carries an optional tag override.** §9.2's
  loop names the record after the proposing source's own tag, but
  §5.4's replayed witness is `.hinted orig`, with the origin the
  committed entry recorded, and one hint source replays four origins.
  The candidate now names the tag the record takes, `none` keeping the
  source's own spelling, and the loop's winner is the override or the
  source's tag.

- **A replay re-records the entries it consumed.** The command builds
  each run's hint file from the winning candidates, but a replayed
  random win cannot rebuild its entry: the random source never ran, so
  the draw memo is empty and the draw key has no answer. Dropping the
  entry would lose the random hints at the first replay, and the files
  would oscillate between builds. A replayed case writes the entry it
  read, so the file a replayed build writes is the file it read.

- **The replayed witness goes through the shrink loop again.** §9.8
  says shrink replays from the same draw, and that is what keeps the
  records byte-identical across a clean rebuild: the entry records the
  pre-shrink assignment, whose container bytes the draw memo holds and
  whose scalars the shrink does not move, and the replayed candidate
  passes through the same `shrinkWitness` call the original did. The
  records' `.ssz` bytes match the search's build byte for byte; the
  records' `source` field names `hinted-<orig>`, which is the one
  intended difference.

- **Mode `require` enforces per case, and a case with no witness falls
  through.** §9.8's table says "a hint that is missing or fails is an
  error", but the corpus carries cases no source wins
  (`isValidIndexedPayloadAttestation_eq_true_iff_checks`'s fourth false
  side), and no committed file can hold an entry for a case that has no
  vector. Enforcing on such a case would make §17.3's `require` job
  unusable, so the mode errors where the promise breaks: a case whose
  hint the check rejected, and a case whose witness came from a search.
  A case that found no witness reports `notFound` as it would in `use`
  mode.

- **The outcome's `hint` field folds the per-case attempts into one
  per-run value.** §16.1 gives the field one value per run, and a run's
  cases can disagree. The fold is reader-relevance ordered: a failure
  outranks a missing entry, a missing entry outranks a replay, and
  staleness (`stale-`) refines whichever answer it touched. `ignored`
  is mode `ignore`'s answer, and a run that searched no case carries no
  field.

- **A set but unknown `THEOREM_VECTORS_HINTS` variable is a build
  error.** §17.2 has the variable read ahead of the
  `theorem_vectors.hints` option; a value that names no mode errors
  instead of falling back, so a typo in the rebuild recipe cannot
  silently run the build in `use` mode and write half the hints.

- **The fingerprint is FNV-1a over the theorem's name, the probe's
  rendered types, the statement's parts, and the preset's shape hashes,
  and it lives on the entry.** §9.8 says "a hash of the statement and
  the input type names" without fixing the function or the place. The
  statement's parts are the hypotheses and the conclusion's sides as
  the probe rendered them; each input with a wire description
  contributes `hash` of its `SSZType` shape. The shape hashes move with
  the preset, because a derived container's caps are the preset's, so a
  file-level fingerprint would mark one preset's entries stale after
  the other preset's run, and the operative comparison is each entry's
  own `fingerprint` field, which §9.8's example does not carry. A new
  `BeaconState` field changes the shape hash and the fork's random
  hints go stale at once, the way §9.8's staleness paragraph expects. A
  plain 64-bit hash is enough: the fingerprint only flags staleness,
  and the check decides either way (§9.8).

- **The run merges its hint file unconditionally.** §9.8's update
  recipe copies the output tree over the committed files, so an
  overriding line that wins nothing must replace the preset's stored
  entries with none; otherwise a survey's candidate would outlive the
  line that overrode it and the next build would replay it under the
  override. The merge keys on the preset, so a second preset's entries
  never clobber the first's.

- **Steps 7 and 8, from the stage-4 outcome: no read past a drawn
  list's end reaches compiled code, and the scalar kinds are read
  once.** The probe gains a `safe` face: per case, per read, whether
  the read's `!`-index stays inside its collection at the candidate's
  bytes, computed from the index and the collection's element count,
  which cannot panic. The search loop, the solver's fixed points, the
  random source's points, the shrink loop, and the hint's rebuilt
  candidates all gate on it before the compiled `reads` or `check`
  runs, so the clean build prints no panic and the coupled grid skips
  an out-of-range point instead of paying for a wasted solve on a
  misgrounded formula. The statement carries each input's scalar kind,
  which the reader computed once in `MetaM`, and the sources' `applies`
  tests read that table, which is also the fix for the stage-4
  shortfall the conservative head-constant test had: an alias (`Gwei`
  for `UInt64`) now reads as a scalar in `applies` too.

- **The update recipe copies and never deletes.** §9.8's "one run of
  the update recipe refreshes them" covers changed and new hints; a
  theorem that stops winning, or whose name changed, leaves its
  committed file in place, and in `use` mode that file reads `failed` on
  every build. Deleting the stale file by hand is the fix, and the
  report is where a stale one shows.

- **The committed Gloas hints cover the ten theorems that wrote
  records.** Their sources are the four kinds the stage runs: `base`
  for `getPtcElseOffset_lt_same_slot`; `bitVec` for
  `getPtcElseOffset_lt_next_slot`,
  `convertBuilderIndexToValidatorIndex_toBuilderIndex`,
  `isBuilderIndex_convertBuilderIndexToValidatorIndex`, and
  `toBuilderIndex_convertBuilderIndexToValidatorIndex`; `seed` for the
  two window theorems, `initializePtcWindow_ge`, and
  `isValidIndexedPayloadAttestation_eq_true_iff_checks`'s true side;
  and `random` for `canBuilderCoverBid_iff`'s three cases and the
  payload-attestation theorem's three false sides. A clean build
  replays all ten (`hint: replayed`), the vector bytes match the
  search's build, and a hand-edited scalar turns its case's replay into
  a search and the run's field to `failed` while the other nine
  replay.

- **The built source's knobs, per stage 6.** §9.9's builder sketch names
  the catalog constants `[Preset] → [Config] → Knobs → BeaconState`,
  and the Gloas builders carry the seams their bodies use beside those
  two: `[CryptoBackend]` where a spec signature check reaches the seam,
  and a local `letI : HasherTag := fastHasherTag` pin, the way the fork
  interface pins it, because the run needs one concrete hasher and an
  abstract binder gives none. The probe applies a builder across
  whichever of the four seams its signature actually names
  (`applyAcrossInstances`), so the catalog's shape stays the design's
  for the caller.

- **The grid's epoch boundary reads the fork's constant.** §9.9's second
  and third grid steps are "the first epoch boundary", and the framework
  half cannot name a fork constant. `Built.epochBoundaryOf` spells the
  fork's `Const.slotsPerEpoch` from the binding's fork name, evaluates
  it compiled at the run's preset, and takes the upstream minimal value
  8 when the constant is missing or does not reduce. The binding gains
  no field.

- **`Witness/Built.lean` imports `Witness.Random`.** §9.9 runs "the same
  loop the random source runs over a draw", and that loop
  (`tryDraw`, `casePlanOf`, `drawAt`) lives in Random, so the built
  source drives it there instead of copying it. §4.1's dependency column
  names `Witness.Source` and `Witness.BitVec` only; the third import is
  the shared loop.

- **A built hint's replay goes through the cache.** §9.8's table gives
  the built row "the builder name, the knobs, and the solved scalars";
  the replay fetches those bytes through `Built.cachedBytes`, the same
  cache face the source's walk uses, so a builder runs at most once per
  build per grid step across the search, the hint derivation, and the
  replay. Without this, a replayed built witness reran the builder in
  every theorem that held one.

- **The cache stamp is the binding module's trace, per run.** §9.9
  stamps each cache entry with "the Lake trace of the fork's `Builders`
  module". The binding module is the stamp's source instead, because a
  builder's bytes also depend on the crypto seam the binding fixes
  (`withQueue` runs deposit-signature checks through it), and the
  Builders module does not import the binding. The binding's trace folds
  the Builders module's artifacts beside the fork body and the seams, so
  everything the bytes depend on invalidates the stamp. The command
  reads it once per theorem (the binding constant's parent) and hands it
  down in `SearchCtx`, beside the output root the cache lives under and
  the grid's epoch boundary; three stage-6 additions to that structure.

- **`genesis` sets `eth1_deposit_index` to the deposit count.** The
  pyspec helper the catalog row cites leaves the index at 0; a state
  whose registry already holds every deposit has processed them, so the
  builder writes the count, the value `initialize_beacon_state_from_eth1`
  gave the same field back when genesis states carried it.

- **The fork record's versions, per builder.** §9.9's `genesis` row
  says "the way the pyspec's `create_genesis_state` does", and that
  helper sets the fork's own version on both sides of the record. The
  Gloas builders follow it: `genesis`, `advanced`, and `withQueue`
  carry the fork's own version on both sides, and only `upgraded`'s
  record names two versions, its `previous_version` reading the chain's
  genesis fork version from the parent's config. A client that reads
  `previous_version` of a `genesis` vector's state as the true parent
  version reads the Gloas version instead.

- **`withQueue` fills the deposit queue only.** §9.9's catalog row
  lists "pending deposits, withdrawals, or builder payments"; the Gloas
  builder appends and drains pending deposits alone, which is the queue
  the onboarding step reads and the registry content the corpus's
  theorems need. Withdrawals and builder payments wait for a theorem
  that reads them.

- **A built hint's stability claim holds for one-container statements.**
  §9.9 says the built hint "stays valid across `Plausible` versions,
  because no generator is involved". That holds when the statement's
  only container is the state; a statement with containers beside it
  draws them, and the built entry carries those containers' `seed` /
  `size` / `draw` key beside the builder and knobs, so such an entry is
  as generator-bound as a random one. The Gloas corpus holds one such
  theorem, and the report shows it.

- **The shrink trace and the notFound entry, per stage 6 steps 8 and
  9.** A random entry carries its shrink path, one index list per
  accepted `probe.shrink` call, and its replay walks those candidates
  alone, one call per recorded entry, instead of walking every call's
  full list. A case every source failed records a `notFound` entry
  under the run's fingerprint, and `use` and `require` modes skip that
  case's search while the fingerprint stands; `ignore` mode searches
  and rewrites. The payload-attestation theorem's unsatisfiable case
  stops paying its grid walk per build, which is what keeps the clean
  recipe near one minute. The skip keys on the fingerprint alone, and
  the fingerprint covers the statement and the input shapes. A raised
  `randomDraws`, a new `with` clause, or a builder fix that makes a
  recorded case satisfiable does not re-search it. A fully covering
  seed added to a theorem whose cases all read `notFound` hits the
  seed-claim error until one rebuild recipe run refreshes the entries.

- **The stage-6 pins carry file-level instances.** The pins' drive needs
  the binding's minimal instances across many `do` statements, and a
  `letI` inside the lifted block left the statements after it without
  the earlier statements' locals and instances under this module's
  build. The pins declare four private instances at file level (the
  binding's preset, config, and crypto seam, plus the parent fork's
  config for the `upgraded` pin) and tag them
  `attribute [local instance]`, so no other test module inherits them.

- **The committed Gloas hints, after stage 6.** `canBuilderCoverBid_iff`'s
  true side and one false side hold `source: "built"`, the builder
  `withQueue` at the grid's queue step (16 validators, slot 40, queue 4),
  with the solved scalars; its other false side is `random`, because
  the built grid's walk did not satisfy that case and the draw did. Two
  of the payload-attestation theorem's false sides moved from `random`
  to `built` over the `genesis` state, their drawn attestation named
  by the entry's `seed` / `size` / `draw` fields. The drawn containers'
  key is present only when containers beside the state were drawn.

## Theorem vectors, stage 7

Deviations found while building the run shapes (the probe's run-body
builders, the executor's run rows, and the record's error value) against
`THEOREM_VECTORS_ARCHITECTURE.md` and the plan's stage 7.

- **`ProbeResult` gains `errorRepr`, defaulted to `none`.** §5.5's sketch
  carries no field the `.runError` record's `error` value could come
  from. §11.3's table names the error's `repr` as the shape's answer,
  and §12.2 records that repr string in the record's `error` field. The
  run term computes the repr inside compiled code, so the value needs a
  place in the `ProbeResult`. UTF-8 bytes cannot stand in for the field:
  the record layer writes the string, so the bytes would need decoding
  back into a string, or they would lose that the value is a string at
  all. The other shapes keep the default `none`, so the stage-2
  assemblers stay unchanged.

- **The run bodies read the run through `runPure`, with the error and
  return types taken off the action's own `StateT` spine.** §11.3's
  sketch leaves the type splicing open. A reducible `whnf` unfolds a
  monad abbrev (`GloasRun`) and stops at the `StateT` spine, which a
  full `whnf` would unfold away, and the pre-state's own type supplies
  `runPure`'s `T` with its `SSZRepr` instance, which exists because the
  pre-state crossed the byte boundary (§9.1). A rejected `.runOk` run,
  or a clean `.runError` run, assembles `agree := false`, which sends
  the record into the executor's agreement error with both sides named
  (§11.3, §18): the kernel excluded the case for the witness, so the
  mismatch is a compiler, FFI, or serialization defect.

- **`accepts` takes the render environment.** §13.1's sketch types
  `accepts : VectorRecord → Bool`, and §13.4's acceptance predicate needs
  the record's fork binding: the handler lookup, the state-type check. A
  record names its fork by tag, and only the environment resolves the tag
  to a binding, so the field takes the `RenderEnv`. The report's
  records-no-format list stays truthful, because acceptance stays complete.

- **The harness reads raw `.ssz` beside `.ssz_snappy`.** §17.4 says
  harness.py "accepts `.ssz` where it finds no `.ssz_snappy`". The resolver
  prefers the snappy file. It skips decompression for a raw one. The rule
  covers every blob the harness reads. The generated cases exercise only
  the epoch-processing pair. `--vectors` collects the rendered tree and
  skips the archive, so a vectors run needs no download. The server spawn
  moved to the repository root, where Lake and the just recipes run. The
  subpackage manifest stopped carrying the workspace's full require set
  when stage 0 added `plausible`, and `lake exe` refused to start from the
  subpackage. The raw blob's path in the request is absolute, so the
  server's own working directory no longer matters.
