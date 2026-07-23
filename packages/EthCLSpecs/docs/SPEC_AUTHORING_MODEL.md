# The Spec-Authoring Model

This document is the contract for a Lean 4 library that implements the
Ethereum consensus specification, the SSZ type system, the state-transition
function, and fork choice, for the Fulu and Gloas forks. It defines the line
between what a spec author writes and what the framework supplies. Read it
first. The two sibling documents both build on it: `FRAMEWORK_ARCHITECTURE.md`
implements each row of the contract from below, and `SPECS_ARCHITECTURE.md`
uses each row from above. Where those two need a shared word, they take it from
the glossary here rather than coining their own, so the seam between them never
drifts.

A consensus spec sits at a small intersection. Most readers know one side of
it. A reader fluent in the Python `pyspec` may not have written Lean; a reader
fluent in Lean may not know what `process_epoch` does. This document teaches
both sides as it goes, so a new contributor can read it start to finish and
understand the contract without a second source.

The thesis it earns: there is one spec body, instantiated at two
configurations, and the author names neither configuration.

This document defines *what* the DSL gives a spec author. For *how* to write the
body of a `forkdef` so it reads well, paragraphing phases, naming intermediates,
section comments, and when to split a handler, see the repo-wide
[`docs/CODING_STYLE.md`](../../../docs/CODING_STYLE.md), whose function-body
section draws several of its worked examples from this package.

---

## 1. Purpose and the shared spine

Three documents describe this library. This one is the contract. The other two
expand it from opposite sides. To keep them coherent they share four pieces of
connective tissue, all defined here, quoted there.

**The author/framework boundary table.** The canonical interface. One row per
deliverable, three columns: what the author writes, what the framework
generates, and where the framework implements it. `FRAMEWORK_ARCHITECTURE.md`
builds each "framework generates" cell; `SPECS_ARCHITECTURE.md` consumes each
"author writes" cell. The full table is Section 5 of this document.

**The fast-versus-pure duality.** The framework pre-bundles exactly two
configurations. The *fast* configuration backs the pyspec test runner; it
uses `EStateM` and a cached `Box`. The *pure* configuration backs proofs; it
uses `StateT` over `Except` and an uncached `Box`. The spec body is generic over
both and names neither. The runner, which the framework owns, instantiates the
fast configuration. A per-fork theorems module, separate from the spec body,
instantiates the pure one. This invariant is stated identically in all three
documents. Authors never see it. Section 3 derives it.

**The spec-revision pin.** Each fork records the latest upstream Python spec
version at which its whole pyspec suite passes. The pin lives in the spec,
per fork, as a checked constant. Two forks can sit at different pins at the same
time. Section 10 gives the operational definition and the discrepancy policy.

**The glossary.** The single source of truth for vocabulary, two registries:
the Lean identifiers and the coined concept-phrases. Any cross-cutting term that
either sibling document introduces is registered here first, so the vocabulary
grows by addition, never by a parallel definition somewhere else. Section 4 is
the glossary.

---

## 2. What a fork spec is, and where it stops

### 2.1 The six deliverables

A fork spec delivers six things. Hold this list in mind; the boundary table
(Section 5) mirrors it row for row, and the fork declaration model (Section 7)
explains how a later fork delivers each one as a diff over its parent.

1. **Container types.** The fork's SSZ data structures, `BeaconState`,
   `BeaconBlock`, `Attestation`, `Validator`, and the rest.
2. **Consensus-domain helpers.** The `get_*` accessors, the `compute_*`
   derivations, the `is_*` predicates, and the committee and shuffling
   functions. State-free ones are pure; accessors that read the `State` are
   monadic (Section 2.3).
3. **The state-transition function.** Slot, block, and epoch steps over
   `State`, composed into the per-block transition.
4. **The fork-choice store and its handlers.** A parallel state machine over
   `Store`, with the `on_*` event handlers.
5. **The lifecycle functions.** Genesis construction and the fork upgrade.
6. **The constants.** Grouped by tier (preset, universal, config).

Two state machines run here, in parallel. The state-transition steps thread
`State`; the fork-choice handlers thread `Store`. Both are written as monad
actions that name no concrete monad. Section 3 says why.

### 2.2 The domain line: what the author owns versus what the framework provides

The author owns the consensus logic. Everything in the six deliverables above is
the author's, including the helpers that do not change from one fork to the
next. The framework owns the plumbing: the arithmetic, the SSZ machinery, the
crypto mechanics, the effect monad, the finite-map backing, and the box
representation. None of the framework's parts mentions a validator, an epoch, a
balance, or a `State`.

This is the *domain line*, and it has one sharp test. If a helper names a
consensus concept, it is spec-owned, even when its body is identical across
forks. `getCurrentEpoch` reads `state.slot` and divides by `SLOTS_PER_EPOCH`; it
mentions a slot and an epoch, so the author writes it, in the spec. The integer
square root it might call is domain-agnostic, so the framework provides it.

Fork-invariance is a separate, within-spec question. A helper that is stable
across forks lives in the shared spec layer; a helper that varies is a per-fork
diff. Neither fact moves the helper across the domain line. Stability decides
*where in the spec* a helper lives, not *whether the framework owns it*.

The surface of a fork spec is the beacon-chain spec, the fork-choice spec, and
the lifecycle functions. The validator guide's honest-behavior duties and the
p2p networking layer are out of scope.

### 2.3 The authoring style

State-free helpers are pure functions, the `compute_*` derivations and the `is_*`
predicates over explicit arguments. An accessor that reads the `State` is a monadic
action instead, `getCurrentEpoch : StateTransition Epoch`, which reads cleanly in a
do-block and matches Lean's convention that a top-level `getX` is monadic; the
state-reading layer is uniformly monadic, with a pure core extracted only where a
later proof needs it. Crypto, the BLS verification and the signing-root construction,
runs through the framework's helper functions, never raw FFI. The framework stays invisible: a step reads like the spec it
implements, with the plumbing tucked behind the primitives of Section 6.

Two goals govern the style: extreme readability and idiomatic Lean 4.
Conformance is *behavioral*. A fork is correct when it passes the upstream test
vectors. That freedom lets the Lean rendering follow whatever reads most
naturally and ignore the shape of the Python source. The library does not mirror
the `pyspec` file structure; it re-expresses the same behavior in Lean.

Readability includes the variable names. Name a variable for what it holds. The
threaded state is `state`, a validator is `validator`, a block is `block`, a field is
`field`, a value is `value`; the extreme one-letter abbreviations (`s` for the state,
`v` for a validator, `b` for a block) are out. Short names stay only where they are
conventional and carry no domain meaning: a type variable (`H` for the hasher tag),
the monad variable, a loop index `i`. Everywhere else the longer name is the readable
one, and the readable one wins.

---

## 3. One spec body, two configurations

### 3.1 The duality

The framework bundles four implementation axes, the effect monad, the
Merkleization hasher, the finite-map backing, and the box flavour, into two
named configurations.

| Axis | `fast` (the runner) | `pure` (proofs) |
|---|---|---|
| Effect monad | `EStateM StateTransitionError State` | `StateT State (Except StateTransitionError)` |
| Hasher | `Sha256` (FFI, opaque) | `Sha256Spec` (pure-Lean, kernel-reducible) |
| Fork-choice map | `hashMap` | `treeMap` |
| Box flavour | `FastBox` (cached, `= CachedBox Sha256`) | `UncachedBox Sha256Spec` (uncached) |

The spec body is generic over every axis and commits to neither column. The
test runner, which the framework owns, instantiates the fast column. A per-fork
theorems module, which sits outside the spec body, instantiates the pure column.
Both columns elaborate from the same source. The runner gets native speed and a
warm cache; the proofs get a kernel-reducible hasher, uncached getters and
setters whose laws hold by `rfl`, and a deterministic key order. The author
writes once and gets both.

### 3.2 The section pattern, and why the header is generated

A spec module opens a Lean `section`. The header of that section, the instance
and `variable` declarations that put the right things in scope, is written by a
framework macro, not by hand. The macro cannot be mis-stated; a hand-rolled
header can. Two macros set it up, split along the seam that declarations persist
across modules while `variable`s do not. `state_preamble BeaconState`, written once in
the fork's `State` module, declares the per-fork `State` and its `modifyState` updater.
`state_section`, written at each section, opens the `section` itself and re-establishes
the `variable` line:

```lean
-- once, in the State module, after the BeaconState container:
state_preamble BeaconState
--   abbrev State := Box HasherTag.H BeaconState
--   def modifyState (f : State → State) … := …        -- concrete-domain updater

-- at each section (the macro opens the `section`; close it with `end`):
state_section
--   variable [Preset] [HasherTag]
--   variable [Config] [CryptoBackend]
--   variable {StateTransition : Type → Type}
--   variable [Monad StateTransition]
--   variable [MonadStateOf State StateTransition]
--   variable [MonadExceptOf StateTransitionError StateTransition]
```

The author opens one namespace for the whole authoring surface. `open EthCLLib.Spec`
brings in the `fork*` forms and `inherit`, the header macros, `assert` and the step
primitives, the `Const` constants, and the spec-facing helpers, so a spec file needs
no second open (`FRAMEWORK_ARCHITECTURE.md` lays out the namespace). The fork's own
declarations live in its namespace, `EthCLSpecs.Fulu` or `EthCLSpecs.Gloas`, one flat
namespace per fork.

The `variable` line carries two instance-implicit selector classes, `[Preset]`
and `[HasherTag]` (Section 8 explains the preset tiers; Section 4 the hasher
tag), the monad variable `StateTransition`, and three raw standard-library
constraints on that monad. The constraints are deliberately raw. There is no
custom capability bundle: a `StateM`-style bundle collides with a core name, and
the one thing a bundle would buy, header brevity, the macro already provides.

A step is then written as a value of type `StateTransition Unit`, generic over
the monad. The hasher stays generic too, threaded through `[HasherTag]`, which
carries the chosen hasher as a field and resolves by instance search. A free
`{H}` type variable was tried and does not thread into caller steps, so the tag
class carries it instead.

One naming note. `StateTransition` is a `Type → Type` variable in PascalCase,
which reads against the lowerCamelCase-for-variables convention. The deviation
is deliberate. `StateTransition` is a glossary term (Section 4), and seeing it at
every step teaches what the step is.

A fork-choice section uses the companion macro, which likewise opens the `section`:

```lean
-- at each fork-choice section (close it with `end`):
fork_choice_section map
--   variable [Preset] [HasherTag]
--   variable [Config] [CryptoBackend]
--   variable {map : MapKind} [FcMap map]   -- Store map's container fields boxed
--   variable {StoreTransition : Type → Type}
--   variable [Monad StoreTransition]
--   variable [MonadStateOf (Store map) StoreTransition]
--   variable [MonadExceptOf StoreTransitionError StoreTransition]
```

The fork-choice map cannot hide the way the hasher and the box flavour do. It
appears in the `Store` type itself, since the store's map-valued fields are
typed `map K V`. So `Store hashMap` and `Store treeMap` are genuinely distinct
types that coexist with no ambient "current" map, and a fork-choice section
takes `map` as an explicit type variable. `FRAMEWORK_ARCHITECTURE.md`, in its
finite-map and fork-choice store section, owns the `Store` definition.

### 3.3 What the author keeps in mind

Two rules let a step typecheck unchanged at the pure configuration. First, steps
must be total. No `partial def`. A `partial def` does not reduce in the kernel,
so it would break the pure column. Second, an unbounded loop must pick a
termination strategy: well-founded recursion by default, and the framework's
`fuelLoop` primitive when a decreasing measure resists. Section 7 and the
control-flow section of `FRAMEWORK_ARCHITECTURE.md` carry the detail.

---

## 4. The canonical glossary

The authoritative vocabulary, cross-cutting terms only. No framework internals
live here. Both sibling documents quote these entries instead of re-coining
them. The table grows by addition; a new cross-cutting term is registered here
before it appears downstream.

### 4.1 Lean identifiers

| Identifier | One-line meaning |
|---|---|
| `StateTransition` | The generic effect type a state-transition section gives its monad variable; a step is `StateTransition Unit`. |
| `StoreTransition` | The generic effect type a fork-choice section gives its monad variable; a handler is `StoreTransition Unit`. |
| `state_preamble` | Header macro, written once in the fork's `State` module, declaring the per-fork `State` abbrev and the concrete-domain `modifyState`. |
| `state_section` | Header macro opening a state-transition `section` and emitting its `variable` line (raw `Monad` / `MonadStateOf` / `MonadExceptOf` constraints, no custom bundle). |
| `fork_choice_section` | Header macro opening a fork-choice `section` and emitting its `Store map` store-machine constraints plus `{map} [FcMap map]`. |
| `StateTransitionError` | The state machine's reject type; typed constructors per failure kind (`assert`, `todo`, `outOfBounds idx bound`). |
| `StoreTransitionError` | The store machine's reject type; its own `assert` / `todo`, plus `missingKey`, and `transition` wrapping a `StateTransitionError`. |
| `Hasher` | SizzLean's Merkleization-backend class, parameterized by a tag type; unchanged by this framework. |
| `HasherTag` | The framework selector class carrying the chosen hasher as the field `HasherTag.H`. |
| `Sha256` | The FFI hasher tag (opaque, fast); the fast configuration's hasher. |
| `Sha256Spec` | The pure-Lean hasher tag (kernel-reducible); the pure configuration's hasher. |
| `State` | The fork's `BeaconState` viewed as an SSZ box: `Box HasherTag.H BeaconState`. |
| `getStateRoot` | The Merkle root of the threaded `State`, taken inside a step; keeps the cache-warmed box (`modifyGet`-shaped). |
| `stateRoot` | The Merkle root of a `State` value in hand, with the cache-warmed box; the lossless pure form for a non-monadic context that threads the box by hand. |
| `stateRoot!` | The Merkle root of a `State` value in hand, discarding the cache-warmed box; terminal-only (the `!` marks the discard, never a panic). |
| `sszGet` | Field read on a boxed value. |
| `sszUpdate` | Single-field write on a boxed value, carrying the size-proof discharge and cache maintenance. |
| `modifyState` | Multi-field update of the threaded state; the per-fork updater `state_preamble` emits, with a concrete `State → State` domain so a step writes `modifyState fun state => …` without a binder annotation. |
| `assert` | The macro for a spec assertion; renders its expression into a diagnostic descriptor and throws the section's `assert` reject (`StateTransitionError` in a state section, `StoreTransitionError` in a fork-choice section, resolved through `SpecReject`). |
| `SpecReject` | The class mapping a descriptor to an error type's `assert` / `todo` reject, so the one `assert` / `todo` work in both machines. |
| `MapKind` | The kind of a finite-map backing; the type a `map` variable ranges over. |
| `FcMap` | The class of operations a fork-choice map provides (`insert`, `lookup`, `contains`, `fold`/`keys`). |
| `Store` | The fork-choice store, a record of `FcMap`-backed maps, parameterized by the map backing: `Store map`. |
| `stateTransition` | The full per-block transition machine (the `pyspec` `state_transition`), written as a do-block. |
| `runStateTransition` | The act of discharging the `stateTransition` machine; a fork-choice handler runs it inside `onBlock`, the nested-machine bridge. |
| `fuelLoop` | The bounded-recursion primitive for loops whose decreasing measure resists a clean well-founded argument. |
| `Preset` | The class of preset-varying constants, threaded `[Preset]`. |
| `Config` | The class of config values, threaded `[Config]`. |
| `Const` | The namespace of constant abbrevs that unifies the three tiers; the author writes `Const.x`. |
| `fast` | The configuration the runner instantiates. |
| `pure` | The configuration the theorems module instantiates. |
| `initializeBeaconStateFromEth1` | The genesis-construction lifecycle entry point. |
| `upgradeToGloas` | The fork-upgrade lifecycle entry point; the single cross-fork reference. |
| `PySpecTests` | The conformance layer that runs the upstream vectors against a fork's interface. |
| `pyspecPinnedVersion` | The per-fork constant holding the pinned spec release tag (stable or pre-release). |

### 4.2 Concept-phrases

| Phrase | One-line meaning |
|---|---|
| The domain line | The boundary between author-owned consensus logic and framework-owned primitives (Section 2.2). |
| The duality | One spec body, two configurations (`fast`, `pure`), the author names neither (Section 3). |
| Behavioral conformance | A fork is correct when it passes the test vectors, which frees the Lean rendering from the Python source shape (Section 2.3). |
| The fork diff | A later fork delivered as added or changed containers, per-fork constants, and an explicitly ordered pipeline reusing the parent's step bodies (Section 7). |
| The four-layer structure | Framework, spec body, theorems module, and `PySpecTests`, by owner and run-time (Section 9). |
| The spec-revision pin | The latest upstream spec version a fork's suite passes against, recorded as `pyspecPinnedVersion` (Section 10). |
| The fork interface | The fixed entry-point signatures a fork must satisfy so `PySpecTests` can drive it, each entry point independently invocable (Section 11). |
| The inheritance mechanism | Raw syntax captured by the declaration forms and replayed in the child namespace, where unqualified references late-bind to the child's overrides; the `fork … from …` declaration names each fork's parent (Section 7). |
| The injection seams | The external factors the framework abstracts behind typeclass injection (`FcMap` / `MapKind`, `[HasherTag]`, `[CryptoBackend]`, the box flavour, the monad), so a client substitutes production, caching, or symbolic implementations. The seams section of `FRAMEWORK_ARCHITECTURE.md` owns the detail. |

---

## 5. The author/framework boundary table

The definitive interface. Each row is one deliverable. The "author writes"
column is what a spec author types; the "framework generates" column is the
framework's stable public surface for that row; the "implemented by" column
names the part of `FRAMEWORK_ARCHITECTURE.md` that builds it. A row whose
implementer is blank by the domain line says so; a row with no implementer at
all would be a gap. The rows track the six deliverables of Section 2.1, in
order, so they map one to one.

| Author writes | Framework generates | Implemented by (`FRAMEWORK_ARCHITECTURE.md`) |
|---|---|---|
| **Container types** as a field list under `forkcontainer` | the dependent `structure`, the derived `SSZRepr` (serialize, deserialize, hash-tree-root) plus `Inhabited` / `BEq` / `DecidableEq` / `Ord` / `Hashable`, and the fork-incremental inheritance | the container front-end |
| **Consensus-domain helpers** (`get_*` / `compute_*` / `is_*`, committees, shuffling) whole; state-free ones pure, state-reading accessors monadic | nothing by the domain line; the framework supplies only the primitives the other rows list | (empty cell, by Section 2.2) |
| **State-transition steps** as `forkdef` bodies over `StateTransition`, composed into the ordered pipeline | the section header (`state_preamble` / `state_section`), the monad and its constraints, and the discharge (`runStateTransition`) | the effect-monad architecture, the header macros |
| **Field access and assertions** via `sszGet` / `sszUpdate` / `modifyState` / `assert` | the access primitives, the size-proof discharge, the cache maintenance, the `assert` descriptor rendering | the state representation, the error model |
| **Fork-choice `on_*` handlers** as `StoreTransition` actions over the `Store` | `FcMap`, `Store`, and the step/check driver | the finite-map and fork-choice store |
| **Lifecycle functions** (`initializeBeaconStateFromEth1`, `isValidGenesisState`, `upgradeToGloas`) over the container constructors | the container constructors and the `genesis` / `fork` harness drivers | the container front-end, the conformance framework |
| **Arithmetic** as faithful `UInt64` transcription | the `UInt64` operations, the `Nat`-correspondence lemmas, `umax` / `umin` / `isqrt`, the type-directed `uintToBytes` width | the arithmetic layer |
| **Crypto calls** through the framework's signing-root and verify helpers | `computeSigningRoot` and friends, `isValidMerkleBranch`, the vector-typed BLS wrappers (`blsVerify` / `blsVerifySigned` / `blsFastAggregateVerify` / `blsEthFastAggregateVerify` / `blsAggregatePubkeys`) over the BLS and KZG primitives behind `[CryptoBackend]` | the crypto layer |
| **Bounded loops** as fold / `forM` / well-founded recursion, or `fuelLoop` / `fuelIterate` where the measure resists | the `Step` type, `fuelLoop` (monadic) and `fuelIterate` (pure walk) | the control-flow combinators |
| **Constants** as `Const.*` references, grouped by tier | the three-tier `Preset` / universal / `Config` system under one `Const` namespace | the preset / constant / config tier system |
| **The fork interface implementation** (the fixed entry points) | every test driver and the format-to-entry-point dispatch in `PySpecTests` | the conformance framework |

The conformance row is inverted on purpose, Section 11 explains the inversion.
The author writes only the interface implementation; `PySpecTests` owns all the
drivers.

---

## 6. The `State` from the author's view

`State` is the fork's `BeaconState` wrapped in an SSZ box:

```lean
abbrev State := Box HasherTag.H BeaconState
```

The author reads a field with `sszGet`, writes one with `sszUpdate`, and takes
the Merkle root with `getStateRoot` (or the terminal-only `stateRoot!`). The author
never constructs or unwraps the box, and never names the hasher.

```lean
-- Read the current slot, write a new one, take the post-state root.
def processSlot : StateTransition Unit := do
  let state ← get
  set (sszUpdate state with slot := sszGet state slot + 1)
  -- elsewhere, when a vector wants the post-state root:
  --   let root ← getStateRoot
```

The box carries two things the author does not see, both invisible because the
type system makes them so.

The first is the hasher, selected by the `[HasherTag]` instance. The fast
configuration and symbolic transition proofs use `Sha256`, the FFI hasher kept
opaque: equality of two roots follows from the same hash over the same buffers,
with no concrete bytes needed. Proofs that must reduce a root to concrete bytes
in the kernel use `Sha256Spec`, the pure-Lean reference. One spec body serves
every choice. SizzLean's `Hasher (H)` class stays untouched, which is what keeps
its two-hasher equivalence proofs valid.

The second is the cache flavour. The flavour constructors are `CachedBox H` (cached)
and `UncachedBox H` (uncached), generic over the hasher tag, both producing
`Box H BeaconState`. They differ in flavour, not in type. SizzLean's `FastBox` and
`PureBox` are the `Sha256`-pinned aliases (`FastBox = CachedBox Sha256`), so the fast
configuration is `FastBox` and the pure configuration, whose hasher is `Sha256Spec`,
is `UncachedBox Sha256Spec`. The flavour is chosen once, at the anchor where the state
is first built: cached for runner speed, uncached so the getter-setter laws hold by
`rfl` with no cache-coherence obligation in the proofs.

So the type-level fast-versus-pure split is the monad alone. The hasher is an
instance and the flavour is a constructor choice; both are orthogonal to the
monad and both stay invisible to the author. The fork-choice map is the one axis
that cannot hide, because `map` lands in `Store`'s own type. The container front
end never boxes a value on its own; the `State` abbrev above and the `Store`'s
boxed fields are the only places a box is named, and `sszGet` / `sszUpdate`
operate only on a box, so a raw value can never be read by mistake.

---

## 7. The step-writing primitives

A spec step uses a small, closed set of primitives. Anything outside this set
should not appear in a step body. Each primitive maps to its `pyspec`
equivalent.

| Primitive | `pyspec` equivalent | What it does |
|---|---|---|
| `assert cond` | `assert cond` | Renders `cond`'s syntax into a diagnostic descriptor and throws `StateTransitionError.assert descr` when it fails. The author writes no message; the failure describes itself. |
| `sszGet state field` | `state.field` | Reads `field` from the boxed `state`. |
| `sszUpdate state with field := value` | `state.field = value` | Writes `field`, returning a new box; carries the size-proof discharge and cache maintenance. |
| `modifyState fun state => …` | several `state.field = …` lines | Updates several fields of the threaded state at once. |
| `getStateRoot` | `hash_tree_root(state)` | Takes the threaded state's Merkle root, keeping the cache-warmed box so a later root reuses the tree. |
| `sszGetIdx xs i` / `bitlistGetIdx bs i` | `xs[i]` | Reads element `i` of an untrusted or parameter index; an out-of-range index surfaces as the typed reject `outOfBounds idx bound` through `liftErr`, never a crash. |
| `xs[i]'h.down`, after `let h ← assertH (i < size)` | `xs[i]` | Proof-carrying read of an index a validation has checked; total, no reject branch, the bad index rejected at the `assertH`. |
| do-block sequencing | statement sequence | Threads the monad; `let x ← …` binds an effectful result, plain `let` a pure one. |

```lean
def incrementSlot : StateTransition Unit := do
  modifyState fun state => sszUpdate state with slot := sszGet state slot + 1

def checkSlot (expected : Slot) : StateTransition Unit := do
  let state ← get
  assert (sszGet state slot == expected)
```

A word on the `assert` descriptor. It is a `String`, but a diagnostic one,
printed only when a result disagrees with a vector. Nothing in conformance or in
proofs branches on it; the vectors record valid-or-invalid and never a reason. So
the descriptor sits outside the stringly-typed concern, which is about strings in
*decision-making* code. The harness does branch, but on the error *constructor*,
`assert` versus `todo` versus `outOfBounds`, which is typed. The error model
section of `FRAMEWORK_ARCHITECTURE.md` owns the constructor set.

Indexed access carries the same discipline, in two forms. A read of an untrusted or
parameter index is `sszGetIdx xs i` (or `bitlistGetIdx` for a `Bitlist`), which returns the
element or the typed reject `outOfBounds idx bound` through the error channel, never a panic.
A read the author has already validated is guarded by `let h ← assertH (i < size)` and taken
as the total, reject-free `xs[i]'h.down`, whose bound is the asserted condition; the bad
index rejected at the `assertH`.

---

## 8. The fork declaration model

### 8.1 What the author delivers to add a fork

Fulu is the first implemented fork and the base. Its conceptual parent, Electra,
is not built, so Fulu declares its containers, helpers, and pipelines whole.
Gloas is a genuine diff over Fulu: a few added or changed containers, per-fork
constants, and an explicitly ordered pipeline that reuses Fulu's step bodies.

The conceptual lineage, "Fulu is Electra plus PeerDAS, Gloas is Fulu plus
ePBS", is useful as documentation. The *implemented* diff runs from Gloas over
Fulu, the one parent that exists.

### 8.2 Why a copy or alias would be wrong

When a descendant fork overrides a callee, an inherited caller has to dispatch to
the descendant's version. A symbol-level copy, or an alias, gets this wrong by
early binding. The inherited caller would keep calling the parent's callee, the
classic open-recursion (fragile-base-class) problem, and the build would stay
green while the behavior was silently wrong.

The mechanism that avoids this is source re-elaboration into a flat per-fork
namespace. Each fork is a complete, flat namespace. An unchanged parent function
is inherited by capturing the author's *raw body syntax* and re-elaborating it
inside the child namespace. There, the body's unqualified sibling calls resolve
to the child's overrides by ordinary name resolution. Late binding falls out for
free. Because the inheritance replays the author's own syntax, the sibling names
are un-stamped and bind at the child site, so no blanket hygiene override is
needed. `FRAMEWORK_ARCHITECTURE.md`, in its capturing-declaration-forms section,
owns the macro detail.

### 8.3 The parent declaration

A fork names its parent once, with a `fork` declaration in the fork's root
module:

```lean
fork Fulu            -- the base, no parent
fork Gloas from Fulu -- Gloas inherits from Fulu
```

The `fork … from …` declaration records the lineage edge in an environment
extension. It is data the resolver reads, not a generator. The bare `fork`
keyword declares the fork; `forkdef` / `forkcontainer` / `forkstruct` declare its
members. The lineage generalizes to deeper chains (`X from Y from Z`), one hop
here since Fulu is whole.

### 8.4 The three fates over two forms

The author-facing shape is a per-fork manifest of three *fates* over two *forms*.

The three fates of a parent declaration:

- **Inherit.** The declaration is unchanged in this fork.
- **Override.** The declaration replaces a parent declaration of the same name.
- **New.** The declaration introduces a name the parent did not have.

The two forms:

- **`inherit Foo`** for the inherit fate. It resolves by walking the lineage from
  the `fork … from …` data: this fork did not capture `Foo`, so the resolver
  steps to the parent and replays the parent's captured `Foo` in the child
  namespace.
- **A full declaration** (`forkdef`, `forkcontainer`, or `forkstruct`) for the
  override and new fates. The two are identical in form. Whether a parent symbol
  of that name existed is the only thing that distinguishes an override from a
  new declaration, and the author does not have to mark which.

```lean
namespace EthCLSpecs.Gloas

inherit getCurrentEpoch        -- unchanged from Fulu

forkdef processBlock : StateTransition Unit := do   -- overrides Fulu's
  ...                                                -- inherited callees here
                                                     -- bind to Gloas's overrides

forkdef processExecutionPayloadHeader : StateTransition Unit := do  -- new in Gloas
  ...

end EthCLSpecs.Gloas
```

The fork's ordered step composition, its `processBlock` and `processEpoch`
sequence, is itself an inheritable body, so a fork that does not reorder its
pipeline can `inherit` it.

### 8.5 Capture is the common base

The same mechanism inherits every kind of declaration, so capture is the shared
base of all three forms, and each form layers its own generation on top:

- `forkdef` captures, for steps and helpers.
- `forkcontainer` captures and generates the SSZ instances, for SSZ containers.
- `forkstruct` captures and runs ordinary `deriving`, for non-SSZ structures
  like `Store`, `FcNode`, and `LatestMessage`.

The shared `fork` prefix marks the common behavior: every form is captured for
per-fork replay. All three are producers into one syntax store; `inherit` is the
single consumer. Late binding is needed for all of them. An inherited container
field whose type names an overridden container, or whose capacity names an
overridden constant, must resolve to the child fork's version.

Containers and structures follow the same two cases as functions. An unchanged
one is `inherit`ed; a changed or new one is declared in full. There is no
field-merge or append form. SSZ field order is load-bearing, so a fork that
changes a container restates its complete field list, explicit on the page and
checked by conformance, rather than computing the order from a parent. A full
declaration regenerates the SSZ instances over its field list.

Two consequences the author should expect. First, the replayed declaration
resolves against whatever is in scope at the `inherit` site, so the author owns
the preamble. The section header (Section 3), any `open` or notation, and the
constants the body uses must be in scope in the child before `inherit`. The
framework does not reconstruct the preamble; a missing one fails to elaborate
with a plain unknown-identifier error. Second, inheritance is by symbol, so a
property proved about a caller is proved per fork: Fulu's and Gloas's
`processOperations` are distinct symbols. Proof reuse across forks is a known
cost, acceptable while proofs are deferred (Section 9).

---

## 9. The four-layer structure

Four layers, by owner and run-time.

| Layer | Owner | When it runs | What it is generic over |
|---|---|---|---|
| **Framework** | the framework | n/a (it is the machinery) | everything; invisible to the author |
| **Spec body** | the author | both configurations | `[Preset]`, `[HasherTag]`, the monad (and `map` in fork-choice) |
| **Theorems module** | the author, per fork | the pure configuration | nothing; it pins `pure` and states properties |
| **`PySpecTests`** | the framework | the fast configuration | nothing; fork-agnostic, drives the fork interface |

The framework provides the machinery and is invisible to the author. The spec
body is what the author writes, generic over the preset, the hasher tag, and the
monad, naming no configuration. The theorems module is per fork, sits outside the
spec body, instantiates the pure configuration, and states properties. Proofs are
deferred past the first milestone, so this layer is reserved rather than
populated. The spec body stays proof-agnostic so the theorems can be added later
without rework. `PySpecTests` is the conformance layer: it runs the upstream
vectors against a fork by driving the fork's interface (Section 11) at the fast
configuration. It is written once, fork-agnostic, and owns every per-format
detail; a fork becomes testable by satisfying the interface, with no test wiring
of its own.

Dependencies flow one way, and the framework and spec body are separate packages, so
the framework cannot import the spec and the layering is build-enforced. The framework
builds on SizzLean (the SSZ machinery, `Box`, `Hasher`) and the crypto FFI (BLS, KZG).
The spec body builds on the framework. The theorems module builds on the spec body.
`PySpecTests` splits along the fork interface: its generic driver lives in the
framework and is written against that interface, so it builds on no concrete spec,
while its runner lives with the spec body and instantiates the driver at a fork. If
proofs ever need mathlib, the theorems layer is the containment boundary, kept in a
standalone package so mathlib stays off the framework, spec, runner, and `PySpecTests`
paths, the same discipline the repository applies to its Poseidon proofs.
`SPECS_ARCHITECTURE.md`, in its module-layout section, places each layer in the
package structure and says what crosses each boundary.

---

## 10. The spec-revision pin and the discrepancy policy

The pin is the latest upstream Python spec version for which a fork's Lean
implementation passes the full pyspec suite. It is recorded as a constant in
the fork:

```lean
def pyspecPinnedVersion : String := "v1.7.0-alpha.11"
```

The name is lowerCamelCase, per the Lean convention; the value is the release
tag, stable or pre-release. The pin is a checked value in the spec, not prose,
and `PySpecTests` reads it to select the vector release. One tag covers both the
spec version and the matching `consensus-spec-tests` vectors, which release
together and are what the suite runs against. The pin lives per fork, in the
spec, outside the framework. Two forks can sit at different pins at the same
time.

The discrepancy policy is directional. The vectors are the operational proxy for
the spec, so a divergence between Lean and a vector almost always means the Lean
is wrong, and the fix goes in Lean. The spec markdown is the ultimate authority
and overrides only in the rare case where a vector contradicts it; when that
happens, the divergence is recorded. `SPECS_ARCHITECTURE.md`, in its
spec-revision-tracking section, states the directional policy in full and keeps
the record.

---

## 11. The inverted conformance contract

The conformance contract is inverted. The author implements an interface rather
than wiring tests.

The framework defines a fixed *fork interface*: the entry-point functions every
fork must provide, with fixed signatures, expressed as a typeclass the fork
instantiates. The entry points are `stateTransition`, `processSlots`, the
individual `process_*` steps and operation handlers, the reward and penalty
delta functions, the `on_*` fork-choice handlers,
`initializeBeaconStateFromEth1`, and the fork upgrade (`upgradeToGloas`,
`upgradeToHeze`). Each entry point is
independently invocable, so a single-operation vector can drive a single handler
without running a whole block.

A fork implements the interface. Omit or mis-sign an entry point and the fork
fails to satisfy it, breaking the build. The typechecker is the contract.

The per-step operation and epoch axes are realized as two family methods
(`runOperation`, `runEpochSubstep`) over a typed handler tag (`OpKind` / `EpochStep`),
not one method per step, so the interface stays small. The tag keeps the contract on
the typechecker here too: a fork matches it exhaustively, so omitting a handler is a
compile error, and a handler the fork does not drive is an explicit `todo` arm rather
than a silent fallthrough. The wire handler name from the case path is parsed to its tag
once, at the driver boundary; an unrecognized name is out of scope.

`PySpecTests` owns all the test-running knowledge. For each vector format it
knows how to decode the case, which interface entry point to drive, and what
"valid" or "rejected" means:

| Format | Entry point driven | What "pass" means |
|---|---|---|
| `sanity/blocks` | `stateTransition` | the full transition's post-state root matches |
| `epoch_processing/*` | a single `process_*` epoch sub-step | the sub-step's post-state root matches |
| `operations/*` | a single operation handler | the operation's post-state root matches |
| `rewards/*` | a single delta function | the delta function's output matches |
| `genesis` | `initializeBeaconStateFromEth1` | the constructed state's root matches |
| `fork` | `upgradeToGloas` | the upgraded state's root matches |
| `fork_choice` | the `on_*` handlers | the interleaved store checks pass |

So the author writes no handler table and maps nothing to tests. They implement
the interface, and `PySpecTests`, written once and fork-agnostic, runs every
format against it. "Rejected" means the entry point threw any error constructor;
the vector records only valid-or-invalid, so the reject reason stays diagnostic
and is never matched against it (Sections 7 and the error model section of
`FRAMEWORK_ARCHITECTURE.md`). The dispatch correctness that lets an inherited
entry point resolve to the right fork's override is the inheritance concern of
Section 8.

`FRAMEWORK_ARCHITECTURE.md`, in its conformance-framework section, owns the
driver shapes, the Python input side, and the per-worker Lean server.
`SPECS_ARCHITECTURE.md`, in its conformance-plan section, lists which formats
each fork runs.
