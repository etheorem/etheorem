# The Framework Architecture

This document describes the framework and DSL that implement the contract in
`SPEC_AUTHORING_MODEL.md`. That document draws the line between what a spec
author writes and what the framework supplies, and its Section 5 boundary table
lists, row by row, what the framework generates. This document builds each of
those "framework generates" cells from below. Read `SPEC_AUTHORING_MODEL.md`
first; it carries the canonical glossary and the boundary table, and this
document quotes both rather than re-defining them. The third sibling,
`SPECS_ARCHITECTURE.md`, sits above this one and uses the same surface from the
author's side.

A consensus spec sits at a small intersection. A reader fluent in the Python
`pyspec` may not have written a Lean macro; a reader fluent in Lean may not know
what a hash-tree-root is. This document teaches both sides as it goes. Where a
Lean idiom is load-bearing, it gets a sentence the first time it appears; where
a spec term needs grounding, it gets one too.

The framework owns the plumbing. It owns the arithmetic, the SSZ machinery, the
crypto mechanics, the effect monad, the finite-map backing, and the box
representation. None of its parts names a validator, an epoch, a balance, or a
`State`. That is the domain line of `SPEC_AUTHORING_MODEL.md`, applied from the
implementer's side: a framework primitive is domain-agnostic, and every
consensus-aware helper lives in the spec.

The operational target is conformance. A fork is correct when it passes the
upstream test vectors, and that freedom shapes every choice below: pick the
implementation that passes vectors and proves cleanly, then expose the seam so a
production client can swap a different one in. Production concerns, batch crypto,
persistent storage, live in the injected dependencies, not in the framework
core. Proofs are deferred past the first milestone, and the framework's job
there is to not foreclose them.

---

## 1. Framework overview and the injection seams

The framework abstracts every external factor behind a typeclass that a client
injects. `SPEC_AUTHORING_MODEL.md` registers these collectively as *the
injection seams*; this section owns the detail of each one. The pattern is
uniform. A spec step or handler names an abstract capability through an
instance-implicit class, and a consumer, the test runner, a proof, or a future
production client, picks the concrete instance at the call boundary. The spec
body commits to none of them.

These seams carry the design.

| Seam | Class / variable | What it abstracts | Fast instance | Pure instance |
|---|---|---|---|---|
| Preset constants | `[Preset]` | preset-varying constants (`SLOTS_PER_EPOCH`, vector widths) | `minimal` / `mainnet` | a fixed preset |
| Config values | `[Config]` | config-tier values (fork versions, genesis delay) | the test config | a fixed config |
| Merkleization hasher | `[HasherTag]` | the SSZ hash backend, carried as `HasherTag.H` | `Sha256` (FFI, opaque) | `Sha256Spec` (pure-Lean) |
| Crypto backend | `[CryptoBackend]` | BLS verify/aggregate, KZG | caching FFI | symbolic (abstract `verify`) |
| Execution engine | `[ExecutionEngine Payload Tx]` | EL-answered predicates (`is_inclusion_list_satisfied`) | optimistic global instance | a local refuting/real instance |
| Finite-map backing | `{map : MapKind} [FcMap map]` | the fork-choice store's maps | `hashMap` | `treeMap` |
| Box flavour | smart constructor at the anchor | cache strategy of the boxed state | `FastBox` (cached, `= CachedBox Sha256`) | `UncachedBox Sha256Spec` (uncached) |
| Effect monad | `{StateTransition : Type → Type}` | the state-threading effect | `EStateM` | `StateT ∘ Except` |

Most of these hide completely behind instance resolution or a constructor choice
at the anchor, so the author never names them. The fork-choice map is the one
exception, and it cannot hide: `map` lands in the `Store` type itself, so
`Store hashMap` and `Store treeMap` are genuinely distinct types. A fork-choice
section takes `map` as an explicit type variable for that reason. The finite-map
and fork-choice store section below carries the consequence.

The injection discipline pays off three ways. The runner gets native speed: the
FFI hasher, the cached box, the hash-map, and a verify cache that memoizes
repeated calls. Proofs get tractability: a kernel-reducible hasher, an uncached
box whose getter-setter laws hold by `rfl`, a tree-map with deterministic key
order, and an abstract crypto backend that carries no compiler axioms. A future
production client gets extension points: a persistent `Store` map is a new
`MapKind` instance, batched verify is a new `[CryptoBackend]`, and neither
touches the spec or the framework core. The framework is *open* in the
open/closed sense; a new backing arrives as a new instance, not as an edit to an
existing match.

The framework's own dependencies are two. SizzLean supplies the SSZ machinery:
the `SSZRepr` class and its deriving handler, the `Box`/`view`/`hashTreeRoot`
cache, the `Hasher` class, and the generic `sszGet` / `sszUpdate` access macros.
A crypto FFI library supplies BLS and KZG. The consensus-spec container library
that preceded this one is a design reference, not a dependency. Nothing the
framework ships mirrors the Python source file structure; the rendering follows
what reads naturally in Lean and answers only to the vectors.

---

## 2. The DSL realization strategy

The DSL is a library of typeclasses plus the section pattern, with targeted
custom syntax where instance boilerplate or expression capture earns a macro.
There is no wholesale custom-syntax language and no external transpiler. Authors
write Lean against the framework's interfaces, and the framework generates the
plumbing at macro-expansion inside Lean.

Three positions fix the strategy.

**Library-first, custom syntax where it earns its keep.** Steps, helpers, and
pipeline composition are plain Lean. A step is a `forkdef` over the abstract
`StateTransition` monad with the section's raw constraints in scope, and its body
is an ordinary do-block calling library functions: `sszGet`, `sszUpdate`,
`modifyState`, `assert`. `forkdef` is `def`-shaped. The only thing it adds over a
plain `def` is the syntax capture that powers fork inheritance. Custom syntax is
reserved for four places where a macro genuinely improves the page: the capturing
declaration forms (`forkdef`, `forkcontainer`, `forkstruct`), the header macros
(`state_preamble`, `state_section`, `fork_choice_section`), the `assert` macro (which renders its
expression into the error descriptor), and `inherit` (the inheritance consumer).
Everything else is a function call.

**Generation by macro, not external codegen.** The framework generates the SSZ
instances, the inherited per-fork copies, and the discharge at macro-expansion.
Access stays SizzLean's generic `sszGet` / `sszUpdate`; the framework generates
no per-field lenses. The container front-end below makes this concrete: one
field-list declaration expands into the dependent `structure` and its derived
instances, with reads and writes left to SizzLean's macros. There is no
higher-level description language compiled to Lean; the Lean is the description.

**Authored fresh.** The new specs are written against the framework, which
auto-generates what earlier hand-written experiments produced by hand. The design
references inform the shape, then the framework regenerates that shape
mechanically.

Cross-cutting discipline lives here too. `set_option` and `open` stay tight to
the section that needs them, with `autoImplicit false` per file and no
file-scope leakage. The custom forms must report author errors in spec terms: a
mistyped field or a missing interface entry point reports an unknown identifier
or an unsatisfied instance, not a macro-internal trace. The lakefile stays
declarative; macro machinery and the C shim use Lake's API rather than ad-hoc
scripts.

**The namespace layout.** The framework lives under one top namespace, `EthCLLib`,
and gathers the author-facing surface into a single sub-namespace, `EthCLLib.Spec`,
so a spec file opens exactly one namespace to write a spec. `open EthCLLib.Spec`
brings in the `fork*` forms and `inherit` (declared as `scoped` syntax, so the open
activates the macros along with the names), the header macros
`state_preamble` / `state_section` / `fork_choice_section`, `assert` and the step primitives, the `Const`
surface, the `Preset`/`Config`/`HasherTag` classes the section references, and the
spec-facing functions (`computeSigningRoot`, `computeDomain`, `isValidMerkleBranch`,
`fuelLoop`). What the author never writes against stays out of it: the generic
`PySpecTests` driver sits under `EthCLLib.PySpecTests`, and the macro internals and
cache wiring are `private` or under `EthCLLib.Internal`. Methods on framework types
use ordinary dot-notation (`FcMap.lookup`, `Box.view`), so the public surface stays
one level deep and the glossary's unqualified vocabulary reads as written.

---

## 3. The capturing declaration forms

Adding a later fork is a diff over its parent. When a descendant overrides a
callee, an inherited caller has to dispatch to the descendant's version. A
symbol-level copy or an alias gets this wrong by early binding: the inherited
caller keeps calling the parent's callee, the classic open-recursion problem, and
the build stays green while the behavior is silently wrong. The mechanism that
avoids this is source re-elaboration into a flat per-fork namespace.

Each fork is a complete, flat namespace. An unchanged parent declaration is
inherited by capturing the author's raw body syntax and re-elaborating it inside
the child namespace. There, the body's unqualified sibling calls resolve to the
child's overrides by ordinary name resolution. Late binding falls out for free.
Because the inheritance replays the author's own syntax, the sibling names are
un-stamped and bind at the child site, so no blanket hygiene override is needed.
`SPEC_AUTHORING_MODEL.md` registers this as *the inheritance mechanism*.

### 3.1 One capture base, three forms

The same capture powers every kind of declaration, so capture is the shared base
and each form layers its own generation on top.

| Form | Captures | Generates on top | For |
|---|---|---|---|
| `forkdef` | the raw body syntax | nothing beyond a `def` | steps and helpers |
| `forkcontainer` | the raw field list | the SSZ instances (the container front-end) | SSZ containers |
| `forkstruct` | the raw field list | ordinary `deriving` only | non-SSZ structures (`Store`, `FcNode`, `LatestMessage`) |

All three are producers into one syntax store, keyed by fork and name. `inherit`
is the single consumer. The shared `fork` prefix marks the common behavior: every
form is captured for per-fork replay. Late binding is needed for all three. An
inherited container field whose type names an overridden container, or whose
capacity names an overridden constant, must resolve to the child fork's version,
and re-elaboration in the child namespace delivers that.

### 3.2 The parent declaration

A fork names its parent once, with a `fork` declaration in the fork's root
module.

```lean
fork Fulu            -- the base, no parent
fork Gloas from Fulu -- Gloas inherits from Fulu
```

The `fork … from …` declaration records the lineage edge in an environment
extension. It is data the resolver reads, not a generator. The bare `fork`
keyword declares the fork; `forkdef` / `forkcontainer` / `forkstruct` declare its
members. The lineage generalizes to deeper chains (`X from Y from Z`); the
current build has one hop, since Fulu is whole and Gloas is its diff.

### 3.3 The two forms over three fates

The author-facing shape is a per-fork manifest of three *fates* expressed through
two *forms*. A declaration is **inherited** (unchanged from the parent),
**overridden** (replacing a parent declaration of the same name), or **new**
(introducing a name the parent did not have).

`inherit Foo` covers the inherit fate. It resolves by walking the lineage from the
`fork … from …` data: this fork did not capture `Foo`, so the resolver steps to
the parent and replays the parent's captured `Foo` in the child namespace. A full
declaration (`forkdef`, `forkcontainer`, or `forkstruct`) covers the override and
new fates. The two are identical in form. Whether a parent symbol of that name
existed is the only thing that tells them apart, and the author does not mark
which; the resolver knows from the lineage.

```lean
namespace EthCLSpecs.Gloas

inherit getCurrentEpoch        -- unchanged from Fulu

forkdef processBlock : StateTransition Unit := do   -- overrides Fulu's;
  ...                                                -- inherited callees here
                                                     -- bind to Gloas's overrides

forkdef processExecutionPayloadHeader : StateTransition Unit := do  -- new in Gloas
  ...

end EthCLSpecs.Gloas
```

The fork's ordered step composition, its `processBlock` and `processEpoch`
sequence, is itself an inheritable body, so a fork that does not reorder its
pipeline can `inherit` it.

### 3.4 Containers inherit or rewrite

Containers and structures follow the same two cases as functions. An unchanged one
is `inherit`ed; a changed or new one is declared in full. There is no field-merge
form, no append form, and no macro-level `extends`. SSZ field order is
load-bearing for serialization and Merkleization, so a fork that changes a
container restates its complete field list. The order stays explicit on the page
and checked by conformance, rather than computed from a parent by some merge rule
the reader cannot see. A full declaration regenerates the SSZ instances over its
field list.

Two consequences the author should expect. The replayed declaration resolves
against whatever is in scope at the `inherit` site, so the author owns the
preamble: the section header, any `open` or notation, and the constants the body
uses must be in scope in the child before `inherit`. The framework does not
reconstruct the preamble; a missing one fails to elaborate with a plain
unknown-identifier error, which is the legible-errors discipline at work.
Inheritance is by symbol, so a property proved about a caller is proved per fork:
Fulu's and Gloas's `processOperations` are distinct symbols. Proof reuse across
forks is a known cost, acceptable while proofs are deferred.

---

## 4. The preset / constant / config tier system

Spec constants split into three tiers, and the framework unifies all three under
one `Const` namespace so the author writes `Const.x` and never classifies the
tier. `Preset` and `Config` are **classes**, threaded instance-implicit
(`[Preset]`, `[Config]`), not value-implicit binders.

The value-implicit framing fails, and the failure is concrete. A bare constant
like `slotsPerEpoch` has no explicit argument to infer a `{p : Preset}` binder
from, so the elaborator errors with "don't know how to synthesize implicit
argument," and a config value appears in no type at all, so it can never be
inferred. Instance resolution solves both: it finds the in-scope instance with
nothing to unify against. That is why the tiers are classes.

| Tier | Class | Shapes a type? | Example `abbrev` | Auto-carries |
|---|---|---|---|---|
| Preset | `class Preset` | yes (vector widths) | `Const.slotsPerEpoch := Preset.slotsPerEpoch` | `[Preset]` |
| Universal | none | no | `Const.farFutureEpoch : Epoch := 2^64 - 1` | nothing |
| Config | `class Config` | no | `Const.genesisForkVersion := Config.genesisForkVersion` | `[Config]` |

Each tier is an `abbrev` whose body is a class projection (for the two class
tiers) or a literal (for the universal tier). A preset abbrev carries `[Preset]`;
the universal abbrev carries no binder and reads identically at the call site; the
config abbrev carries `[Config]`. The mechanism that makes each abbrev carry only
the binder its body uses is a single `section variable [Preset] [Config]` opened
in the `Const` namespace: Lean attaches a `variable` to a declaration only when
the body mentions it, so the preset abbrevs pick up `[Preset]`, the universal one
picks up neither, and the config one picks up `[Config]`.

```lean
namespace Const
section
variable [Preset] [Config]

abbrev slotsPerEpoch : Nat := Preset.slotsPerEpoch          -- carries [Preset]
abbrev farFutureEpoch : Epoch := 2 ^ 64 - 1                 -- carries nothing
abbrev genesisForkVersion : Version := Config.genesisForkVersion  -- carries [Config]

end
end Const
```

Because the preset tier shapes types, a container's field widths read as
`Const.*` and reduce to literals when the preset instance is concrete. A field
typed `Vector Root Const.slotsPerHistoricalRoot` becomes a fixed-width vector once
`[Preset]` resolves to `minimal` or `mainnet`, and the reduction holds by `rfl`.
Config never shapes a type; preset does. The config tier is low-traffic at first,
threaded the same way from day one so it costs nothing to grow.

The concrete instances are `@[reducible] def`s the runner provides at the test
boundary, not instances registered globally. Keeping them unregistered is what
lets `minimal` and `mainnet` coexist without clashing. The runner selects per
test by injecting the instance, either explicitly at the call (`@stateTransition
mainnet cfg …`) or, for a runtime choice, with `letI : Preset := selectPreset
name` followed by a bare call. The `@[reducible]` attribute matters for proofs:
it lets values reduce by `rfl` and `native_decide` and lets type-level widths
reduce by `rfl`, so a concrete-preset proof sees through the instance to the
literal underneath.

Whether a feature exists in a fork is an orthogonal axis. The fork diff expresses
it, not a `Preset` or `Config` field.

---

## 5. The container front-end

`forkcontainer` is a declaration generator over SizzLean's machinery, not an
access layer. SizzLean owns the access machinery and the framework reuses it
unchanged: the `SSZRepr` class and its `deriving SSZRepr` handler, `Box` / `view`
/ `hashTreeRoot` and the cache, and the generic `sszGet` / `sszUpdate` macros that
carry the size-proof discharge and cache maintenance. From one field-list
declaration `forkcontainer` produces:

- the dependent `structure`, parameterized over the `[Preset]` instance;
- the derived `SSZRepr` (serialize, deserialize, hash-tree-root) through
  SizzLean's handler;
- `Inhabited`, `BEq`, `DecidableEq`, `Ord`, and `Hashable`;
- the fork-incremental inheritance through the capture base of the capturing
  declaration forms section.

```lean
forkcontainer Checkpoint where
  epoch : Epoch
  root  : Root
-- expands (sketch) to:
--   structure Checkpoint [Preset] where
--     epoch : Epoch
--     root  : Root
--   deriving Inhabited, BEq, DecidableEq, Ord, Hashable
--   -- then SizzLean's SSZRepr deriving handler over the field list
```

Every container is `[Preset]`-parameterized uniformly, even a preset-free one like
`Checkpoint`. The macro never has to classify which fields need the binder, and
two concrete-preset instances of a preset-free container are definitionally equal,
so the uniformity costs nothing. The derive is always the full `SSZRepr`. There is
no hash-tree-root-only tier: carrying an unused `deserialize` costs nothing, and
the only real split is SSZ versus non-SSZ, which is exactly the split between
`forkcontainer` and `forkstruct`.

`forkcontainer` produces no access code. Reads and writes are SizzLean's generic
`sszGet` / `sszUpdate` macros, so the framework generates no per-field lenses and
the author reads `sszGet checkpoint epoch` against any container the macro built.

The one substantive piece of new work this front-end requires is making `SSZRepr`
derive for a `[Preset]`-parameterized container whose field widths are symbolic
(`Const.*`) until the preset instance is concrete. SizzLean's deriving handler
splices caps symbolically and reduces them once the preset is fixed, so the fix
lives in the dependency, not in a workaround here. That work is the
already-landed SizzLean change that derives `SSZRepr` over preset-resolved
symbolic caps.

### 5.1 The boxing model

`forkcontainer` always declares the raw type, because the raw type is
unavoidable. A box wraps it, subfields nest it, and genesis constructs it. It
never produces a box. The threaded `State` is the one named boxed handle (the
state representation section owns it); the `Store`'s container-valued fields write
`Box HasherTag.H X` inline; components like `Validator` and `Attestation` stay raw,
used in fields and as list elements. Safety is free from the type system: `sszGet`
and `sszUpdate` operate on a `Box`, so the threaded state is necessarily boxed and
a raw value cannot be accessed by mistake.

Fork-incremental declaration uses the inheritance mechanism: raw field-list
capture replayed in the child namespace, so inherited field types and capacity
constants late-bind to the child's overrides. Two cases, the same as for
functions. An unchanged container is `inherit`ed; a changed or new one is declared
in full. Gloas's `BeaconState` (it replaces `latestExecutionPayloadHeader` with
`latestBlockHash` in place, then adds the ePBS fields) and its `BeaconBlockBody`
(it drops `executionPayload`) are both full redeclarations; the brand-new ePBS
containers are fresh declarations; the unchanged containers are `inherit`ed.

---

## 6. The error model

Two error types, one per state machine, with the store type composing the state
type. The error model is drafted before the effect-monad architecture, because the
monad's exception parameter is one of these types.

```lean
inductive StateTransitionError where
  | assert (descr : String)          -- a spec assertion failed
  | todo (what : String)             -- an unimplemented branch
  | outOfBounds (idx bound : Nat)    -- indexed access past the end

inductive StoreTransitionError where
  | assert (descr : String)
  | todo (what : String)
  | missingKey (key : Root)          -- an FcMap lookup found nothing
  | transition (e : StateTransitionError)  -- a nested-transition failure
```

The split is principled. `outOfBounds` is state-side; `missingKey` is store-side;
both machines carry `assert` and `todo`; and only the store type embeds the state
type, because `onBlock` runs the state machine inside the store machine and a
transition failure has to surface (the effect-monad architecture section owns the
bridge).

Constructors carry typed terms per failure kind rather than a baked string, in
keeping with the project's stringly-typed-is-a-smell principle. The two exceptions
are `assert`'s `descr` (rendered from the asserted expression's syntax) and
`todo`'s `what`. Both are diagnostic strings, printed only on a vector mismatch and
never branched on, since the vectors record valid-or-invalid and never a reason.
The error *constructor* is what is load-bearing, and the pyspec harness reads
it in its classify mode:

| Constructor | Classify-mode meaning |
|---|---|
| `assert` | an expected rejection; a vector marked invalid should hit one |
| `todo` | an unimplemented branch; flagged out-of-scope, not counted as a rejection |
| `outOfBounds` / `missingKey` | a smell; the spec should not hit these on well-formed input, so they surface as likely bugs |

### 6.1 `todo` as the deferral work-queue

A `todo` is a deliberate deferral, not an abandoned path. It marks a branch with a
documented claim, the `what` string plus a classify-mode annotation, that no
in-scope vector reaches it. A vector that does reach one fails loudly as `todo`
rather than passing silently, so a mis-judgment is caught by the safety net rather
than hidden. This makes `todo` the work-queue of the conformance development loop:
author a step, leave its not-yet-wired branches as `todo`, run the subset, and let
classify mode point to the `todo`s a vector actually hits.

The crypto layer is the most common home for `todo`. The `[CryptoBackend]`
verify-gates are pervasive and the FFI backend is the latest-bound dependency, so
crypto-gated branches get stubbed first and filled in as the backend and the
vectors come online. The `todo`s that remain are then provably unreachable in
scope.

### 6.2 `RunError`: the runner layer above the spec rejects

The two error types above are *spec* rejects, consensus outcomes. Deserializing a
vector's SSZ bytes is a separate, *runner* concern: a parse failure is a bug in our
decoder or container types, not a rejection the spec made. So decode failures live one
layer up, in a runner error parameterized by the spec reject it may also carry:

```lean
inductive RunError (E : Type) where
  | decode (what : String)   -- the runner could not deserialize the vector bytes
  | spec   (e : E)           -- a genuine spec reject, classified by E's own classify
```

Every `ForkInterface` method returns `Except (RunError …) …`. `RunError.classify` (defined
over a `Classify` class instanced for the two spec error types) sends `decode → likelyBug`
(a well-formed vector decodes) and `spec e → e.classify`, and `RunError.ofSpec` lifts a
spec-level `Except` into the runner error once a method crosses from decoding into spec code.
This keeps the spec error types pure and replaces two earlier hacks that spelled a runner
concern in the spec's vocabulary: a fabricated `outOfBounds 0 0` on the state path and an
`assert "… decode failed"` on the fork-choice anchor path. A decode failure is now named for
what it is and cannot masquerade as a consensus reject.

---

## 7. The effect-monad architecture and the header macros

Spec steps are written in an abstract monad and instantiated two ways. The fast
configuration uses `EStateM StateTransitionError State` and backs the runner; the
pure configuration uses `StateT State (Except StateTransitionError)` and backs
proofs. The section carries three raw standard-library constraints on the monad
variable, `[Monad m]`, `[MonadStateOf State m]`, and `[MonadExceptOf
StateTransitionError m]`, the shape the design references used.

There is no custom capability bundle. A `StateM`-style bundle was rejected on two
findings. `StateM` is a core-reserved name, so a bundle would collide with it. And
the one thing a bundle would buy, header brevity, the header macro below already
provides without a class. So the constraints stay raw.

### 7.1 The header macros

The header is written by framework macros, not by hand, so the author cannot
mis-state it, and it splits along the seam that declarations persist across modules
while `variable`s do not. `state_preamble BeaconState`, written once in the fork's
`State` module, declares the `State` abbrev and its concrete-domain `modifyState`.
`state_section`, written at each section, opens the `section` and emits the `variable`
line; `fork_choice_section map` does the store counterpart.

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

The `variable` line carries the two instance-implicit selector classes `[Preset]`
and `[HasherTag]`, the monad variable `StateTransition`, and the three raw
constraints on it. A step is then a value of type `StateTransition Unit`, generic
over the monad. The hasher stays generic too, threaded through `[HasherTag]`,
which carries the chosen hasher as a field and resolves by instance search. A free
`{H}` type variable was tried and does not thread into caller steps (the same
metavariable failure a value-implicit `{p}` had), so the tag class carries it
instead.

The monad variable is named `StateTransition` in PascalCase, against the
lowerCamelCase-for-variables convention. The deviation is deliberate.
`StateTransition` is a glossary term, and seeing it at every step teaches what the
step is.

The fork-choice section uses the companion macro, which likewise opens the `section`.

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

The fork-choice map cannot hide the way the hasher and the box flavour do, because
it appears in the `Store` type itself. So `fork_choice_section` emits `{map}
[FcMap map]` explicitly, and `Store hashMap` and `Store treeMap` coexist as
distinct types with no ambient "current" map. The store machine carries its own
three raw constraints, `[Monad m]`, `[MonadStateOf (Store map) m]`, and
`[MonadExceptOf StoreTransitionError m]`, with no `StoreM` bundle, for the same
reasons the state side has none.

### 7.2 Discharge and the nested-machine bridge

Discharge is a consumer concern. The `.run` of the monad stays out of the spec
body, which is generic over the monad; the runner and the theorems module
discharge it. The runner pins `[Preset]`, `[HasherTag]`, and the concrete monad at
the entry point, and the inner steps share the section's instances.

The fork choice runs a full state transition inside the `onBlock` handler. The
`runStateTransition` bridge runs the inner `StateTransition` machine from a
`StoreTransition` handler and maps any inner failure to
`StoreTransitionError.transition`, the wrapper constructor from the error model.

```lean
def onBlock (signedBlock : SignedBeaconBlock) : StoreTransition Unit := do
  let pre ← getPreState signedBlock.message.parentRoot   -- a boxed State from the Store
  let post ← runStateTransition pre (stateTransition signedBlock)
  -- runStateTransition discharges the inner machine and maps
  -- StateTransitionError → StoreTransitionError.transition
  storePostState signedBlock post
```

The primitives a step uses are a small, closed set: `assert` and the proof-returning
`assertH`, `modifyState`, `set`, `throw`, `todo`, the `sszGet` / `sszUpdate` access pair,
and the reject-reads `sszGetIdx` / `bitlistGetIdx`. Anything outside this set should not
appear in a step body.

---

## 8. The state representation

`State` is the fork's `BeaconState` wrapped in an SSZ box, generic over the hasher
through the `[HasherTag]` selector class.

```lean
abbrev State := Box HasherTag.H BeaconState
```

The author reads a field with `sszGet`, writes one with `sszUpdate`, takes the
Merkle root with `getStateRoot`, and never constructs or unwraps the box or names the
hasher. The box carries two things the author does not see, both invisible because
the type system makes them so.

The first is the hasher, selected by `[HasherTag]`. SizzLean's `Hasher (H)` class
stays untouched, which is what keeps its two-hasher equivalence proofs valid. The
framework adds only the selector: `HasherTag` carries `H` as a field, so it threads
by instance resolution exactly like `[Preset]`. The fast configuration provides
`Sha256` (the FFI hasher, opaque); the pure configuration provides `Sha256Spec`
(pure-Lean, kernel-reducible). Symbolic transition proofs also use `Sha256`, since
equality of two roots follows from the same hash over the same buffers with no
concrete bytes needed; proofs that must reduce a root to concrete bytes in the
kernel use `Sha256Spec`.

The second is the cache flavour. The flavour constructors are `CachedBox H` (cached)
and `UncachedBox H` (uncached), generic over the hasher tag, both producing
`Box H BeaconState`. SizzLean's `FastBox` and `PureBox` are the `Sha256`-pinned
aliases (`FastBox = CachedBox Sha256`), so the fast configuration is `FastBox` and the
pure configuration, whose hasher is `Sha256Spec`, is `UncachedBox Sha256Spec`. They
differ in flavour, not in type. The flavour is chosen once, at the anchor where the
state is first built: cached for runner speed, uncached so the getter-setter laws hold
by `rfl` with no cache-coherence obligation in the proofs.

So the type-level fast-versus-pure split is the monad alone. The hasher is an
instance and the flavour is a constructor choice, both orthogonal to the monad and
both invisible.

### 8.1 The access surface

The access primitives are SizzLean's generic macros, used directly.

| Primitive | `pyspec` equivalent | What it does |
|---|---|---|
| `sszGet state field` | `state.field` | reads `field` from the boxed `state` (`sszGet state message.slot` for a nested field, `sszGet state validators[i]` for an index) |
| `sszUpdate state with field := value` | `state.field = value` | writes `field`, returning a new box; carries the size-proof discharge and cache maintenance |
| `sszModify state field[i]! := g` / `… as x => body` | `state.field[i] = g(state.field[i])` | read-modify-write of one path, named once; `:= g` applies a function, `as x => body` binds the current value (`fun`-free, for `{ x with … }`); sugar over `sszUpdate … := … (sszGet …)` |
| `modifyState fun state => …` | several `state.field = …` lines | updates several fields of the threaded state at once |
| `getStateRoot` | `hash_tree_root(state)` | the Merkle root of the threaded state, keeping the cache-warmed box (`stateRoot` returns the root with the box for a non-monadic context, `stateRoot!` discards it, terminal-only) |
| `sszGetIdx (sszGet state F) i` / `xs[i]!` | `xs[i]` | element read; a load-bearing (data-derived) index uses `sszGetIdx`, surfacing `outOfBounds idx bound`, never a crash; a statically-bounded or `assert`-guarded index uses the total `xs[i]!` |

```lean
def incrementSlot : StateTransition Unit := do
  modifyState fun state => sszUpdate state with slot := sszGet state slot + 1

def checkSlot (expected : Slot) : StateTransition Unit := do
  let state ← get
  assert (sszGet state slot == expected)
```

Indexed access carries a deliberate split. A field projection stays pure. A load-bearing
index, one a data field supplies with no structural bound, reads through `sszGetIdx` (or
`bitlistGetIdx` for a `Bitlist`) and returns through the error channel, surfacing
`outOfBounds idx bound` rather than a panic, with a single `liftErr` adapter joining the two
(its `[ErrorConv IndexError E]` instance mapping the miss to the section's reject), so a bad
index becomes a rejected transition rather than an aborted process. An index a spec
validation already checks reads through `assertH (i < size)`: the assert returns the witness
and the read is the proof-carrying, reject-free `xs[i]'h.down`, the bad index having rejected
at the `assertH`. Where the bound is statically known (a `Fin n` into a length-`n` vector, a
loop over `xs.size`, a `% LEN` modulo through `vmodGet`) the read is a proof-carrying lookup
or the total `xs[i]!`, and proofs see a clean in-range lookup rather than an `Inhabited`
default. A pure query whose data-derived index comes from untrusted input returns `Except
IndexError` and reads through the same `sszGetIdx` (`get_base_reward`, `get_attesting_indices`,
the reward-delta helpers); one whose index is valid by construction keeps the total `xs[i]!`,
resting on the query's length invariant, the provability residual recorded in `FUTURE_WORK.md`.

The container front-end never boxes a value on its own. The `State` abbrev here
and the `Store`'s boxed fields are the only places a box is named, and `sszGet` /
`sszUpdate` operate only on a box, so a raw value can never be read by mistake.

---

## 9. The finite-map and fork-choice store

The fork choice is a parallel state machine over a `Store`, and the store holds
finite maps from roots to blocks, states, and votes. The framework abstracts the
map backing so the store's laws are provable on a deterministic backing while the
runner uses a fast one.

`MapKind` is a higher-kinded kind: the type a `map` variable ranges over, with each
inhabitant standing for a concrete map type constructor. `FcMap` is the operation
contract.

```lean
class FcMap (map : MapKind) where
  insert   : map K V → K → V → map K V
  lookup   : map K V → K → Option V        -- partial; a miss is missingKey
  contains : map K V → K → Bool
  fold     : (β → K → V → β) → β → map K V → β
  keys     : map K V → List K
```

`lookup` is partial; a miss is the `missingKey` reject of the error model.
`fold` and `keys` back the all-keys walks the fork choice needs, `getHead` and
the filtered-block-tree among them. Key constraints differ by backing: `hashMap`
needs `BEq` and `Hashable`, `treeMap` needs `Ord`. The `Ord` requirement is what
gives the proof-side `treeMap` a deterministic key order, which a proof that
quantifies over all store keys depends on.

Two instances ship: `treeMap` (ordered, proof-friendly) and `hashMap` (fast). The
higher-kinded `MapKind` framing is what lets a single `map` variable abstract over
both without the store committing to either.

### 9.1 The `Store`

The `Store` is a record of `FcMap`-backed maps, parameterized by the map backing.

```lean
forkstruct Store (map : MapKind) where
  blocks       : map Root (Box HasherTag.H BeaconBlock)
  blockStates  : map Root (Box HasherTag.H BeaconState)
  checkpoints  : map Checkpoint Root
  latestMessages : map ValidatorIndex LatestMessage
  justifiedCheckpoint : Checkpoint
  finalizedCheckpoint : Checkpoint
  -- ... per-fork fields are spec content
```

The `[FcMap map]` requirement sits on the operating defs, not on the struct; the
struct needs only the kind. So `Store hashMap` and `Store treeMap` are distinct
types that coexist with no ambient current map, which is why a fork-choice section
takes `map` as an explicit type variable.

The container-valued fields are boxed: `map Root (Box HasherTag.H BeaconState)`,
`map Root (Box HasherTag.H BeaconBlock)`. Boxing them means stored states arrive
warm as pre-states for child transitions, and test vectors deserialize straight
into boxes. The small fields, the checkpoints, the `LatestMessage`, the bit arrays,
stay raw. The hasher comes from `[HasherTag]`, so `Store` is parameterized by `map`
alone; the hasher is not a `Store` parameter.

`Store` is declared through `forkstruct`, not `forkcontainer`. It is a plain
non-SSZ structure: it gets ordinary `deriving` and no `SSZRepr` or
hash-tree-root, and it is per-fork and inheritable. `forkstruct` shares
`forkcontainer`'s capture base, so `Store` participates in fork inheritance and
late-binding; it just skips the SSZ generation. A plain Lean `structure` would not
be captured, so it could neither be inherited nor have its references late-bind.
Gloas redeclares `Store` in full with the ePBS payload-tracking fields (an
unchanged `Store` would simply be `inherit`ed); either way the boxed-state field
types late-bind in the Gloas namespace, so `blockStates` picks up Gloas's
`BeaconState`.

---

## 10. The arithmetic layer

Arithmetic stays in `UInt64`, matching SSZ `uint64` semantics: `Gwei = UInt64`,
fast and native. The `pyspec`'s operation order is transcribed faithfully. The
spec keeps intermediates in range, it divides before multiplying and floors
subtraction with `min` rather than underflow-wrapping, so the `UInt64` computation
neither overflows nor errors and equals the `pyspec`'s unbounded result.

Operation order is never reordered for convenience. Under truncating division
`(a * b) / c` and `(a / c) * b` differ, so faithful transcription is the rule, not
a cheaper reorder. The spec's explicit floors, `decreaseBalance`'s `min` for
instance, are reproduced as spec logic, with no reliance on wraparound either way.

`Nat` is the fallback only where a computation's faithful order genuinely needs an
intermediate above `2^64` (to be verified against the `pyspec`, likely few or none)
or where `Nat` is much simpler. There the result narrows back with an exact
`UInt64.ofNat`, never a reject. There is no `Nat` tier in the state itself; `Nat`
appears only as a transient intermediate.

The framework provides `umax`, `umin`, and `isqrt` (the integer square root the
committee math needs), and a type-directed `uintToBytes` whose width follows from
the value's type. The width-from-type discipline removes a whole bug class, the
4-versus-8-byte serialization mistake, by never letting the author pick the width
by hand.

For proofs, the framework provides a library of `UInt64`-to-`Nat` correspondence
lemmas, `(a + b).toNat = a.toNat + b.toNat` under a no-overflow bound and the like.
A proof lifts `UInt64` arithmetic into `Nat` for clean reasoning about sums and
bounds, then lifts the result back, discharging the no-overflow side conditions
from the spec's invariants. The runtime body stays fast in `UInt64` while proofs
get `Nat`'s ease.

---

## 11. The crypto layer

The domain line splits the crypto into two parts. The framework owns the
domain-agnostic mechanics; the spec owns the consensus-aware part.

Framework-owned mechanics come in two kinds. The **hashing-based** primitives are
the signing-root combinators, `computeForkDataRoot`, `computeDomain`, and
`computeSigningRoot`, which hash over small byte containers and take a fork-version
value without reading state, plus `isValidMerkleBranch`, the Merkle-proof
verification `processDeposit` runs against `eth1Data.depositRoot`. Both are backed
by SizzLean's hashing by default, and the framework is free to swap another
implementation if it fits better. The **signature- and commitment-based**
primitives are the BLS verify and aggregate (including the `fastAggregateVerify`
that `processSyncAggregate` uses) and the KZG primitives. These sit behind the
`[CryptoBackend]` seam.

The seam's currency is the raw `ByteArray`, the crypto FFI's wire format. The spec's
pubkeys, signatures, and roots are SSZ byte vectors (`BLSPubkey = Vector UInt8 48`,
`BLSSignature = Vector UInt8 96`, `Root = Vector UInt8 32`), so the spec calls the seam
through vector-typed wrappers that do the conversion at the boundary: `blsVerify`,
`blsFastAggregateVerify`, `blsEthFastAggregateVerify`, and `blsAggregatePubkeys` (in the
crypto layer beside the seam), and `blsVerifySigned`, which folds in `computeSigningRoot`
(in the signing-root layer beside the helper it composes). A spec gate then names the
pubkey, the object, the domain, and the signature. The single-value conversion itself is a
SizzLean coercion (`CoeOut (Vector UInt8 n) ByteArray`), so a byte vector flows into a
`ByteArray` position with nothing written at the call site; an array of them keeps an
explicit `.map`, since the coercion does not lift through a container.

The spec owns the consensus-aware part: `getDomain` (it reads `state.fork` and the
genesis validators root, then selects the `DOMAIN_*` constant per operation), the
`DOMAIN_*` constants, and the fixed-versus-state fork-version choice per signature
type (deposits use `GENESIS_FORK_VERSION`, most others the state's). The boundary
turns on a gates-versus-data distinction: `verify` is a gate the spec asserts on,
and the signing root is data fed forward into that gate.

### 11.1 The backend seam

The crypto primitives are instance-implicit (`[CryptoBackend]`), even though one
real algorithm is used, because the seam buys two things.

**Caching.** The pyspec suite calls BLS `verify` repeatedly on recurring
inputs: shared validator sets, domains, and fixtures recur across the sweep, and the
runner holds one long-lived server per worker so the memo stays warm. The runner
injects a backend that memoizes `verify` over the real FFI, keyed on the full
`(pubkey, message, signature)` wire bytes, a small fixed-size key whose hash costs far
less than the pairing it skips. The aggregate verifies and the KZG batch delegate
straight to the FFI. Their key would be a whole pubkey set or multi-kilobyte cell
arrays, and the exact input rarely recurs, so a memo there would mostly pay hashing
cost on misses. The memo lives in an `IO.Ref` table inside the runner's backend
instance, out of the spec body and the pure configuration, so it forecloses no proofs.
Caching is on by default. The `ETHCL_DISABLE_CRYPTO_CACHE` environment variable,
surfaced as the pytest `--no-crypto-cache` flag, swaps in the plain FFI backend
instead, for cache-on versus cache-off comparison. The `bls_setting: 2` verify-off
backend is selected independently, per case.

**Proofs.** The pure configuration injects a symbolic backend where `verify` is an
uninterpreted (or assumed-true) `Bool`. A transition theorem then reasons "if the
asserts pass then …" without executing the FFI, and it carries no compiler axioms
for crypto. The spec body calls the backend through the instance, never the FFI
directly, so swapping caching-FFI (runner) for symbolic (proofs) is the same
instance injection as `[Preset]` or `[HasherTag]`.

A third backend mode honors each vector's `bls_setting`, read from `meta.yaml` by
the Python layer. `bls_setting: 2` injects a verify-off backend where `verify ≡
true`, so a case the upstream generator made invalid only by a dummy signature is
not falsely rejected. That keeps the reject-faithfulness audit honest.

KZG is part of the same backend. The primitive is required by Fulu's PeerDAS,
inherited by Gloas, so it lands in the first fork. The standalone `kzg` test format
is out of scope; the primitive is exercised only through in-scope spec paths.

```lean
class CryptoBackend where
  verify              : Pubkey → ByteArray → Signature → Bool
  fastAggregateVerify : List Pubkey → ByteArray → Signature → Bool
  kzgVerifyCellProofBatch : Array KZGCommitment → Array CellIndex → Array Cell → Array KZGProof → Bool

-- a step calls the backend through the vector-typed wrapper, never the FFI directly:
def verifyBlockSignature (block : SignedBeaconBlock) : StateTransition Unit := do
  let state ← get
  let domain ← getDomain Const.domainBeaconProposer none           -- spec-owned
  let pubkey ← proposerPubkey state block.message.proposerIndex
  assert (blsVerifySigned pubkey block.message domain block.signature)  -- gate
  -- blsVerifySigned = blsVerify pubkey (computeSigningRoot block.message domain) block.signature
```

---

## 12. The control-flow combinators

Translating the `pyspec`'s imperative loops, the framework prefers idiomatic
Lean 4: `forM` / `mapM` / `foldlM` for effectful iteration, `foldl` and the `List`
combinators for accumulation, tail recursion where it reads cleanly. This serves
the readability goal and usually hands termination to Lean for free; a fold or
`forM` over a finite list is structural recursion with no obligation. Three loop
shapes result, and only the last needs machinery.

| Shape | Example | Termination | Machinery |
|---|---|---|---|
| Structural fold / `forM` / `mapM` | the shuffle (`foldl` over a fixed round count), epoch processing (`forM` over validators) | structural | none |
| Clean-measure well-founded | `processSlots` (`while state.slot < target`) | `termination_by target - state.slot` | none |
| Hard-measure | the fork-choice walks (`getHead`, filtered-block-tree, weight recursion) | runtime-valued bound | `fuelLoop` |

For the hard-measure case, where the bound is a runtime value (store size) and a
decreasing measure is less obvious up front, the framework provides a `Step` done/next
type and two structural-recursion-on-`Nat` primitives over it, both total and
kernel-reducible: `fuelLoop` (monadic, for a walk that reads the store through the
effect monad) and `fuelIterate` (pure, for a walk that is a plain function of the store).
The author writes the step body returning `.done` / `.next` and passes the bound (a store
or block count, a safe over-estimate); no `Nat` counter and no exhaustion branch in the
body. `fuelIterate` returns the accumulator itself when the fuel runs out, matching a
hand-rolled `| 0, a => a` walk, so the bound must exceed the walk length (exhaustion is
then unreachable and the result is always real).

```lean
def getAncestor (store : Store map) (root : Root) (slot : Slot) : Root :=
  fuelIterate ((FcMap.keys store.blocks).length + 1) root fun r =>
    match FcMap.lookup store.blocks r with
    | some block => if block.slot > slot then .next block.parentRoot else .done r
    | none       => .done r
```

These suit the *linear* fork-choice walks (a single `.next` continuation): `getAncestor`
and the `getHead` descent. A *tree* walk like `filterBlockTree`, which recurses over every
child inside a fold, is genuine tree recursion that a linear combinator cannot express, so
it keeps its own fuel-bounded `where` helper. The exhaustion result is a real value, never
`panic!`, which keeps the proof path intact; the "fuel never exhausted on a well-formed
store" fact becomes a separate, deferrable lemma rather than a gate on the definition.

The per-loop decision rule is explicit, and the specs document applies it case by
case. Prefer to avoid `fuelLoop`. When a clean measure exists, well-founded
recursion via `termination_by` / `decreasing_by` is better: no artificial bound,
no unreachable branch, the function is honestly total. The `getHead` walk, for
instance, has a clean measure when child slots strictly increase, so
`maxSlot - currentSlot` strictly decreases. The tradeoff is that `decreasing_by`
forces the invariant proof at definition time, which `fuelLoop` defers. Use
well-founded recursion when the measure is clean and the invariant proof is cheap;
use `fuelLoop` when the invariant proof would otherwise block the definition from
existing before proofs are in scope.

---

## 13. The conformance framework

`PySpecTests` is the conformance layer. It runs the upstream vectors against a
fork by driving the fork's interface, and it is written once and fork-agnostic. It
owns everything mechanical: decode, format-to-entry-point dispatch, control flow,
comparison, reject-reason recording, classify mode, reporting. The fork supplies
only its interface implementation, no handler table and no per-format wiring. A
fork that satisfies the interface is testable; one that does not fails to compile.
The decode and compare are bespoke, since they need the fork's `SSZRepr` and
containers, so no off-the-shelf framework replaces the core.

`PySpecTests` splits along the fork-interface typeclass, which is what lets it live in
the framework package without depending on any spec. The generic driver is here, in
the framework: it decodes through `[SSZRepr]`, dispatches each format to an interface
method, compares by root, and classifies, all written against the interface, so it
names no concrete fork. The runner exe is in the specs package: it instantiates this
generic driver at `Fulu` or `Gloas` and runs the long-lived server the Python harness
talks to. The runner depends on the specs because it sits with them, so the dependency
flow stays acyclic (the package structure is in the module-layout section of
`SPECS_ARCHITECTURE.md`).

### 13.1 The Python input side

The input side is Python's. It acquires the `consensus-spec-tests` release for the
fork's `pyspecPinnedVersion`, walks the case-tree layout, and parses each case's
metadata. The path encodes the preset and fork, so the case data does not have to.

```
tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>/
```

Each case carries a `meta.yaml`. Three fields drive the Lean side:

| `meta.yaml` field | Consumed by | Effect |
|---|---|---|
| `bls_setting` | the crypto layer | selects the backend mode (`2` ⇒ verify-off) |
| `blocks_count` | the fold drivers | bounds the block fold |
| `fork_epoch` (the `transition` format) | the lifecycle driver | the per-case boundary epoch, injected as a config override |

Acquisition and metadata are Python; SSZ-decode, run, compare, and classify are
Lean.

### 13.2 The driver shapes

Three driver shapes cover every in-scope format.

| Driver | Formats | What it does |
|---|---|---|
| Fold-compare-root | `sanity/blocks`, `sanity/slots`, `random`, `finality`, `transition` | decode the pre-state plus a sequence, fold the transition, compare the post-state root |
| Step/check interpreter | `fork_choice` | replay `on_*` handlers with interleaved store checks |
| Single-step runner | `epoch_processing/*`, `operations/*`, `rewards/*`, `genesis`, `fork` | run one entry point, compare or expect reject |

`random`, `finality`, and `sanity/blocks` share the one fold driver; they differ
only in which vectors upstream emits. The `transition` format also applies
`upgradeToGloas` mid-fold at the per-case fork-boundary slot (the boundary epoch is
the vector's `fork_epoch`, injected as that case's config override), exercising the
lifecycle upgrade in-line. The single-step runner covers the reward and penalty
delta functions in isolation for `rewards/*`, the genesis builder for `genesis`,
and the `upgradeToGloas` entry for `fork`. `ssz_static`, `bls`, and `kzg` are out
of scope, since they test the SSZ and crypto primitives, a framework-library
concern. Spec-faithful-mode annotations mark unreachable branches, classified as
`todo` rather than failures.

### 13.3 The per-worker Lean server

The vectors are thousands of independent cases, embarrassingly parallel. The runner
is `pytest` with `pytest-xdist` for multi-core distribution and reporting. No Lean
test framework parallelizes well across cores, so the mature multi-core runner
lives on the Python side.

The Lean pyspec executable runs as a long-lived **server**: a loop that reads
a vector request, decodes and runs and compares against the fork interface, and
emits a structured result, keeping its crypto cache warm across requests. Each
`xdist` worker holds one such server through a `session`-scoped fixture (session
scope is per-worker in `xdist`), and every per-vector test sends its vector to that
worker's server and asserts the result. There is no per-test Lean startup, the
cache stays warm per worker, and `pytest` still gives per-vector reporting:
pass/fail, per-format breakdown, and failing-vector detail with the reject reason
and classify bucket, plus dynamic load-balancing across cores.

The crypto cache is per worker, one per core, warm over that worker's stream of
vectors. A single globally shared cache would need one Lean process with
thread-safe `Task` parallelism, an upgrade taken only if profiling shows repeats
span workers. The plumbing to build is small: the Lean server request/result loop
and the pytest fixture managing the subprocess.

The report distinguishes the classify buckets from the error model: a passing
case, an expected rejection (`assert` against an invalid vector), an out-of-scope
deferral (`todo`), and a likely bug (`outOfBounds` / `missingKey` on well-formed
input). A `todo` that a vector actually reaches fails loudly rather than passing
silently, which is the deferral safety net at work.

---

## 14. Self-testing

The framework tests only what it owns and relies on its dependencies' suites for
the rest, with no duplication.

SizzLean already tests the SSZ and cache machinery in its own test suite: cache
coherence (a `FastBox`'s cached root equals the `PureBox` uncached root, so caching
never changes the hash-tree-root), generic `SSZRepr` round-trips
(`deserialize ∘ serialize = id`, and the root against a reference), and the
preset-generic `SSZRepr` reduction (that the root and `sszUpdate` reduce at a
concrete preset). The framework relies on those rather than re-testing them.

The framework's own self-tests cover what it adds:

- **Map-backing equivalence.** `hashMap` and `treeMap` give the same `FcMap`
  results, so the proof-side backing matches the runner's.
- **Crypto-cache transparency.** The caching `[CryptoBackend]` returns the real
  backend's answer, so memoization never changes a result.
- **Inheritance-macro dispatch.** The capture/replay of the capturing declaration
  forms resolves to the child's overrides, so an inherited caller late-binds.
- **The arithmetic correspondence lemmas.** The `UInt64`-to-`Nat` lemmas hold
  (basic `UInt64` lemmas are stdlib, so they are not re-proved).

These are Lean-internal unit tests, written as `#guard` / `native_decide` /
`example`, distinct from the `pytest` vector harness. The project has two test
surfaces: Lean unit tests for the machinery, `pytest-xdist` for conformance.
Several of these self-tests are exactly the theorems the proof-support layer would
later prove, so they graduate from tested to proven once proof work starts.

CI runs two jobs. `lake build` over the framework and specs compiles everything
and runs the Lean unit self-tests (the `#guard` and `native_decide` cases are
checked at build), the existing `lean-action` workflow. The pyspec suite
(`pytest-xdist`) is a separate job; since the mainnet vectors are slow, it can run
sharded or on demand rather than on every push.

The spec-revision pin lives in the spec, per fork, as `pyspecPinnedVersion`, not in
the framework. The framework separately pins its toolchain (`lean-toolchain`) and
its dependency revs (SizzLean, the crypto FFI). The `consensus-spec-tests` release
tag the suite runs against is part of the per-fork pin.

---

## 15. Proof-support

Proofs are out of scope for the first framework milestone. The framework's
obligation is to not foreclose them, so every definition stays kernel-reducible and
every external call stays behind a seam a proof can leave abstract.

Two techniques the design keeps open. First, every spec `assert` is a gate, and a
proof case-splits on its `Bool` condition: the reject branch is killed by the
theorem's success hypothesis, and the accept branch hands the condition back as a
free hypothesis. This works uniformly whether the condition is a plain field
comparison (`block.slot == state.slot`), a crypto `verify`, an SSZ-root equality
(`block.stateRoot` against the root from `getStateRoot`), or a Merkle-branch check. The opaque cases,
`verify` and the hash, are split on, never reduced, so no `native_decide` and no
compiler axiom enters. Second, the crypto backend is left abstract in proofs
(quantified `[CryptoBackend]`, not a fixed instance), so `verify` is an abstract
`Bool` the split handles, and a property proved over an abstract backend holds for
the real FFI for free. The same opacity covers the state root (`getStateRoot` /
`stateRoot!`): the FFI hasher stays
opaque, the root-equality assert is split, and for invariant proofs the equation is
a gate rather than a fact the proof consumes. Goals that genuinely need a hash's
concrete bytes fall back to `native_decide` or `Sha256Spec`, the standard four-case
hasher discipline, while the gate-split path stays axiom-free.

Seven anti-patterns the framework avoids in every definition, in order of severity:

1. **`IO` inside `State` or `Box`.** Forecloses the pure configuration entirely; a
   `StateT ∘ Except` cannot be formed if the state holds an `IO.Ref`.
2. **`partial def` for any spec function.** The kernel assigns it an opaque
   constant, so `simp [f]` does nothing. Use fuel-bounded recursion instead.
3. **`@[irreducible]` on the uncached `Box` instance.** The pure config's box is
   `UncachedBox Sha256Spec`, where `sszGet` is a field projection and `sszUpdate` a
   record update, both reduce definitionally and the getter-setter laws hold by
   `rfl`. If the dispatching instance is irreducible, the kernel stops at the dispatch
   and never reaches the reducible projection underneath. Keep the uncached box
   instance `@[reducible]` or `@[inline]`; the cached (`FastBox`) instance can be
   opaque, since proofs never run on the fast path.
4. **`@[extern] opaque` deep in spec logic.** Fine at the FFI edges, where the
   common proof path is opacity plus gate-split (axiom-free) and the named
   equivalence axioms are only the concrete-bytes fallback. A spec function that
   itself calls some other extern-opaque primitive would force compiler axioms into
   every proof above it.
5. **A load-bearing `arr[i]!` in a monadic step.** A data-derived index (a validator /
   committee / queue index an operation supplies) with no structural bound reads through
   `sszGetIdx`, surfacing `outOfBounds idx bound` (§7), so a bad index lands in the
   `likelyBug` bucket and a proof need not unfold through the `Inhabited` default. Total
   `arr[i]!` is reserved for a statically-bounded index (a `Fin n` into a length-`n`
   vector, a loop over `xs.size`, a `% LEN` modulo, a constant), an index already
   `assert`-guarded, or a pure query / transform that has no reject channel.
6. **`native_decide` in `@[simp]` lemmas.** Pollutes every downstream theorem's
   axiom set with the compiler axiom. Reserve `native_decide` for proofs about
   specific concrete outputs; prove structural `simp` lemmas by `decide` or `rfl`.
7. **`hashMap`-only in the pure path.** `Std.HashMap` has no guaranteed key order,
   and a proof that quantifies over all store keys needs `treeMap`. The `FcMap`
   abstraction supports both, and the pure path uses `treeMap`.

Two further facts the design records for the eventual proof work. The
`UInt64`-to-`Nat` correspondence lemmas let arithmetic proofs reason in `Nat` under
no-overflow bounds while the runtime stays `UInt64`. And inheritance is by symbol,
so a property about a caller is proved per fork; `Fulu.processOperations` and
`Gloas.processOperations` are distinct symbols, and proof reuse across forks is a
known cost, accepted while proofs are deferred. The theorems module is the
containment boundary if proofs ever need mathlib, keeping it off the framework,
spec, runner, and `PySpecTests` paths, the same discipline the repository applies
to its Poseidon proofs.
