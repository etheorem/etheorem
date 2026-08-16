import Lean

/-!
# `EthCLLib.Internal.Capture`: the fork-inheritance capture base

This module is the single mechanism behind *the inheritance mechanism*
(`SPEC_AUTHORING_MODEL.md` §8, `FRAMEWORK_ARCHITECTURE.md` §3): a later fork
is a diff over its parent, and an unchanged parent declaration is inherited by
capturing the author's **raw body syntax** and re-elaborating it inside the
child namespace. There, the body's unqualified sibling calls resolve to the
child's overrides by ordinary name resolution. Late binding falls out for free,
the open-recursion (fragile-base-class) trap a symbol-level copy or alias would
fall into.

Two environment extensions carry the data:

* `lineageExt` records the `fork … from …` edges: each fork's full namespace
  paired with its parent's full namespace (or `Name.anonymous` for a root).
* `captureExt` records every capturing form's body, keyed by
  `(forkNamespace, residualName)`, as the raw `Syntax` to replay.

The key's two halves come from splitting the elaboration-time namespace at the
nearest registered fork (`splitAtFork`). A declaration written inside
`namespace EthCLSpecs.Fulu` … `namespace Const` keys as
`(EthCLSpecs.Fulu, Const.slotsPerEpoch)`, so `inherit Const.slotsPerEpoch` in
the child finds it. Keying on the raw current namespace instead would file the
constant under `EthCLSpecs.Fulu.Const`, which is no fork at all, and no lineage
walk would ever reach it.

Both are `SimplePersistentEnvExtension`s, so the captures survive into the
`.olean` and a child fork in a *separate module* can inherit a parent declared
in an *imported* module. `Syntax` is a closure-free core inductive, so it
serialises through the olean object writer with no extra instances.

The three capturing forms (`forkdef`, `forkcontainer`, `forkstruct`) are the
*producers* into `captureExt`; `inherit` is the single *consumer*. This file
owns only the storage and the resolver; the forms themselves live in
`EthCLLib.Spec.Forms`, which calls `recordCapture` / `recordLineage` and reads
back through `resolveInherited`.

## Lean idioms annotated on first appearance

* `registerSimplePersistentEnvExtension`: builds an environment extension whose
  per-declaration entries (`α`) are folded into an in-memory state (`σ`) and
  written to the `.olean`. `addEntryFn` folds one new local entry;
  `addImportedFn` rebuilds the state from every imported module's entry arrays.
* `initialize x ← act`: runs `act : IO _` once at module load to build a
  top-level constant (here, the extension handle). Extensions must be created
  this way so their identity is stable across the whole compilation.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.Internal

/-- Which capturing form produced an entry. `inherit` dispatches on this to
re-emit the right kind of declaration in the child namespace. -/
inductive CaptureKind where
  /-- A `forkdef`: a step or helper. The payload is the signature plus the
  declaration value (`:= body`, equations, or a `where` block). -/
  | def_
  /-- A `forkcontainer`: an SSZ container. The payload is the field block; the
  form regenerates the `structure` and its `SSZRepr` derive on replay. -/
  | container
  /-- A `forkstruct`: a non-SSZ structure (`Store`, `FcNode`, …). The payload
  is the field block; the form regenerates the `structure` with ordinary
  `deriving` on replay. -/
  | struct
  /-- A `forkabbrev`: a type alias or a constant. Replay re-emits an `abbrev`,
  never a `def`; the `@[reducible]` attribute is what SSZRepr synthesis and the
  symbolic-cap derive see through, so demoting it would break both. -/
  | abbrev_
  /-- A `forkinstance`: a named typeclass instance. Replay re-emits an
  `instance`, which a `def`-shaped capture could not do (the capturing forms
  drop modifiers, so an `@[instance]` attribute would not survive). -/
  | instance_
  /-- A tier declaration: a `forkpreset` / `forkconfig` class, or a
  `forkpresetvalues` / `forkconfigvalues` value set. The payload is a block of
  named entries, and the capture holds only the fork's own *diff*.

  These are the one kind `inherit` never consumes. A class and a value set are
  each a single declaration, so per-name inheritance cannot compose one; the
  child's own tier form merges the lineage's blocks by entry name instead
  (`mergedTier`), which is the class-shaped analogue of per-name `inherit`. -/
  | tier
  deriving Inhabited, DecidableEq, Repr

/-- One captured declaration's replay payload.

Stored verbatim from the author's source. Which of the three syntax slots carry
content depends on `kind`:

| kind         | `binders`              | `sig`               | `val`         |
| ------------ | ---------------------- | ------------------- | ------------- |
| `def_`       | ∅                      | `optDeclSig`        | `declVal`     |
| `abbrev_`    | ∅                      | `optDeclSig`        | `declVal`     |
| `instance_`  | ∅ (they ride in `sig`) | `declSig`           | `declVal`     |
| `container`  | ∅                      | ∅                   | `structFields`|
| `struct`     | the author's binders   | ∅                   | `structFields`|
| `tier`       | ∅                      | ∅                   | entry block   |

Only `struct` needs the `binders` slot: Lean's `structure` takes its parameters
beside the field block, while `declSig` (what an `instance` and a typed `def`
carry) already holds the binders ahead of the `: type`. Both unused slots
default, so a producer writes only what its kind fills. -/
structure CapturedDecl where
  /-- The fork namespace the declaration was written in (e.g. `EthCLSpecs.Fulu`).
  Named `forkNs`, not `fork`, because the `fork` keyword the forms declare would
  shadow a field named `fork` at every construction site. -/
  forkNs : Name
  /-- The declaration's name *relative to the fork namespace*: `processBlock` for
  a step written directly in the fork, `Const.slotsPerEpoch` for one written
  inside a nested `namespace Const`. This is the name `inherit` spells. -/
  name : Name
  /-- Which form captured it. -/
  kind : CaptureKind
  /-- A null node of `bracketedBinder`s the author wrote beyond the implicit
  `[Preset]`. Defaults to the empty null node, so `.getArgs` is well defined
  even for the kinds that never fill it. -/
  binders : Syntax := mkNullNode
  /-- The declaration's signature, in whichever `declSig` flavour the kind uses. -/
  sig  : Syntax := .missing
  /-- A declaration value (`declVal`), or a structure's field block. -/
  val  : Syntax
  deriving Inhabited

/-- Lineage edges: `(forkFullName, parentFullName)`, parent `anonymous` for a
root fork. An `Array` (not a map) keeps the extension state trivial to merge
across imports; lineage chains are short, so the linear scan in `parentOf`
is free. -/
initialize lineageExt :
    SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- Every captured declaration body, across every fork. Scanned by
`lookupCapture`; the count is in the low thousands at most and the scan runs
only at macro-expansion time. -/
initialize captureExt :
    SimplePersistentEnvExtension CapturedDecl (Array CapturedDecl) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- Record a `fork … from …` edge. `parent` is `none` for a base fork. -/
def recordLineage (env : Environment) (fork : Name) (parent : Option Name) :
    Environment :=
  lineageExt.addEntry env (fork, parent.getD Name.anonymous)

/-- Record a captured declaration body. -/
def recordCapture (env : Environment) (cap : CapturedDecl) : Environment :=
  captureExt.addEntry env cap

/-- Is `ns` a registered fork, i.e. did some `fork …` command name it? Roots
count: their lineage entry pairs them with `Name.anonymous`. -/
def isFork (env : Environment) (ns : Name) : Bool :=
  (lineageExt.getState env).any fun (f, _) => f == ns

/-- Split an elaboration-time namespace into `(owningFork, residualPath)`,
nearest enclosing fork wins.

`EthCLSpecs.Fulu.Const` splits as `(EthCLSpecs.Fulu, Const)`; `EthCLSpecs.Fulu`
itself splits as `(EthCLSpecs.Fulu, .anonymous)`. A namespace with no registered
fork anywhere above it yields `none`, and the caller keys the capture on the raw
namespace instead, the behaviour every capture had before nesting was supported.

The recursion peels one component at a time and rebuilds the residual on the way
out, so the residual's component order matches the source. -/
partial def splitAtFork (env : Environment) (ns : Name) : Option (Name × Name) :=
  if isFork env ns then
    some (ns, Name.anonymous)
  else
    match ns with
    | .anonymous => none
    | .str p s   => (splitAtFork env p).map fun (f, r) => (f, r.str s)
    | .num p i   => (splitAtFork env p).map fun (f, r) => (f, r.num i)

/-- The capture key for a declaration named `declName` (the author's `declId`,
itself possibly dotted) written while the current namespace is `ns`. -/
def captureKey (env : Environment) (ns declName : Name) : Name × Name :=
  match splitAtFork env ns with
  | some (forkNs, residual) => (forkNs, residual ++ declName)
  | none                    => (ns, declName)

/-- The parent fork of `fork`, if `fork` has a recorded `from` edge with a
non-anonymous parent. -/
def parentOf (env : Environment) (fork : Name) : Option Name :=
  (lineageExt.getState env).findSome? fun (f, p) =>
    if f == fork && p != Name.anonymous then some p else none

/-- The capture of `name` declared *in fork `fork` itself*, if any. -/
def lookupCapture (env : Environment) (fork name : Name) : Option CapturedDecl :=
  (captureExt.getState env).find? fun cap => cap.forkNs == fork && cap.name == name

/-- Resolve an `inherit name` at `fork`: walk strictly upward through the
lineage and return the nearest ancestor's capture of `name`.

`inherit` is a pure consumer, it never re-captures, so the search starts at the
*parent* (the current fork did not declare `name`, that is why it is inherited)
and climbs. For a chain `X from Y from Z` where `Y` left `name` unchanged, the
walk passes `Y` (no capture) and lands on `Z`'s, exactly the version that is
current for `X`. -/
partial def resolveInherited (env : Environment) (fork name : Name) :
    Option CapturedDecl :=
  match parentOf env fork with
  | none        => none
  | some parent =>
    match lookupCapture env parent name with
    | some cap => some cap
    | none     => resolveInherited env parent name

/-! ## Tier merging

A `tier` capture holds one fork's diff of a `Preset` / `Config` class or of one
of their value sets. The declaration a fork actually emits is the whole lineage's
diffs merged, so the two functions below reconstruct it. `inherit` plays no part;
the child's own tier form calls `mergedTier` directly. -/

/-- The lineage from the root down to `fork`, root first. -/
partial def lineageChain (env : Environment) (fork : Name) : List Name :=
  match parentOf env fork with
  | none        => [fork]
  | some parent => lineageChain env parent ++ [fork]

/-- The name an entry in a tier block declares. Both entry shapes put it at index
1, behind the optional docstring, so one accessor serves fields and assignments
alike. -/
def tierEntryName (entry : Syntax) : Name := entry[1].getId

/-- Fold one fork's diff into the accumulated block: an entry that redeclares an
inherited name replaces it *in place*, so the ancestor's ordering survives and a
child override does not reshuffle the class; a new name is appended. -/
def mergeTierEntries (acc new : Array Syntax) : Array Syntax :=
  new.foldl (init := acc) fun acc entry =>
    match acc.findIdx? (tierEntryName · == tierEntryName entry) with
    | some i => acc.set! i entry
    | none   => acc.push entry

/-- The full entry block for tier `key` at `fork`: every ancestor's diff merged
root-first, then `fork`'s own. A fork that declares nothing under `key`
contributes nothing, so a tier can skip generations. -/
def mergedTier (env : Environment) (fork key : Name) : Array Syntax :=
  (lineageChain env fork).foldl (init := #[]) fun acc f =>
    match lookupCapture env f key with
    | some cap => mergeTierEntries acc cap.val.getArgs
    | none     => acc

end EthCLLib.Internal
