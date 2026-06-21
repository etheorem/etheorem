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
* `captureExt` records every `forkdef` / `forkcontainer` / `forkstruct` body,
  keyed by `(forkNamespace, shortName)`, as the raw `Syntax` to replay.

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
  deriving Inhabited, DecidableEq, Repr

/-- One captured declaration's replay payload.

Stored verbatim from the author's source. `sig` and `val` are the two pieces a
`forkdef` needs (`optDeclSig` and `declVal`); a container or struct uses only
`val`, which holds its field block, and leaves `sig` as `Syntax.missing`. -/
structure CapturedDecl where
  /-- The fork namespace the declaration was written in (e.g. `EthCLSpecs.Fulu`).
  Named `forkNs`, not `fork`, because the `fork` keyword the forms declare would
  shadow a field named `fork` at every construction site. -/
  forkNs : Name
  /-- The declaration's short name (e.g. `processBlock`). -/
  name : Name
  /-- Which form captured it. -/
  kind : CaptureKind
  /-- A `forkdef`'s `optDeclSig`; `Syntax.missing` for a container / struct. -/
  sig  : Syntax
  /-- A `forkdef`'s `declVal`, or a container / struct's field block. -/
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

end EthCLLib.Internal
