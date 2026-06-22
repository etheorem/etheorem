import Lean
import SizzLean.Cache.MerkleTree.Build
import SizzLean.Cache.MerkleTree.SetAt
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Cache.Box
import SizzLean.Cache.IndexError

/-!
# `SizzLean.Cache.Update`: `sszUpdate t with …` surface syntax

User-facing batched multi-field update syntax for SSZ cache values:

```lean
sszUpdate t with
  previousVersion := pv,
  currentVersion  := cv,
  epoch           := e
```

## Background: macros vs functions

Unlike a regular Lean `def`, `sszUpdate` is implemented as a
*term elaborator* (akin to a macro). Its body runs at compile
time and produces a `Syntax` tree for the *real* expression Lean
will then typecheck and compile. This lets the body inspect
`t`'s elaborated type, known statically, and decide which
piece of code to produce. The user sees one surface syntax;
under the hood, the cached and uncached flavours expand to
different code without any runtime dispatch.

The elaborator inspects `t`'s type at expansion time and emits
*specialised* code per cache flavour:

* `t : TreeBacked H T` (= `CachedSSZ H T`): emits a Merkle-aware
  update that lowers to a single `Node.setManyAt` call. Writes
  sharing a path prefix allocate one fresh `.pair` per *level of
  shared spine*, not one per write.
* `t : UncachedSSZ H T`: emits a plain struct rewrite:
  `{ view := { t.view with f := v, … } }`. No tree machinery, no
  Merkle vocabulary in the emission. The uncached path doesn't
  even reject basic-packed element indexing (a restriction that
  only matters when there's a Merkle leaf to re-encode).

Anything else is a type error at the macro call site. There is no
caching *typeclass* to be generic over: flavour-generic code takes a
concrete `SSZ.Box H T` and relies on this macro's two-arm dispatch
(see `Cache/Box.lean` for why a class can't drive `sszUpdate`).
Specialise the function to a concrete cache type at the call site
if you need `sszUpdate`-style ergonomics.

## What runs at macro-expansion time

For both flavours:
* **Path parsing.** Each clause's LHS becomes an `Array PathStep`
  with `field`/`index` segments.
* **View-update chain.** A `let`-chain that applies each clause's
  update to the previous view binding (so shared-prefix clauses
  compose correctly).

For the cached flavour, also:
* **Field-index lookup.** Each `f := v` clause's `f` is resolved
  against `T`'s structure-field list via
  `Lean.Meta.getStructureFields`. Wrong field names fail with a
  clear error at the macro call site.
* **Gindex bit computation.** Each field's gindex is converted to
  `List Bool` at expansion time, so the emitted code carries the
  bit list as a literal. No runtime `Nat.log2` / `Nat.testBit`
  calls, the spine-walk just reads the precomputed bits.
* **Field-type extraction.** Pins `SSZRepr` instance synthesis for
  the per-clause replacement sub-Merkle-tree.

## Emission shape (cached path)

For `sszUpdate t with f₁ := v₁, …, fₖ := vₖ` on `TreeBacked H T`:

```lean
let t₀ : TreeBacked H T := t
({ view := { t₀.view with f₁ := v₁, …, fₖ := vₖ }
   tree := t₀.tree.setManyAt
     [ ([bits₁], Node.ofShape H (SSZRepr.shape (T := F₁)) (toRepr v₁))
     , …
     , ([bitsₖ], Node.ofShape H (SSZRepr.shape (T := Fₖ)) (toRepr vₖ)) ]
 } : TreeBacked H T)
```

The bit lists are *literals* (`[false, true, false, false]`), so
the spine-walk and gindex bits fold at elaboration time.

## Emission shape (uncached path)

For `sszUpdate t with f₁ := v₁, …, fₖ := vₖ` on `UncachedSSZ H T`:

```lean
let t₀ : UncachedSSZ H T := t
({ view := { t₀.view with f₁ := v₁, …, fₖ := vₖ } } : UncachedSSZ H T)
```

That's it, no Merkle, no `Node.ofShape`, no `setManyAt`.

## Nested paths

Each clause's LHS is a sequence of idents separated by `.`:

```lean
sszUpdate header with
  message.slot          := newSlot,
  message.proposerIndex := newIdx,
  signature             := newSig
```

The view side uses a `let`-chain, one `with`-record update per
clause, applied in source order. This is correct under shared
prefixes too: `f.g := w` then `f.h := x` reads `v₁.f` (which has
`g := w`) when computing the second update, so both mutations
survive.

## Index syntax

Vector / list element updates: `sszUpdate t with vec[i] := v`. On
the cached path `walkPath` walks into the `Vector α n` / `SSZList
α cap` type, computes the per-element gindex base via `gindexBaseForCap`,
and emits `gindexBits (base + i)` as a *runtime* piece of the bits-list
expression. A concrete cap folds the base to a single literal at expansion
time (the fast path); a `[Preset]`-resolved symbolic cap leaves the base as
`2 ^ chunkDepth cap`, which reduces once the preset is pinned, so
per-element writes work on preset-generic containers too. The view side
calls `Vector.set!` / `SSZList.set!` regardless of cache flavour.

### Checked `[i]` vs infallible `[i]!`

An index segment comes in two forms. The checked `vec[i]` rejects an
out-of-range index: any clause that uses it makes the whole `sszUpdate`
return `Except IndexError _`, with the issue-time guard producing
`.error (indexError i bound)` in program order. The infallible `vec[i]!`
mirrors `Array.set!`: an out-of-range write is a silent no-op, the clause
contributes no error, and an `sszUpdate` whose index clauses are *all* `[i]!`
(or that has none) returns the bare cache value, no `Except` to thread. The
two forms emit the identical spine address and view rewrite; `[i]!` only drops
the issue-time guard and the `Except` wrapping. `sszGet` mirrors this: a
checked `[i]` read returns `Except`, an `[i]!` read returns the element's
`default` on a miss. Reach for `[i]!` in spec loops where the bound is a known
invariant; keep `[i]` where a miss must reject.

## Basic-packed element indices: supported, at owner-rebuild cost

`sszUpdate t with vec[i] := v` where `vec`'s element type is basic
and packs multiple-elements-per-chunk (e.g. `Vector UInt64 n`,
`SSZList Gwei cap`) works on every flavour. A packed element shares
a 32-byte chunk with its neighbours and has no Merkle sub-tree of
its own, so the cached path cannot key a `PendingWrite` at an element
gindex. Instead it points the write at the *owning* field's gindex
and rebuilds that whole field's subtree from the index-updated
`view` (the `projDrop` mechanism in `walkPath`). This is
byte-identical to the manual whole-field replacement
`sszUpdate t with vec := t.view.vec.set! i v`, the macro just writes
it for you. The uncached path handles it with the same plain
`{ view := { … with vec := vec.set! i v } }` rewrite it uses for
everything.

Cost (cached path only): rebuilding the owning field's subtree is
O(field-chunks) merkleization, not the O(log cap) of a single-leaf
update. Fine for occasional writes; for tight per-element loops
(reward/penalty sweeps over `balances`) a true single-chunk re-encode
path would still be needed. Composite-element and whole-field updates
keep their O(log N) behaviour.

## Decisions

* **`H` is inferred from `t`'s type, not passed at the call site.**
  `TreeBacked H T` / `UncachedSSZ H T` pin the hasher in the type
  at construction; the elaborator reads it back and splices it
  into the emitted `Node.ofShape` calls (cached path) or just
  drops it (uncached path). Mixing hashers within a single cached
  value is a type error.
* **`term_elab`, not `macro`.** The elaborator needs `t`'s static
  type to look up structure fields, extract the hasher, *and*
  decide between the two emission paths. That requires `elabTerm`
  / `inferType` on the base, which is a `TermElabM` capability.
* **Per-cache-type emission, not typeclass dispatch.** Each cache
  type gets its specialised optimal emission, and `SSZ.Box`'s closed
  two-constructor sum makes the cross-flavour case a compile-time
  two-arm match. There is deliberately no caching *typeclass*: a
  class abstracting the two flavours could carry read-side methods
  but couldn't drive `sszUpdate` without leaking a Merkle `Patch`
  field into its public API (see `Cache/Box.lean`).
-/

set_option autoImplicit false

namespace SizzLean.Cache

open SizzLean.Repr

open SizzLean.Hasher

open Lean Elab Term Meta

/-- A single path segment after the leading ident: `.field` (descend into a
structure field), `[i]` (descend into a vector / list element, *checked*), or
`[i]!` (the same element step, *infallible*). The leading ident itself plays
the role of the first `.field` segment.

`[i]` vs `[i]!` only differ on the out-of-range path. A clause with a checked
`[i]` makes the whole `sszUpdate` return `Except IndexError _`, rejecting an
out-of-range index in program order (`sszGet` likewise returns `Except`). The
bang form `[i]!` mirrors `Array.set!` / `Array.get!`: an out-of-range write is
a silent no-op and an out-of-range read yields the element type's `default`,
so the clause never contributes an error and an all-`[i]!` update returns the
bare cache value. Use `[i]` when the index is attacker-controlled and a miss
must reject; use `[i]!` inside spec loops where the bound is a known invariant
and threading `Except` through every write is just noise. -/
declare_syntax_cat sszUpdateSegment
syntax (name := sszUpdateSegmentField)     "." ident            : sszUpdateSegment
syntax (name := sszUpdateSegmentIndex)     "[" term "]"          : sszUpdateSegment
syntax (name := sszUpdateSegmentIndexBang) "[" term "]" noWs "!" : sszUpdateSegment

/-- A single clause: a path (head ident + zero or more segments) on
the LHS, value on the RHS. Examples:

```
epoch := 99                              -- flat field
message.slot := 99                       -- nested field
blockRoots[i] := r                       -- field + index
state.balances[i] := b                   -- nested + index
graffiti[i].byte := x                    -- index + field (rare)
```
-/
declare_syntax_cat sszUpdateClause
syntax (name := sszUpdateClauseDotted)
    ident sszUpdateSegment* " := " term : sszUpdateClause

/-- The `sszUpdate t with …` term-elaborated syntax. -/
syntax (name := sszUpdateStx) "sszUpdate " term:max " with "
    sepBy1(sszUpdateClause, ", ") : term

/-- The read-side companion of `sszUpdate`. `sszGet b path` expands
to `b.view.path` so user code never has to spell out the
internal `.view` projection. Path syntax mirrors `sszUpdate`
exactly:

```
sszGet b epoch                       -- flat field read
sszGet b message.slot                -- nested field
sszGet b validators[i]               -- vector / list index
sszGet b validators[i].effBalance    -- index + field
```

The expansion is purely syntactic: `sszGet b epoch` rewrites to
`b.view.epoch`, which Lean's kernel handles definitionally. So
`rfl` / `decide` / `simp` proofs about reads close exactly as if
the user had written `.view.epoch` by hand. -/
syntax (name := sszGetStx) "sszGet " term:max ident sszUpdateSegment* : term

/-- Append one path segment onto an accumulating term, for the
`sszGet` macro. Recursive on the segment array. -/
private partial def appendSszGetSegments
    (e : Lean.TSyntax `term)
    (segs : Array (Lean.TSyntax `sszUpdateSegment))
    (i : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
  if h : i < segs.size then
    let seg := segs[i]
    let e' ← match seg with
      | `(sszUpdateSegment| .$f:ident)  => `($e.$f)
      | `(sszUpdateSegment| [$j:term])  => `($e[$j])
      | `(sszUpdateSegment| [$j:term]!) => `($e[$j]!)
      | _ => Macro.throwError s!"sszGet: malformed path segment {seg}"
    appendSszGetSegments e' segs (i + 1)
  else
    return e

/-- True when a `sszGet`/`sszUpdate` path contains a *checked* index segment
`[i]`, the only forms that can reject, hence the only ones that make the
result `Except`. A bang `[i]!` segment is infallible and does not count. -/
private def segsHaveCheckedIndex (segs : Array (TSyntax `sszUpdateSegment)) : Bool :=
  segs.any (fun seg => seg.raw.getKind == ``sszUpdateSegmentIndex)

/-- `Except`-producing variant of `appendSszGetSegments`, used when the path
has a checked index. Walks the path from the owner term `cur`: a `.f` step
projects, a checked `[j]` step emits a bounds check that rejects with the
*real* index and bound (`IndexError.indexError j cur.size`) when `j` is out of
range and otherwise descends into `cur[j]!`, and a bang `[j]!` step descends
into `cur[j]!` with no check (it can't reject). The fully-walked value is
wrapped in `.ok`, so the path stays a clean `Except IndexError _` with a
precise reject at every checked index position. -/
private partial def appendSszGetExcept
    (cur : Lean.TSyntax `term)
    (segs : Array (Lean.TSyntax `sszUpdateSegment)) (i : Nat) :
    Lean.MacroM (Lean.TSyntax `term) := do
  if h : i < segs.size then
    let seg := segs[i]
    match seg with
    | `(sszUpdateSegment| .$f:ident) =>
        appendSszGetExcept (← `(($cur).$f)) segs (i + 1)
    | `(sszUpdateSegment| [$j:term]) =>
        let inner ← appendSszGetExcept (← `(($cur)[$j]!)) segs (i + 1)
        `(if $j < ($cur).size then $inner
          else _root_.Except.error
                 (_root_.SizzLean.Cache.IndexError.indexError $j ($cur).size))
    | `(sszUpdateSegment| [$j:term]!) =>
        appendSszGetExcept (← `(($cur)[$j]!)) segs (i + 1)
    | _ => Macro.throwError s!"sszGet: malformed path segment {seg}"
  else
    `(_root_.Except.ok $cur)

macro_rules
  | `(sszGet $base $head:ident $segs:sszUpdateSegment*) => do
      if segsHaveCheckedIndex segs then
        -- Checked-index form: out-of-range reads reject with the real index
        -- and bound, matching `IndexError`.
        appendSszGetExcept (← `(($base).view.$head)) segs 0
      else
        -- Field-only or all-`[i]!` form: pure bare read. Reduces for
        -- `rfl`/`decide` exactly as a hand-written `.view.path`; `[i]!`
        -- yields the element's `default` on a miss (no `Except`).
        let init : Lean.TSyntax `term ← `(($base).view.$head)
        appendSszGetSegments init segs 0

/-! ## `sszModify`: read-modify-write of one path -/

/-- Read-modify-write of one field or element on a boxed value, naming the path once.
Two forms: `sszModify t path := g` applies the function `g` to the current value, and
`sszModify t path as x => body` binds the current value to `x` and rewrites it to `body`
(the `fun`-free inline form, for `{ x with … }`-style updates). Both are pure syntactic
sugar over `sszUpdate t with path := … (sszGet t path)`, so the path is written once (no
read/write drift) and the expansion inherits `sszUpdate`'s write, including the cached
single-leaf update on a `[i]!` element, and `sszGet`'s read. Use it on the total `[i]!`
and field paths, where `sszGet` returns the element directly; a checked `[i]` read is
`Except IndexError`, which the transform cannot consume, so a checked read-modify-write
needs its own monadic spelling. -/
syntax (name := sszModifyFnStx)
    "sszModify " term:max ident sszUpdateSegment* " := " term : term
syntax (name := sszModifyAsStx)
    "sszModify " term:max ident sszUpdateSegment* " as " ident " => " term : term

-- Build the `sszUpdate` write-clause in its own `sszUpdateClause` quotation, then splice
-- the whole clause into `sszUpdate t with …`. Writing the path inline under `with` would
-- be misread: that position is `sepBy1(sszUpdateClause)`, so the quotation parser takes the
-- leading `$head` as a whole-clause antiquotation rather than the start of an inline clause.
macro_rules
  | `(sszModify $t $head:ident $segs:sszUpdateSegment* := $g) => do
      let clause ← `(sszUpdateClause|
        $head:ident $segs:sszUpdateSegment* :=
          (let cur := sszGet $t $head:ident $segs:sszUpdateSegment*; $g cur))
      `(sszUpdate $t with $clause)
  | `(sszModify $t $head:ident $segs:sszUpdateSegment* as $x:ident => $body) => do
      -- A `let` (not `(fun $x => …) read`) binds `$x` so its type is pinned by the read
      -- before `$body` elaborates; a `{ $x with … }` record body needs that type eagerly.
      let clause ← `(sszUpdateClause|
        $head:ident $segs:sszUpdateSegment* :=
          (let $x := sszGet $t $head:ident $segs:sszUpdateSegment*; $body))
      `(sszUpdate $t with $clause)

/-- Append `v` to a list field of a boxed value, naming the field once:
`sszAppend s f v` is the cap-clamping push, sugar for `sszModify s f as l => l.push v`
(so `sszUpdate s with f := (sszGet s f).push v`). The non-monadic boxed-state append; the
monadic state-threading wrapper is the spec's `appendState`. -/
syntax (name := sszAppendStx)
    "sszAppend " term:max ident sszUpdateSegment* ppSpace term:max : term

macro_rules
  | `(sszAppend $t $head:ident $segs:sszUpdateSegment* $v:term) =>
      `(sszModify $t $head:ident $segs:sszUpdateSegment* as l => l.push $v)

/-- Which cache flavour the macro is targeting. The elaborator
picks this from the base term's type and branches the emission. -/
private inductive CacheKind where
  | cached    -- `TreeBacked H T` (= `CachedSSZ H T`)
  | uncached  -- `UncachedSSZ H T`
  | box       -- `SSZ.Box H T`: closed sum; expand to two-arm match
  deriving Inhabited

/-- Extract the hasher `H` (as an `Expr`), `T` (as a `Name`), and
the cache flavour from the base term's type. The two accepted
shapes are concrete `TreeBacked H T` and concrete `UncachedSSZ H T`,
anything else is a clean macro-time error.

The hasher is returned as an `Expr` rather than a `Name` because
user-facing call sites expect the inferred-`H` to be delab-rendered
back into syntax (so the macro splices `Sha256`, or whatever `H`
was pinned at construction, into the cached path's emitted
`Node.ofShape` calls).

`T` is returned *both* as the whnf'd full application (`@Decl p…`, used by
`walkPath` so field caps are instantiated at the call site's concrete
parameters) *and* as its head `Name` (used to emit the value-type
annotations, whose suppressed parameters are re-synthesised at the call
site). For a `[Preset]`-generic container the application carries the
concrete preset, so a per-element write resolves the field cap to a literal
(or to the in-scope local `[Preset]` fvar) rather than a dangling telescope
variable. -/
private def extractConcreteCacheHT (ty : Expr) :
    MetaM (Expr × Expr × Name × CacheKind) := do
  let ty ← whnf ty
  match ty.getAppFn, ty.getAppArgs with
  | .const head _, args =>
      let kind? : Option CacheKind :=
        if head == ``SizzLean.Cache.TreeBacked then some .cached
        else if head == ``SizzLean.Cache.UncachedSSZ then some .uncached
        else if head == ``SizzLean.Cache.SSZ.Box then some .box
        else none
      match kind? with
      | some kind =>
          match args.toList with
          | hArg :: tArg :: _ =>
            let tArgW ← whnf tArg
            match tArgW.getAppFn with
            | .const tName _ => return (hArg, tArgW, tName, kind)
            | _ =>
                throwError "sszUpdate: value type in {head} is not a constant"
          | _ =>
              throwError "sszUpdate: {head} is missing required type arguments"
      | none =>
          throwError
            "sszUpdate: base must be one of `TreeBacked H T`, `UncachedSSZ H T`, \
             or `SSZ.Box H T`; got {ty}."
  | _, _ =>
      throwError
        "sszUpdate: base type is not a constant application (got {ty}). The macro requires a concrete \
         `TreeBacked H T`, `UncachedSSZ H T`, or `SSZ.Box H T` at the call site."

/-- Render a `List Bool` as Lean syntax for splicing into an emitted
term. Used (on the cached path) to bake gindex bit lists into the
emitted code as literals. -/
private def bitsToTermSyntax (bits : List Bool) : TermElabM (TSyntax `term) := do
  let elems : Array (TSyntax `term) ← bits.toArray.mapM fun b =>
    if b then `(true) else `(false)
  `([$elems,*])

/-- A single step along an update path. `field name` descends into a
structure field; `index i checked` descends into a vector / list element
(with `i : Nat` an arbitrary runtime term). `checked` is `true` for the
fallible `[i]` form (an out-of-range index rejects) and `false` for the
infallible `[i]!` form (an out-of-range write is a no-op, contributing no
error and no `Except` wrapping). -/
private inductive PathStep where
  | field (name : Name)
  | index (idx : TSyntax `term) (checked : Bool)
  deriving Inhabited

/-- A piece of the composed gindex-bits expression (cached path
only). `literal bs` is a compile-time-known bit list; `runtime e`
is a runtime `List Bool` expression. The final emitted bits-list
expression is the concatenation of these pieces. -/
private inductive BitsPiece where
  | literal (bits : List Bool)
  | runtime (stx : TSyntax `term)

/-- The per-element gindex base `2 ^ chunkDepth cap` as a term.

A *concrete* cap is folded to a single numeral at macro-expansion time, so
the emitted gindex reads as a plain literal: the common case, and the form
`decide` / `native_decide` reduce most cleanly (this is the fast path the
pre-symbolic-cap code always took). A `[Preset]`-resolved *symbolic* cap
can't be evaluated yet, so it stays the runtime expression `2 ^ chunkDepth
cap` over the delaborated cap, the same literal-or-symbolic split the derive
handler's `capToShapeSyntax` makes for shape descriptors. `chunkDepth` is an
ordinary function, so it reduces once the preset is pinned. `delab` (not
`exprToSyntax`) renders the cap's parameter fvar by name, which is in scope
at the emission site. -/
private def gindexBaseForCap (capExpr : Expr) : TermElabM (TSyntax `term) := do
  match ← Lean.Meta.evalNat (← whnf capExpr) |>.run with
  | some capVal =>
      pure <| Syntax.mkNumLit (toString (2 ^ SizzLean.Spec.chunkDepth capVal))
  | none =>
      let capSyn ← Lean.PrettyPrinter.delab capExpr
      `(2 ^ SizzLean.Spec.chunkDepth $capSyn)

/-- Walk an update path from `rootType` (the *concrete* `@Decl p…`
application read off the base term's type), accumulating gindex bits and
producing the terminal field type for `SSZRepr` instance synthesis.
Used only on the cached path.

Each `PathStep.field n` contributes a *literal* bit-list piece
(field index gindex is known at expansion time). Each
`PathStep.index i` contributes a *runtime* bit-list piece because
`i` is a runtime term, but its base (the per-tree gindex offset)
is still compile-time-known. List elements get an extra leading
`[false]` for the mix-in-length wrap.

Each field projection is instantiated at the *current* type's parameter
arguments (`instantiateForall … curTW.getAppArgs`), so a `[Preset]`-generic
container's field cap surfaces with the call site's concrete preset rather
than a fresh telescope variable. That keeps the per-element gindex base
(`2 ^ chunkDepth cap`) either a literal (concrete preset) or an expression
over the in-scope local `[Preset]` fvar, both of which delaborate and
re-elaborate cleanly.

Composite-element vectors / lists descend into the element's own
sub-tree (`gindexBits (base + i)`). Basic *packed* element indices
(`Vector UInt64 n`, `SSZList Gwei cap`, …) have no per-element
sub-tree, so the walk instead targets the *owning* field's gindex,
keeps that field as the terminal type, and returns `projDrop := 1`,
asking the caller to rebuild the whole field's subtree from the
index-updated `view` (see the module docstring's owner-rebuild
note). -/
private def walkPath (rootType : Expr) (path : Array PathStep) :
    TermElabM (Array BitsPiece × Expr × Nat) := do
  if path.isEmpty then throwError "sszUpdate: empty path"
  let mut curType : Expr := rootType
  let mut pieces : Array BitsPiece := #[]
  let mut terminalType? : Option Expr := none
  -- Trailing path steps the *caller* should drop when projecting the
  -- closure's sub-value: `1` for a packed-basic index terminal, whose
  -- gindex targets the owning field rather than the element (see the
  -- `.index` arm and the module docstring's owner-rebuild note).
  let mut projDrop : Nat := 0
  for hi : i in [0 : path.size] do
    let step := path[i]'hi.upper
    let isLast := i + 1 == path.size
    match step with
    | .field comp =>
        let env ← getEnv
        let curTW ← whnf curType
        let some curT := curTW.getAppFn.constName?
          | throwError "sszUpdate: expected a structure type, got {curType}"
        unless isStructure env curT do
          throwError "sszUpdate: '{curT}' is not a structure (path component '{comp}')"
        let fieldNames := getStructureFields env curT
        let some idx := fieldNames.findIdx? (· == comp)
          | throwError "sszUpdate: field '{comp}' not in structure '{curT}'"
        let numFields := fieldNames.size
        let chunkDepthVal := SizzLean.Spec.chunkDepth numFields
        let g := 2 ^ chunkDepthVal + idx
        pieces := pieces.push (.literal (SizzLean.Cache.MerkleTree.gindexBits g))
        let some info := getFieldInfo? env curT comp
          | throwError "sszUpdate: cannot find field info for '{comp}'"
        let projInfo ← getConstInfo info.projFn
        -- Instantiate the projection at *this* type's parameter args (the
        -- structure's params, e.g. a concrete `[Preset]`), then strip the
        -- remaining `self` binder. The field type then mentions the call
        -- site's preset, not a fresh telescope fvar, so a symbolic cap
        -- delaborates to something in scope at the emission site.
        let projInst ← instantiateForall projInfo.type curTW.getAppArgs
        let fieldType ← forallTelescope projInst fun _ body => pure body
        if isLast then
          terminalType? := some fieldType
        else
          curType := fieldType
    | .index iStx _ =>
        -- The gindex is identical for the checked `[i]` and infallible `[i]!`
        -- forms; the `checked` flag only governs the issue-time guard, handled
        -- in `pathGuardExcept`, not the spine address computed here.
        -- Composite-element index: descend into the element's own
        -- sub-tree (gindex `base + i`). Basic *packed* element: the
        -- element shares a 32-byte chunk with its neighbours and has
        -- no sub-tree of its own, so we can't key a write at an
        -- element gindex. Instead point the write at the *owning*
        -- field (the bits accumulated so far already reach it),
        -- keep the terminal type as that field, and ask the caller
        -- via `projDrop := 1` to rebuild the whole field's subtree
        -- from the index-updated view. Byte-identical to the manual
        -- whole-field workaround, just automatic.
        -- Resolve the container head. Prefer the *surface* type so a
        -- direct `SSZList α cap` matches without unfolding (`whnf` would
        -- reduce the `SSZList` def all the way to its `Subtype` and lose
        -- the head); fall back to `whnf` only for abbreviation-wrapped
        -- field types (e.g. `Bytes32`/`ExVersion` → `Vector …`), where
        -- `Vector` is a structure so `whnf` stops at it.
        let curTypeW ←
          if curType.isAppOfArity ``SizzLean.Repr.SSZList 2
              || curType.isAppOfArity ``Vector 2 then
            pure curType
          else
            whnf curType
        if curTypeW.isAppOfArity ``SizzLean.Repr.SSZList 2 then
          let α := curTypeW.appFn!.appArg!
          if ← isCompositeElem α then
            -- The element gindex base is `2 ^ chunkDepth cap` (`gindexBaseForCap`:
            -- a folded literal for a concrete cap, the runtime `2 ^ chunkDepth
            -- cap` for a `[Preset]`-resolved symbolic one). The list's body
            -- subtree is the left child of the mix-in-length pair, hence the
            -- leading `[false]`.
            pieces := pieces.push (.literal [false])
            let baseSyn ← gindexBaseForCap curTypeW.appArg!
            pieces := pieces.push <| .runtime <|
              ← `(_root_.SizzLean.Cache.MerkleTree.gindexBits ($baseSyn + $iStx))
            if isLast then terminalType? := some α else curType := α
          else
            unless isLast do
              throwError "sszUpdate: cannot index past a basic packed element '{α}'"
            terminalType? := some curTypeW
            projDrop := 1
        else if curTypeW.isAppOfArity ``Vector 2 then
          let α := curTypeW.appFn!.appArg!
          if ← isCompositeElem α then
            -- Same `gindexBaseForCap` split as the `SSZList` arm, minus the
            -- mix-in-length `[false]` (a `Vector`'s root is its body subtree
            -- directly, with no length wrap). The symbolic length is exactly a
            -- `[Preset]`-generic fixed `Vector` field
            -- (`Vector Root SLOTS_PER_HISTORICAL_ROOT`, …).
            let baseSyn ← gindexBaseForCap curTypeW.appArg!
            pieces := pieces.push <| .runtime <|
              ← `(_root_.SizzLean.Cache.MerkleTree.gindexBits ($baseSyn + $iStx))
            if isLast then terminalType? := some α else curType := α
          else
            unless isLast do
              throwError "sszUpdate: cannot index past a basic packed element '{α}'"
            terminalType? := some curTypeW
            projDrop := 1
        else
          throwError "sszUpdate: index `[…]` requires the current type to be `Vector` or `SSZList`, got {curType}"
  let some ty := terminalType? | throwError "sszUpdate: walk produced no terminal type"
  return (pieces, ty, projDrop)
where
  isCompositeElem (α : Expr) : MetaM Bool := do
    let αW ← whnf α
    if αW.isConstOf ``Bool then return false
    if αW.isConstOf ``UInt8 || αW.isConstOf ``UInt16 ||
       αW.isConstOf ``UInt32 || αW.isConstOf ``UInt64 then return false
    if αW.isAppOfArity ``BitVec 1 then return false
    return true

/-- Concatenate `BitsPiece` pieces into a single `List Bool` term
expression. Literal pieces are spliced as list literals; runtime
pieces stay as-is. -/
private def piecesToTermSyntax (pieces : Array BitsPiece) :
    TermElabM (TSyntax `term) := do
  if pieces.isEmpty then return ← `(([] : List Bool))
  let parts : Array (TSyntax `term) ← pieces.mapM fun p =>
    match p with
    | .literal bs => bitsToTermSyntax bs
    | .runtime s  => pure s
  let mut acc : TSyntax `term := parts[parts.size - 1]!
  for k in (List.range (parts.size - 1)).reverse do
    let head := parts[k]!
    acc ← `(($head : List Bool) ++ $acc)
  return acc

/-- Build a sequence of nested record-update / `set!` syntax for the
view side. Given path `[f, [i], g]`, base `vPrev`, and value `v`,
emits something like:

```lean
{ vPrev with f :=
    (vPrev.f).set! i { (vPrev.f.get! i) with g := v } }
```

Works for both cache flavours, purely value-level. -/
private def nestedViewUpdate (vPrev : TSyntax `term) (path : Array PathStep)
    (rhs : TSyntax `term) : TermElabM (TSyntax `term) := do
  let mut cur : TSyntax `term := rhs
  for k in (List.range path.size).reverse do
    let step := path[k]!
    let mut ownerStx : TSyntax `term := vPrev
    for j in [0 : k] do
      match path[j]! with
      | .field n =>
          let projIdent := mkIdent n
          ownerStx ← `(($ownerStx).$projIdent:ident)
      | .index i _ =>
          ownerStx ← `(($ownerStx)[$i]!)
    match step with
    | .field n =>
        let lastIdent := mkIdent n
        cur ← `({ $ownerStx with $lastIdent:ident := $cur })
    | .index i _ =>
        -- `set!` no-ops on an out-of-range index for both `[i]` and `[i]!`;
        -- the difference is only whether the issue-time guard rejects first.
        cur ← `(($ownerStx).set! $i $cur)
  return cur

/-- Emit an `Option`-typed projection of an update path against a
base term, then wrap the final value via `final`. For each index
step `[i]`, emits a runtime bounds check (`i < container.size`)
that short-circuits to `none` when out-of-bounds, mirroring the
view side's `Array.set!` no-op semantics so the cache stays in
lockstep with `view` even on writes the user intended for an
index that no longer exists.

For path `[f, [i], g]` and base `v`, the emitted expression has
shape:
```
if i < v.f.size then
  <final applied to v.f[i]!.g>
else
  none
```

`final` is the continuation that builds the
`some (Node.ofShape …)` payload from the final projected value.
Used on the cached path to emit closures that re-read the
sub-value from the current `view` at commit time. -/
private partial def viewProjectionOption
    (base : TSyntax `term) (path : Array PathStep)
    (final : TSyntax `term → TermElabM (TSyntax `term)) :
    TermElabM (TSyntax `term) := do
  go base 0
where
  go (cur : TSyntax `term) (k : Nat) : TermElabM (TSyntax `term) := do
    if h : k < path.size then
      let step := path[k]'h
      match step with
      | .field n =>
          let projIdent := mkIdent n
          let cur' ← `(($cur).$projIdent:ident)
          go cur' (k + 1)
      | .index i _ =>
          -- The commit-time bounds check is kept for both `[i]` and `[i]!`:
          -- it mirrors the view's `set!` no-op so an out-of-range write drops
          -- the pending entry rather than corrupting the tree.
          let cur' ← `(($cur)[$i]!)
          let inner ← go cur' (k + 1)
          `(if ($i) < ($cur).size then $inner else none)
    else
      final cur

/-- Parse one clause's syntax into a `PathStep` array plus the
value term. Shared between cache flavours. -/
private def parseClause (clauseStx : Syntax) :
    Array PathStep × TSyntax `term :=
  let headSteps : Array PathStep :=
    clauseStx[0].getId.components.toArray.map PathStep.field
  let restSteps : Array PathStep :=
    clauseStx[1].getArgs.flatMap (fun seg =>
      match seg.getKind with
      | ``sszUpdateSegmentField =>
          seg[1].getId.components.toArray.map PathStep.field
      | ``sszUpdateSegmentIndex =>
          #[PathStep.index ⟨seg[1]⟩ true]
      | ``sszUpdateSegmentIndexBang =>
          #[PathStep.index ⟨seg[1]⟩ false]
      | _ => #[])
  let path : Array PathStep := headSteps ++ restSteps
  let valStx : TSyntax `term := ⟨clauseStx[3]⟩
  (path, valStx)

/-- Build the view-update let-chain shared by both cache flavours.
For `n` clauses, emits:

```lean
let v_0 := t₀.view
let v_1 := <nested-with on v_0 for clause 0>
…
let v_n := <nested-with on v_{n-1} for clause n-1>
v_n
```

Each clause's update reads the *previous* view binding so
shared-prefix clauses compose correctly. `t₀.view` is field-access
on the concrete cache type, works for `TreeBacked` and
`UncachedSSZ` alike (both have a `view` field). -/
private def buildViewLetChain
    (clausePaths : Array (Array PathStep))
    (clauseValues : Array (TSyntax `term)) :
    TermElabM (TSyntax `term) := do
  let mkVName (i : Nat) : Ident := mkIdent (Name.mkSimple s!"v_{i}")
  let n := clausePaths.size
  let mut body : TSyntax `term := mkVName n
  for i in (List.range n).reverse do
    let path := clausePaths[i]!
    let valStx := clauseValues[i]!
    let vPrev := mkVName i
    let vCur  := mkVName (i + 1)
    let updateRHS ← nestedViewUpdate vPrev path valStx
    body ← `(let $vCur:ident := $updateRHS; $body)
  `(let $(mkVName 0):ident := t₀.view; $body)

/-- A path step that is a *checked* index `[i]` (vs a field `.f` or an
infallible `[i]!`, both of which never reject). This is what decides whether
an `sszUpdate` returns `Except`. -/
private def isCheckedIdxStep : PathStep → Bool
  | .index _ checked => checked
  | .field _ => false

/-- Whether any clause has a *checked* index segment, the only forms that can
reject, hence the only ones whose `sszUpdate` returns `Except IndexError _`
rather than the bare cache value. An all-`[i]!` (or field-only) update is bare. -/
private def clausesHaveCheckedIndex (clauses : Array Syntax) : Bool :=
  clauses.any (fun c => (parseClause c).1.any isCheckedIdxStep)

/-- Walk one update path from `t₀.view`, emitting a bounds check at each
index step that rejects with the *real* index and bound when out of range.
`rest` is the continuation evaluated once every index in the path is in
range (the next path's check, or `Except.ok ()` at the chain's end); the
result has type `Except IndexError Unit`. Mirrors `viewProjectionOption`'s
nested `if i < owner.size` walk, rejecting with `IndexError.indexError i
owner.size` instead of collapsing to `none`. -/
private partial def pathGuardExcept
    (path : Array PathStep) (rest : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  go (← `(t₀.view)) 0
where
  go (cur : TSyntax `term) (k : Nat) : TermElabM (TSyntax `term) := do
    if h : k < path.size then
      let step := path[k]'h
      match step with
      | .field n =>
          let projIdent := mkIdent n
          go (← `(($cur).$projIdent:ident)) (k + 1)
      | .index i checked =>
          let inner ← go (← `(($cur)[$i]!)) (k + 1)
          -- Only a checked `[i]` rejects; an infallible `[i]!` descends with
          -- no guard (its out-of-range write is a no-op at the view / commit).
          if checked then
            `(if ($i) < ($cur).size then $inner
              else _root_.Except.error
                     (_root_.SizzLean.Cache.IndexError.indexError ($i) ($cur).size))
          else
            pure inner
    else
      pure rest

/-- Issue-time bounds guard for index clauses: an `Except IndexError Unit`
that is `.ok ()` when every index across every clause lands inside its owner
*in the original view* `t₀.view`, and otherwise the *first* out-of-range
index's `.error (indexError idx bound)`, carrying its real values. Chains
the per-path checks (`pathGuardExcept`) in program order so the first failing
index wins. This is the eager, program-order check that turns an
out-of-range write into a rejection; the deferred commit closures keep their
own re-check so a write that a *later* op supersedes is dropped at commit
rather than rejected here. -/
private def buildIndexGuardExcept (clausePaths : Array (Array PathStep)) :
    TermElabM (TSyntax `term) := do
  let mut guard : TSyntax `term ← `(_root_.Except.ok ())
  for path in clausePaths.reverse do
    if path.any isCheckedIdxStep then
      guard ← pathGuardExcept path guard
  return guard

/-- Uncached emission path. Kept *deliberately small*: parse the
clauses into (path, value) pairs, fold them into a single view-
update expression, wrap in `{ view := … } : UncachedSSZ H T`.

No `walkPath`, no `Node.ofShape`, no gindex-bit computation. The
emitted term reduces, via plain `zeta` on the `let t₀ := …` and
the view-update lets, to:

```lean
{ view := { … { base.view with f₁ := v₁ } … with fₙ := vₙ } }
  : UncachedSSZ H T
```

This shape is what proofs about uncached state-transition
functions want to see. `rfl` closes `(sszUpdate u with f := v).view
= { u.view with f := v }` and `(sszUpdate u with f := v).hashTreeRoot
= SSZ.hashTreeRoot H ({ u.view with f := v })` after reduction,
no cache invariant, no Merkle bookkeeping in the goal. -/
private def buildSszUpdateUncached
    (baseStx hashStx : TSyntax `term) (tIdent : Ident)
    (clauses : Array Syntax) : TermElabM (TSyntax `term) := do
  let mut clausePaths : Array (Array PathStep) := #[]
  let mut clauseValues : Array (TSyntax `term) := #[]
  for clauseStx in clauses do
    let (path, valStx) := parseClause clauseStx
    clausePaths := clausePaths.push path
    clauseValues := clauseValues.push valStx
  let viewLetChain ← buildViewLetChain clausePaths clauseValues
  if clausePaths.any (·.any isCheckedIdxStep) then
    -- Checked-index form: reject (in program order) when a `[i]` index is out
    -- of range, matching the pyspec's `IndexError`. `t₀.view` is read by both
    -- the guard and the view-update chain; `.map` builds the update only on
    -- the guard's `.ok` branch, so a failed guard writes nothing and carries
    -- the offending index/bound forward. Any `[i]!` clauses skip the guard.
    let guard ← buildIndexGuardExcept clausePaths
    `(
      let t₀ := $baseStx
      (($guard).map (fun _ =>
          (({ view := $viewLetChain }) : _root_.SizzLean.Cache.UncachedSSZ $hashStx $tIdent)) :
        _root_.Except _root_.SizzLean.Cache.IndexError (_root_.SizzLean.Cache.UncachedSSZ $hashStx $tIdent)))
  else
    `(
      let t₀ := $baseStx
      (({ view := $viewLetChain }) :
        _root_.SizzLean.Cache.UncachedSSZ $hashStx $tIdent))

/-- Cached emission path. Walks each clause's path through `T`'s
nested structure to compute gindex bit-lists and per-clause
replacement sub-Merkle-trees, then emits one batched
`Node.setManyAt` call paired with the view-update chain. All the
Merkle work lives here. -/
private def buildSszUpdateCached
    (baseStx hashStx : TSyntax `term) (tIdent : Ident) (tType : Expr)
    (clauses : Array Syntax) : TermElabM (TSyntax `term) := do
  let mut clausePaths : Array (Array PathStep) := #[]
  let mut clauseValues : Array (TSyntax `term) := #[]
  let mut updatePairs : Array (TSyntax `term) := #[]
  let viewIdent : Ident := mkIdent (Name.mkSimple "__ssz_view")
  for clauseStx in clauses do
    let (path, valStx) := parseClause clauseStx
    clausePaths := clausePaths.push path
    clauseValues := clauseValues.push valStx
    let (bitsPieces, terminalType, projDrop) ← walkPath tType path
    -- For a packed-basic index terminal, `walkPath` keys the gindex at
    -- the owning vector/list field and sets `projDrop := 1`; project
    -- that owner (drop the trailing index) so the closure rebuilds the
    -- whole field's subtree from the index-updated view.
    let projPath : Array PathStep := path.extract 0 (path.size - projDrop)
    let fieldTypeStx : TSyntax `term ← PrettyPrinter.delab terminalType
    let bitsListStx ← piecesToTermSyntax bitsPieces
    -- Emit a `PendingWrite T` closure (`T → Option Node`): at
    -- commit time it projects the latest sub-value out of
    -- `view` and builds the matching sub-tree via
    -- `Node.ofShape`. Index steps in the path emit a bounds
    -- check; if any index goes OOB at commit time, the closure
    -- returns `none` and the pending entry is dropped, the
    -- view side's `Array.set!` no-op semantics for OOB indices
    -- is mirrored exactly. Field-only paths skip the check and
    -- always return `some`.
    --
    -- Reading from `view` at commit (rather than capturing
    -- `valStx` here) is what makes overlapping parent/child
    -- writes mutually consistent, the parent's closure
    -- naturally sees every later child override that has been
    -- folded into the shared view. Overwritten closures (at the
    -- same gindex) are still dropped by `TreeMap.insert` and
    -- never run.
    let closureBody ← viewProjectionOption viewIdent projPath fun proj => `(
      some (_root_.SizzLean.Cache.MerkleTree.Node.ofShape $hashStx
              (@_root_.SizzLean.SSZRepr.shape  $fieldTypeStx _)
              (@_root_.SizzLean.SSZRepr.toRepr $fieldTypeStx _ $proj)))
    let pairStx ← `(
      (($bitsListStx : List Bool),
        ((fun ($viewIdent:ident : $tIdent) => $closureBody)
         : _root_.SizzLean.Cache.PendingWrite $tIdent)))
    updatePairs := updatePairs.push pairStx
  let viewLetChain ← buildViewLetChain clausePaths clauseValues
  let updatesListStx ← `([$updatePairs,*])
  -- Cached emission: accumulate into the pending overlay rather than
  -- walking the spine here. Cross-statement batching falls out
  -- automatically, the spine walk runs once per `commit`, which the
  -- root reader (`hashTreeRootCached`) triggers itself.
  if clausePaths.any (·.any isCheckedIdxStep) then
    -- Checked-index form: a failed issue-time guard short-circuits to `.error`
    -- *without* evaluating `addPendingMany` (it sits under `.map`'s closure,
    -- run only on `.ok`), so no pending write is recorded for an out-of-range
    -- `[i]` index, and the real index/bound ride out on the error. (Recorded
    -- writes still re-check at commit; `[i]!` clauses skip the guard and rely
    -- on that commit re-check to drop an out-of-range write.)
    let guard ← buildIndexGuardExcept clausePaths
    `(
      let t₀ := $baseStx
      (($guard).map (fun _ =>
          ((_root_.SizzLean.Cache.TreeBacked.addPendingMany t₀ $updatesListStx $viewLetChain) : _root_.SizzLean.Cache.TreeBacked $hashStx $tIdent)) :
        _root_.Except _root_.SizzLean.Cache.IndexError (_root_.SizzLean.Cache.TreeBacked $hashStx $tIdent)))
  else
    `(
      let t₀ := $baseStx
      ((_root_.SizzLean.Cache.TreeBacked.addPendingMany t₀
          $updatesListStx
          $viewLetChain) :
        _root_.SizzLean.Cache.TreeBacked $hashStx $tIdent))

/-- Box emission path. The base term has type `SSZ.Box H T`, the
closed sum over the two cache flavours. The macro builds each arm
*body* by calling the per-flavour syntax builders on a fresh arm
binder, then assembles a two-arm match that wraps each body in
the matching `SSZ.Box` constructor.

The emitted shape is, schematically:

```lean
match $baseStx with
| SSZ.Box.cached __ssz_box_t   => SSZ.Box.cached   <cached body with __ssz_box_t>
| SSZ.Box.uncached __ssz_box_t => SSZ.Box.uncached <uncached body with __ssz_box_t>
```

The closed-world `Box` inductive makes the two arms exhaustive at
the type level, no panic, no default case to maintain. The
cached arm gets full O(log N) spine-sharing emission; the uncached
arm gets the trivial struct rewrite. -/
private def elabSszUpdateBox
    (baseStx hashStx : TSyntax `term) (tIdent : Ident) (tType : Expr)
    (clauses : Array Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let armBinder : TSyntax `term ← `(__ssz_box_t)
  let cachedBody   ← buildSszUpdateCached   armBinder hashStx tIdent tType clauses
  let uncachedBody ← buildSszUpdateUncached armBinder hashStx tIdent   clauses
  let finalStx ←
    if clausesHaveCheckedIndex clauses then
      -- Index form: each arm body is `Except IndexError (cache value)`;
      -- map the constructor over the `.ok` so the whole match is
      -- `Except IndexError (SSZ.Box H T)`.
      `(
        let __ssz_box_s := $baseStx
        match __ssz_box_s with
        | _root_.SizzLean.Cache.SSZ.Box.cached __ssz_box_t =>
            ($cachedBody).map _root_.SizzLean.Cache.SSZ.Box.cached
        | _root_.SizzLean.Cache.SSZ.Box.uncached __ssz_box_t =>
            ($uncachedBody).map _root_.SizzLean.Cache.SSZ.Box.uncached)
    else
      `(
        let __ssz_box_s := $baseStx
        match __ssz_box_s with
        | _root_.SizzLean.Cache.SSZ.Box.cached __ssz_box_t =>
            _root_.SizzLean.Cache.SSZ.Box.cached $cachedBody
        | _root_.SizzLean.Cache.SSZ.Box.uncached __ssz_box_t =>
            _root_.SizzLean.Cache.SSZ.Box.uncached $uncachedBody)
  elabTerm finalStx expectedType?

@[term_elab sszUpdateStx]
private def elabSszUpdate : TermElab := fun stx expectedType? => do
  let baseStx : TSyntax `term := ⟨stx[1]⟩
  let clausesNode := stx[3]
  let clauses : Array Syntax :=
    clausesNode.getArgs.filter (·.getKind == ``sszUpdateClauseDotted)
  if clauses.isEmpty then
    throwError "sszUpdate: at least one clause required"
  let base ← elabTerm baseStx none
  let baseType ← inferType base
  let (hExpr, tType, T, kind) ← extractConcreteCacheHT baseType
  let hashStx : TSyntax `term ← PrettyPrinter.delab hExpr
  let tIdent : Ident := mkIdent (`_root_ ++ T)
  -- Early dispatch. Each branch emits in a different shape; the
  -- uncached and box branches never touch `walkPath` or any Merkle
  -- machinery on the uncached arm, so unfolding `sszUpdate` in a
  -- proof about an `UncachedSSZ` (or `SSZ.Box`-on-uncached) value
  -- drags in nothing extra.
  match kind with
  | .uncached => do
      let stx ← buildSszUpdateUncached baseStx hashStx tIdent clauses
      elabTerm stx expectedType?
  | .cached   => do
      let stx ← buildSszUpdateCached baseStx hashStx tIdent tType clauses
      elabTerm stx expectedType?
  | .box      => elabSszUpdateBox baseStx hashStx tIdent tType clauses expectedType?

end SizzLean.Cache
