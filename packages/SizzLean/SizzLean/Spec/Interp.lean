import SizzLean.Spec.Type

/-!
# `SizzLean.Spec.Interp`: values inhabiting each SSZ shape

For each `SSZType` description, `SSZType.interp` returns the Lean
`Type` whose values are exactly the well-formed SSZ values of that
shape. This is the bridge between the syntactic universe in
`Spec/Type.lean` and the operations (`serialize`, `deserialize`,
`hashTreeRoot`) that consume real values.

Mirrors the consensus-specs *§SSZ Types* section. The unused SSZ
forms (`Union`, `ProgressiveContainer` / `StableContainer` / `Profile`
from EIP-7495, `ProgressiveList` / `ProgressiveBitlist` from EIP-7916,
`CompatibleUnion` from EIP-8016) are out-of-scope here, see the
docstring on `SizzLean.Spec.Type` for the rationale.

## Background: how Lean accepts recursive definitions

A recursive `def` must be proved total before Lean will accept it.
The compiler offers two paths:

* **Structural recursion**: the cheap path. Each recursive call's
  argument must be a *strict subterm* of the caller's input, where
  "subterm" is read off the inductive's definition (pattern
  matches expose subterms). Termination follows automatically. The
  *equation compiler* is the part of Lean's elaborator that
  translates a top-level `def` with pattern matches into the
  primitive recursor and checks this property.
* **Well-founded recursion**: the general path. The programmer
  supplies a `termination_by` measure (some quantity that
  decreases on every recursive call) and Lean asks for proof. More
  powerful but heavier.

The definitions below use the structural path, which is what
shapes the `mutual` block.

## Why a `mutual` block

A natural sketch of `interp` (matching ARCHITECTURE.md §3.2)
defines the `container` case as `HList SSZType.interp fs`, a
heterogeneous list parameterised by `interp` itself. The
structural checker rejects that form: passing the recursive
function as a higher-order argument hides the descent on `fs`,
and the equation compiler reports *"unexpected occurrence of
recursive application"*. Well-founded recursion fares no better
because the obligation `sizeOf a < sizeOf (.container fs)` lacks
the membership hypothesis `a ∈ fs` that would make it provable.

The fix is to inline each list traversal as a mutually recursive
helper that consumes its list cons-by-cons. Each helper recurses
structurally on its list argument; `interp` calls the helpers on
subterms of its own argument (`fs` is a subterm of `.container fs`,
etc.). All four helpers are mutually structural-recursive, which the
checker accepts.

Semantically the result is the same heterogeneous tuple a user would
expect, `interp (.container [t₁, t₂]) = (t₁.interp × (t₂.interp × PUnit))`,
isomorphic to the `HList` formulation. The cost is one extra layer
of `Prod` nesting at the type level; the benefit is a structurally
recursive, total definition that downstream proofs can `simp`
through.

## Lean idioms used here, annotated on first appearance

* `{ x : α // p x }`: anonymous-subtype syntax: a pair of a value
  and a proof of `p x`, with the proof erased at runtime. Used to
  enforce capacity bounds on `list` and `bitlist`.
* `Vector α n` (Lean core ≥ 4.10): length-indexed `Array`-backed
  structure with `xs[i]` indexing.
* `mutual … end`: declares a block of mutually recursive definitions
  whose calls between members are checked for joint termination.

-/

set_option autoImplicit false

namespace SizzLean.Spec

mutual

/-- Map an SSZ description to the Lean type its values inhabit.

`uintN` widths beyond `{8,16,32,64}` fall back to `BitVec n`, which
keeps the function total without committing to a Lean representation
for the larger widths (`UInt128`/`UInt256` are not in core);
downstream code can pattern-match on the description if it wants
those native types when they ship. -/
@[reducible] def SSZType.interp : SSZType → Type
  | .uintN 8                  => UInt8
  | .uintN 16                 => UInt16
  | .uintN 32                 => UInt32
  | .uintN 64                 => UInt64
  | .uintN n                  => BitVec n
  | .bool                     => Bool
  | .vector t n               => Vector t.interp n
  | .list t cap               => { xs : Array t.interp // xs.size ≤ cap }
  | .bitvector n              => BitVec n
  | .bitlist cap              => { bs : Array Bool // bs.size ≤ cap }
  | .container fs             => SSZType.interpFields fs

/-- Heterogeneous tuple over a `List SSZType`: one component per
field, encoded as right-nested `Prod` terminated by `PUnit`. The
empty container interps to `PUnit` (single element), matching the
spec's "empty container has a single canonical value" intent. -/
@[reducible] def SSZType.interpFields : List SSZType → Type
  | []      => PUnit
  | t :: ts => SSZType.interp t × SSZType.interpFields ts

end

/-! ## Spot-check: definitional equality across the four shape
families. Each `example : … := rfl` is a build-time assertion that
the two sides are definitionally equal; `rfl` is rejected by
elaboration otherwise. Type equality is propositional (not
`Decidable`) in Lean 4, so the `example := rfl` form is the
correct idiom here; CLAUDE.md explicitly lists it as the
load-bearing alternative to forbidden
`#eval` / `#check` / `#print`.

Under the hood, `rfl` here is `@rfl Type (SSZType.interp …)`. Lean
infers the universe (`Type 0` for all our shapes) and the LHS as the
expected term, then the kernel reduces `SSZType.interp` arm-by-arm
until both sides match. Failure to reduce manifests as an
"expected_type ≠ got_type" elaboration error, not a runtime panic. -/

example : SSZType.interp .bool             = Bool          := rfl
example : SSZType.interp (.uintN 64)       = UInt64        := rfl
example : SSZType.interp (.uintN 32)       = UInt32        := rfl
-- The fourth example exercises a *recursive* arm: `interp (.vector .bool 3)`
-- unfolds to `Vector (interp .bool) 3` which further unfolds to
-- `Vector Bool 3`. The kernel performs both reductions to close `rfl`.
example : SSZType.interp (.vector .bool 3) = Vector Bool 3 := rfl

end SizzLean.Spec
