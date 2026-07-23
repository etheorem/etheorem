import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving

/-!
# `SizzLeanTests.ReprExamples`: typechecker-honest gates for `SSZRepr`

Per CLAUDE.md's *literate by default* discipline, every
user-facing API gets an `example` block the typechecker keeps
honest. This file holds the acceptance examples for `SSZRepr`: a
hand-written instance on a two-field `Pair` structure and its
`deriving`-generated counterpart. Each compiles only if the
corresponding piece of library machinery is correct, so a green
build is a passed gate.

Lives in `SizzLeanTests/` rather than `SizzLean/Repr/` so the
fixture structures (`Pair`, `DPair`) don't ride along on every
`import SizzLean`, they're acceptance tests, not part of the
user-facing surface.

## Why `Pair {a b : Bool}` as the example

`SSZ.roundtrip` is gated by `SSZType.BasicSupported r.shape`
(`Repr/Class.lean`); `BasicSupported` covers the four
native-width integers (`.uintN 8` / `16` / `32` / `64`), `.bool`,
the bit shapes, and the fixed-size composites (see
`Spec/BasicSupported.lean`). The smallest non-trivial user
structure that lives in `BasicSupported` is a two-`Bool`
container, exactly the `Pair` defined below.

The integer examples after the `Pair` block exercise the four
`uintN` arms of `BasicSupported`: thin wrappers around
`UInt8` / `UInt16` / `UInt32` / `UInt64`, each closing
`SSZ.roundtrip` via the corresponding constructor. Composite
arms (`vectorFixed`, `listFixed`, `containerFixed`) are exercised
further down at the spec-level `decode_encode`.
-/

set_option autoImplicit false

namespace SizzLeanTests.ReprExamples

open SizzLean

/-- Two-`Bool` container, the canonical example. -/
structure Pair where
  a : Bool
  b : Bool
  deriving DecidableEq, Repr

/-- Hand-written `SSZRepr` instance for `Pair`.

* `shape` is `.container [.bool, .bool]`, what the
  `deriving SSZRepr` handler synthesises mechanically.
* `toRepr` projects the two booleans into the right-nested `Prod`
  chain `interpFields [.bool, .bool] = Bool × Bool × PUnit`.
* `fromRepr` destructures the chain back into a `Pair`.
* Both iso laws close by `rfl`: `fromRepr ∘ toRepr` builds
  `{ a := p.a, b := p.b }` (structurally `p`); `toRepr ∘ fromRepr`
  builds `(r.1, r.2.1, PUnit.unit)` and matches `r` because `PUnit`
  has a single inhabitant. -/
instance instSSZReprPair : SSZRepr Pair where
  shape    := .container [.bool, .bool]
  toRepr   := fun p => (p.a, p.b, PUnit.unit)
  fromRepr := fun ⟨a, b, _⟩ => { a := a, b := b }
  to_from  := fun _ => rfl
  from_to  := fun ⟨_, _, u⟩ => by cases u; rfl

/-- Acceptance check: roundtrip closes via `SSZ.roundtrip`, which
dispatches on the general `containerFixed` arm with the explicit
field-list witness `cons .bool rfl (cons .bool rfl nil)`. The
Lean typechecker rejects this `example` if either the iso laws
fail or the shape sits outside `BasicSupported`. -/
example (p : Pair) : SSZ.deserialize (SSZ.serialize p) = .ok p :=
  SSZ.roundtrip (.containerFixed (.cons .bool rfl (.cons .bool rfl .nil))) p

/-! ### `deriving SSZRepr` example

Same shape as `Pair` (two `Bool` fields), but the `SSZRepr`
instance is synthesised by the `deriving` handler in
`Repr/Deriving.lean` instead of being written out by hand.
Acceptance is twofold: the declaration compiles (the handler ran
successfully) and the roundtrip example closes via `SSZ.roundtrip`
(the synthesised instance is correct end-to-end). -/

/-- Two-`Bool` container, `SSZRepr` synthesised. -/
structure DPair where
  a : Bool
  b : Bool
  deriving SSZRepr

/-- Acceptance check: roundtrip on the `deriving`-generated
instance. Closes through the same `containerFixed` arm as the
hand-written `Pair` example, the synthesised `shape` must
definitionally equal `.container [.bool, .bool]`. -/
example (p : DPair) : SSZ.deserialize (SSZ.serialize p) = .ok p :=
  SSZ.roundtrip (.containerFixed (.cons .bool rfl (.cons .bool rfl .nil))) p

/-! ### Integer arm examples: the four `uintN` widths

Each `example` exercises one of the four `uintN` constructors of
`BasicSupported`. The library-provided `SSZRepr` instances for
`UInt{8,16,32,64}` (in `Repr/Instances.lean`) all use the identity
iso, so the user-surface `SSZ.serialize` / `SSZ.deserialize` just
delegate to the spec functions and `SSZ.roundtrip` closes by
direct application of the matching predicate constructor.

These compile only if `decode_encode` discharges the integer arms;
they are the typechecker-honest gate that the integer support
holds end-to-end through the user surface. -/

example (x : UInt8) : SSZ.deserialize (SSZ.serialize x) = .ok x :=
  SSZ.roundtrip .uintN8 x

example (x : UInt16) : SSZ.deserialize (SSZ.serialize x) = .ok x :=
  SSZ.roundtrip .uintN16 x

example (x : UInt32) : SSZ.deserialize (SSZ.serialize x) = .ok x :=
  SSZ.roundtrip .uintN32 x

example (x : UInt64) : SSZ.deserialize (SSZ.serialize x) = .ok x :=
  SSZ.roundtrip .uintN64 x

/-! ### Wide integer arm examples: `uintN 128` and `uintN 256`

The `SSZRepr (BitVec 128)` / `(BitVec 256)` instances
(`Repr/Instances.lean`) pin the two spec-only widths at shapes
`.uintN 128` / `.uintN 256` with identity isos. These gates
compile only if `decode_encode` discharges the wide arms
(`Proofs/UIntWide.lean`) through the user surface, and, unlike the
narrow arms, they carry no `bv_decide` axiom. -/

example (x : BitVec 128) : SSZ.deserialize (SSZ.serialize x) = .ok x :=
  SSZ.roundtrip .uintN128 x

example (x : BitVec 256) : SSZ.deserialize (SSZ.serialize x) = .ok x :=
  SSZ.roundtrip .uintN256 x

/-! ### Composite arm examples

`BasicSupported` also covers general `vectorFixed`, `listFixed`,
and `containerFixed`. Each arm carries small side-conditions
(`0 < n` for vectors, `0 < t.fixedByteSize` for lists, an
`allFixedSize` field list for containers); the witnesses are
constructed inline below.

These examples exercise the *spec-level* `decode_encode` rather
than the user-surface `SSZ.roundtrip`. The user-surface path
would require `SSZRepr` instances on the composite types
(`Vector UInt64 4` etc.) plus matching the synthesised `shape`
to the predicate witness, straightforward but mechanical.
-/

open SizzLean.Proofs SizzLean.Spec

/-- Roundtrip for a 4-element `Vector UInt64`. The witness:
`vectorFixed (h_pos := …) (h_t := .uintN64) (h_t_fixed := rfl)`. -/
example (v : Vector UInt64 4) :
    SSZType.deserialize (.vector (.uintN 64) 4)
        (SSZType.serialize (.vector (.uintN 64) 4) v) =
      Except.ok (v, (SSZType.serialize (.vector (.uintN 64) 4) v).size) :=
  decode_encode (.vectorFixed (by decide) .uintN64 rfl) v

/-- Roundtrip for a `SSZ.List UInt32 cap`. The witness:
`listFixed (h_t := .uintN32) (h_t_fixed := rfl) (h_sz_pos := …)`. -/
example (xs : { ys : Array UInt32 // ys.size ≤ 100 }) :
    SSZType.deserialize (.list (.uintN 32) 100)
        (SSZType.serialize (.list (.uintN 32) 100) xs) =
      Except.ok (xs, (SSZType.serialize (.list (.uintN 32) 100) xs).size) :=
  decode_encode (.listFixed .uintN32 rfl (by decide)) xs

/-- Roundtrip for a general fixed-field container, three uintN
fields. The `BasicSupportedFieldsFixed` witness is a triple-nested
`.cons`. -/
example (vs : SSZType.interpFields [.uintN 8, .uintN 16, .uintN 32]) :
    SSZType.deserialize (.container [.uintN 8, .uintN 16, .uintN 32])
        (SSZType.serialize (.container [.uintN 8, .uintN 16, .uintN 32]) vs) =
      Except.ok (vs, (SSZType.serialize (.container [.uintN 8, .uintN 16, .uintN 32]) vs).size) :=
  decode_encode (.containerFixed
                  (.cons .uintN8 rfl
                    (.cons .uintN16 rfl
                      (.cons .uintN32 rfl .nil)))) vs

/-! ### Bit-shape arm examples

`BasicSupported` covers `.bitvector n` (`0 < n`) and
`.bitlist cap` through the bit-packing inverse in
`Proofs/BitPack.lean`. The widths exercise both decoder branches:
10 is not a byte multiple (the zero-padding guard runs on the
partial final byte), 16 is (the guard is skipped). -/

/-- Roundtrip for a 10-bit bitvector. The witness carries the
`0 < n` precondition, mirroring `vectorFixed`. -/
example (bv : BitVec 10) :
    SSZType.deserialize (.bitvector 10)
        (SSZType.serialize (.bitvector 10) bv) =
      Except.ok (bv, (SSZType.serialize (.bitvector 10) bv).size) :=
  decode_encode (.bitvector (by decide)) bv

/-- Roundtrip for a 16-bit (whole-byte) bitvector. -/
example (bv : BitVec 16) :
    SSZType.deserialize (.bitvector 16)
        (SSZType.serialize (.bitvector 16) bv) =
      Except.ok (bv, (SSZType.serialize (.bitvector 16) bv).size) :=
  decode_encode (.bitvector (by decide)) bv

/-- Roundtrip for a bitlist capped at 100 data bits. No side
condition: the delimiter bit makes every encoding non-empty,
including the empty bitlist's `0x01`. -/
example (xs : { bs : Array Bool // bs.size ≤ 100 }) :
    SSZType.deserialize (.bitlist 100)
        (SSZType.serialize (.bitlist 100) xs) =
      Except.ok (xs, (SSZType.serialize (.bitlist 100) xs).size) :=
  decode_encode .bitlist xs

/-- A container carrying a bitvector field: `.bitvector n` is
fixed-size, so it qualifies under `BasicSupportedFieldsFixed`
alongside the basic integers. -/
example (vs : SSZType.interpFields [.uintN 8, .bitvector 10]) :
    SSZType.deserialize (.container [.uintN 8, .bitvector 10])
        (SSZType.serialize (.container [.uintN 8, .bitvector 10]) vs) =
      Except.ok (vs, (SSZType.serialize (.container [.uintN 8, .bitvector 10]) vs).size) :=
  decode_encode (.containerFixed
                  (.cons .uintN8 rfl
                    (.cons (.bitvector (by decide)) rfl .nil))) vs

/-- A container carrying a `uint256` field alongside a `uint64`,
the `ExecutionPayload`-style layout that motivated the wide-integer
arms: `.uintN 256` is fixed-size, so it qualifies under
`BasicSupportedFieldsFixed`. -/
example (vs : SSZType.interpFields [.uintN 64, .uintN 256]) :
    SSZType.deserialize (.container [.uintN 64, .uintN 256])
        (SSZType.serialize (.container [.uintN 64, .uintN 256]) vs) =
      Except.ok (vs, (SSZType.serialize (.container [.uintN 64, .uintN 256]) vs).size) :=
  decode_encode (.containerFixed
                  (.cons .uintN64 rfl
                    (.cons .uintN256 rfl .nil))) vs

/-! ### Mixed-field container arm examples (`containerVar`)

`BasicSupported` also covers general `.container fs` with at
least one variable-size field, decoded through the offset-table
path (`Proofs/ContainerVar.lean`'s groundwork,
`Proofs/Roundtrip.lean`'s `decode_encode_containerVar_aux`). The
witness for `containerVar` is a `BasicSupportedFields fs` (every
field individually `BasicSupported`, fixed or not) plus
`allFixedSize fs = false` and `maxByteLengthFields fs < MAX_LENGTH`.

The four gates below exercise the shapes called out in the
groundwork plan: a variable field last, a variable field first, two
variable fields (so an earlier variable body's end feeds the next
field's `curOff`), and a concrete empty-list value where the
variable field's offset equals `bufEnd` exactly. -/

/-- Variable field last: `.list (.uintN 32) 100` follows a fixed
`.uintN 64`. -/
example (vs : SSZType.interpFields [.uintN 64, .list (.uintN 32) 100]) :
    SSZType.deserialize (.container [.uintN 64, .list (.uintN 32) 100])
        (SSZType.serialize (.container [.uintN 64, .list (.uintN 32) 100]) vs) =
      Except.ok (vs,
        (SSZType.serialize (.container [.uintN 64, .list (.uintN 32) 100]) vs).size) :=
  decode_encode (.containerVar
                  (.cons .uintN64
                    (.cons (.listFixed .uintN32 rfl (by decide)) .nil))
                  (by decide) (by decide)) vs

/-- Variable field first: `.bitlist 16` precedes a fixed `.uintN 8`,
so the fixed field's prefix bytes sit *after* the offset placeholder. -/
example (vs : SSZType.interpFields [.bitlist 16, .uintN 8]) :
    SSZType.deserialize (.container [.bitlist 16, .uintN 8])
        (SSZType.serialize (.container [.bitlist 16, .uintN 8]) vs) =
      Except.ok (vs, (SSZType.serialize (.container [.bitlist 16, .uintN 8]) vs).size) :=
  decode_encode (.containerVar
                  (.cons .bitlist (.cons .uintN8 .nil))
                  (by decide) (by decide)) vs

/-- Two variable fields, `.list (.uintN 8) 10` and `.bitlist 8`,
straddling a fixed `.bool`: the first variable body's end is the
second variable field's `curOff`, exercising the walker's
inter-body offset chaining rather than just a single offset. -/
example (vs : SSZType.interpFields [.list (.uintN 8) 10, .bool, .bitlist 8]) :
    SSZType.deserialize (.container [.list (.uintN 8) 10, .bool, .bitlist 8])
        (SSZType.serialize (.container [.list (.uintN 8) 10, .bool, .bitlist 8]) vs) =
      Except.ok (vs,
        (SSZType.serialize (.container [.list (.uintN 8) 10, .bool, .bitlist 8]) vs).size) :=
  decode_encode (.containerVar
                  (.cons (.listFixed .uintN8 rfl (by decide))
                    (.cons .bool (.cons .bitlist .nil)))
                  (by decide) (by decide)) vs

/-- Edge-case value for the empty-list gate below: the trailing
`.list (.uintN 32) 10` field serializes to an empty body, so its
offset equals `bufEnd` exactly, the smallest possible variable-field
slice `[off, off)` rather than a strict `curOff < nextOff` span. -/
private def emptyListContainer : SSZType.interpFields [.uintN 8, .list (.uintN 32) 10] :=
  (0, ⟨#[], by decide⟩, PUnit.unit)

/-- Roundtrip for the empty-list edge case: `deserializeVarFields`'s
`curOff > nextOff || nextOff > bufEnd` guard must accept
`curOff = nextOff = bufEnd`, not just `curOff < nextOff < bufEnd`. -/
example :
    SSZType.deserialize (.container [.uintN 8, .list (.uintN 32) 10])
        (SSZType.serialize (.container [.uintN 8, .list (.uintN 32) 10])
          emptyListContainer) =
      Except.ok (emptyListContainer,
        (SSZType.serialize (.container [.uintN 8, .list (.uintN 32) 10])
          emptyListContainer).size) :=
  decode_encode (.containerVar
                  (.cons .uintN8
                    (.cons (.listFixed .uintN32 rfl (by decide)) .nil))
                  (by decide) (by decide)) emptyListContainer

end SizzLeanTests.ReprExamples
