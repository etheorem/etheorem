import SizzLean.Proofs.Simp
import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.Interp

/-!
# `SizzLean.Proofs.SimpAttrs`: applying `@[ssz_simp]` to spec defs

Companion to `Proofs/Simp.lean` (which only registers the attribute).
This file imports the spec layer and bulk-applies `@[ssz_simp]` to
the encode/decode/interp definitions that proofs need to unfold.

## What we tag and what we don't

Tag the spec *definitions*, not individual equation lemmas. Lean
auto-generates an equation set per `def` and `attribute [ssz_simp]`
on the def name picks them all up. Tagged here:

* The serializer mutual block: `serialize`, `serializeFixedElems`,
  `serializeVarElemsAux`, `serializeFieldsAux`.
* The deserializer mutual block: `deserialize`,
  `deserializeFixedElems`, `deserializeFixedFields`.
* The container-fields `interp` helper `interpFields`. We tag this
  (not `interp` itself) so `simp [ssz_simp]` unfolds the `Prod` chain
  used by the container case. Without the unfold, `vs.1` / `vs.2`
  projections cannot reduce. `interp` stays out of the set: unfolding
  it eagerly across the universal `s : SSZType` would explode every
  case at once and fight the `let x' : ConcreteType := x` defeq
  coercion idiom we rely on for the basic-type arms.
* Layout helpers `isFixedSize`, `allFixedSize`, `fixedByteSize`:
  the Roundtrip proof's `if t.isFixedSize then ... else ...` arms
  need these to reduce when `Supported` supplies an
  `isFixedSize = true` witness.

Deliberately *not* tagged:

* `SSZType.interp` itself: see above.
* Private bit-packing helpers (`bitsToByte`, `packBitsLE`,
  `bitsToNat`, `msbPos`, `byteToBits`, `unpackBitsLEAux`,
  `bitvecToBytes`, `bitlistToBytes`, `deserializeBitvector`,
  `deserializeBitlist`, the LE primitive readers/writers). These
  reduce only inside dedicated round-trip lemmas (e.g.
  `packBitsLE_unpackBitsLE_inverse`); leaving them out of the
  global set prevents `simp` loops and keeps the search space
  small.

## Lean idiom

`attribute [<attr-name>] decl₁ decl₂ …` bulk-applies the attribute
`<attr-name>` to a list of already-declared names. Used here so the
attribute applications live in the proof layer rather than
cluttering the spec definitions with `@[ssz_simp]` markers, the
spec doesn't need to know which simp set its equations participate
in. -/

set_option autoImplicit false

namespace SizzLean.Spec

attribute [ssz_simp]
  SSZType.serialize
  SSZType.serializeFixedElems
  SSZType.serializeVarElemsAux
  SSZType.serializeFieldsAux
  SSZType.deserialize
  SSZType.deserializeFixedElems
  SSZType.deserializeFixedFields
  SSZType.interpFields
  SSZType.isFixedSize
  SSZType.allFixedSize
  SSZType.fixedByteSize

end SizzLean.Spec
