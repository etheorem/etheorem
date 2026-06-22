import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving

/-!
# `SizzLeanTests.ExampleContainers`: minimal SSZ containers for testing

Small example containers used by `SizzLeanTests`'s cache-
machinery tests. The shapes mirror common consensus-spec
patterns (a flat 3-field struct, a nested struct with a sibling,
a struct with vector fields) but with no dependency on the real
Eth containers in `EthCLSpecs`.

This lets the SSZ library exercise `TreeBacked` coherence and
`sszUpdate` end-to-end *without* the consensus-spec types. Eth-
type-specific tests are in `EthCLSpecs`.

## Containers

* `FlatExample`: 3 fields (two byte-vectors plus a `UInt64`).
  Same shape as Phase-0 `Fork`: exercises the multi-field
  `sszUpdate` path (3 clauses, no nesting).
* `InnerExample` + `NestedExample`: a 5-field nested struct
  wrapped in a 2-field outer with a sibling vector. Same shape as
  `SignedBeaconBlockHeader`: exercises path composition across one
  nesting level plus a sibling flat clause.
* `BatchExample`: two `Vector Root 8` fields. Smaller mirror of
  `HistoricalBatch.Minimal`: exercises vector-index `sszUpdate`
  on a composite-element vector at non-trivial depth (depth 3).
-/

set_option autoImplicit false

namespace SizzLeanTests.ExampleContainers

open SizzLean
open SizzLean.Repr

/-- 32-byte root, mirroring `Eth.Primitives.Root`. -/
abbrev ExRoot : Type := Vector UInt8 32

/-- 4-byte version, mirroring `Eth.Primitives.Version`. -/
abbrev ExVersion : Type := Vector UInt8 4

/-- Flat 3-field container, shape mirrors `Phase0.Fork`.
Exercises multi-clause `sszUpdate` with no nesting. -/
structure FlatExample where
  versionA : ExVersion
  versionB : ExVersion
  marker   : UInt64
deriving Inhabited, DecidableEq, SSZRepr

/-- 5-field inner container, shape mirrors
`Phase0.BeaconBlockHeader`. Used inside `NestedExample`. -/
structure InnerExample where
  slot       : UInt64
  marker     : UInt64
  rootA      : ExRoot
  rootB      : ExRoot
  rootC      : ExRoot
deriving Inhabited, DecidableEq, SSZRepr

/-- Nested container, outer with one inner-struct field and one
sibling primitive-vector field. Shape mirrors
`Phase0.SignedBeaconBlockHeader`. Exercises path composition
across one nesting level plus a sibling flat clause. -/
structure NestedExample where
  message   : InnerExample
  signature : Vector UInt8 96
deriving Inhabited, DecidableEq, SSZRepr

/-- 2-field container of composite-element vectors, shape mirrors
`Phase0.HistoricalBatch.Minimal` but with 8 entries per vector
(versus 64) to keep test-time native_decide fast while still
exercising depth-3 vector geometry. -/
structure BatchExample where
  rootsA : Vector ExRoot 8
  rootsB : Vector ExRoot 8
deriving Inhabited, DecidableEq, SSZRepr

/-- 2-field container holding a composite-element `SSZList`.
Used to exercise list-shrink scenarios, writes referencing an
index that becomes out-of-bounds after a later whole-list
replacement. `cap = 8` keeps `native_decide` fast. -/
structure ListShrinkExample where
  vals   : SSZList ExRoot 8
  marker : UInt64
deriving DecidableEq, SSZRepr

/-- A composite element with a deliberately **non-zero** `Inhabited`
default. Used to expose the bare-OOB-index fragility, the test
needs an element type whose `default` does *not* match the
zero-padding the spec uses for under-capped SSZList positions. -/
structure NonZeroElem where
  a : UInt64
  b : UInt64
deriving DecidableEq, SSZRepr

/-- Non-zero `Inhabited` default. `default NonZeroElem` is
`{ a := 1, b := 1 }`, distinct from the all-zero
`NonZeroElem` that an under-capped SSZList position would
otherwise resolve to via zero-padding. -/
instance : Inhabited NonZeroElem := ⟨{ a := 1, b := 1 }⟩

/-- Container with an SSZList of the non-zero-default element.
The bare-OOB index write fragility manifests here because
`default NonZeroElem` produces a non-zero merkle subtree, which
diverges from the spec's zero-padding at OOB positions. -/
structure NonZeroListExample where
  vals   : SSZList NonZeroElem 8
  marker : UInt64
deriving DecidableEq, SSZRepr

end SizzLeanTests.ExampleContainers
