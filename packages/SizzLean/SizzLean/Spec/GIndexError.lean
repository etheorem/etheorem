/-!
# `SizzLean.Spec.GIndexError`: generalized-index path failure

The error carrier `get_generalized_index` returns. A path fails when it does not
address a node of the shape it is read against.

Its own type, not tags on `SizzLean.Spec.SSZError`, for the reason
`SizzLean.Cache.IndexError` states: `SSZError` is the decode taxonomy, and no
decoder produces any tag below.
-/

set_option autoImplicit false

namespace SizzLean.Spec

/-- The ways an access path fails against a shape.

* `basicTypeDescent`: a step continued past a basic type, which has no children.
  Mirrors `assert not issubclass(typ, BasicValue)`, checked before every step
  (`ssz/merkle-proofs.md:178`).
* `lengthOnNonList`: a `.length` step addressed a shape with no length mix-in
  node. Mirrors `assert issubclass(typ, (List, ByteList))`
  (`ssz/merkle-proofs.md:180`).
* `indexOutOfRange`: a `.field k` step named a position the shape does not hold.
  That is a field index past the field list, or an element past a vector's length
  or a list's capacity. Mirrors the `KeyError` each composite
  `key_to_static_gindex` raises (remerkleable `complex.py`, `bitfields.py`). The
  prose spec refuses a container the same way, since there a step is a field name
  and an absent name has no index. -/
inductive GIndexError where
  | basicTypeDescent : GIndexError
  | lengthOnNonList  : GIndexError
  | indexOutOfRange  : GIndexError
  deriving Repr, DecidableEq

end SizzLean.Spec
