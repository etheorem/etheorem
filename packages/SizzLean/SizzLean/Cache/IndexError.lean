/-!
# `SizzLean.Cache.IndexError`: SSZ element-access failure

The sole failure mode of an *indexed* `sszGet` / `sszUpdate`
(`xs[i]`): the index is past the current length. This is the
SSZ-level surface of the pyspec's `IndexError`; the spec layer lifts
it into a block rejection.

It is deliberately its own one-constructor type rather than a tag on
`SizzLean.Spec.SSZError`: `SSZError` is the *decode* taxonomy
(`tooShort`, `invalidOffset`, …) and an element access at runtime is a
different concern, with exactly one way to fail.
-/

set_option autoImplicit false

namespace SizzLean.Cache

/-- The only way an index-form `sszGet`/`sszUpdate` can fail: the index
is out of range for the field's current length. Carries no payload,
there is a single failure mode. -/
inductive IndexError where
  | indexError
  deriving Repr, DecidableEq

end SizzLean.Cache
