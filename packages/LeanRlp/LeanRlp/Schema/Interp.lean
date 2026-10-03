import LeanRlp.Schema.Type

/-!
# `LeanRlp.Schema.Interp`: the Lean type of a wire shape

`RlpType.interp` maps a schema to the Lean type its values live in:
`bytes` to `ByteArray`, `fixed n` to `Vector UInt8 n`, `nat` to
`Nat`, `uint bits` to `BitVec bits`, `bool` to `Bool`, `list t` to
`List t.interp`, `struct fs` to a right-nested product, `option t` to
`Option t.interp`, and `item` to `Item`.

The typed codec (`toItem`, `fromItem`) and its two theorems are
written once over this map, so a new arm in `RlpType` is one new case
in each function and one new proof case (OCP).

Filled in PLAN.md Stage 4.
-/

set_option autoImplicit false

namespace LeanRlp.Schema

end LeanRlp.Schema
