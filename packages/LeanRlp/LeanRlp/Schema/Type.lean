/-!
# `LeanRlp.Schema.Type`: the schema universe

`RlpType` describes a wire shape, in the manner of SizzLean's
`SSZType`. The nine arms cover the field kinds the execution specs
use (ARCHITECTURE.md §2.2): `bytes`, `fixed n`, `nat`, `uint bits`,
`bool`, `list t`, `struct fs`, `option t`, and `item` for an untyped
subtree.

Scalar rules (ARCHITECTURE.md §2.2): zero is the empty string, a
leading zero byte is `leadingZero`, and a `uint bits` value of
`2^bits` or more is `overflow`.

`RlpType.WellFormed` states the one soundness condition the universe
needs: `option t` is sound only when `t` never encodes to the empty
string. Theorem 5 takes it as a hypothesis, and the `RlpRepr` class
carries it as a field, so callers read it from the instance.

Filled in PLAN.md Stage 4.
-/

set_option autoImplicit false

namespace LeanRlp.Schema

/-- A wire shape. `interp` in `Schema.Interp` gives its Lean type. -/
inductive RlpType where
  | bytes                          -- any byte string
  | fixed (n : Nat)                -- exactly n bytes
  | nat                            -- scalar, no bound
  | uint (bits : Nat)              -- scalar below 2^bits
  | bool                           -- empty string or 0x01
  | list (t : RlpType)             -- homogeneous list
  | struct (fields : List RlpType) -- positional list
  | option (t : RlpType)           -- empty string, or t
  | item                           -- an untyped subtree

end LeanRlp.Schema
