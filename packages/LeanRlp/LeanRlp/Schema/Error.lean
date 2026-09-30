/-!
# `LeanRlp.Schema.Error`: typed schema failures

`SchemaError` names the reason an `Item` does not fit a `RlpType`:
`expectedBytes`, `expectedList`, `wrongWidth expected actual`,
`leadingZero`, `overflow bits`, `badBool`, and `fieldCount expected
actual`. Each value sits under a path of field indices, so the
caller can say which field failed.

The two error layers stay apart: `DecodeError` speaks about bytes,
this type speaks about shapes. `EthELLib` maps both to EEST
exception names; LeanRlp knows no EEST name.

Filled in PLAN.md Stage 4.
-/

set_option autoImplicit false

namespace LeanRlp.Schema

end LeanRlp.Schema
