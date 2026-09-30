import LeanRlp.Schema.FromItem
import LeanRlp.Schema.ToItem
import LeanRlp.Spec.Decode
import LeanRlp.Spec.Encode

/-!
# `LeanRlp.Repr.Class`: the user surface

`RlpRepr` is the record codec class, six fields (ARCHITECTURE.md
§2.3): `shape : RlpType`, `toRepr`, `fromRepr`, the two isomorphism
laws, and `wellFormed : shape.WellFormed`. `WellFormed` is
decidable, the derived field closes by `decide`, and the schema
theorems read it from the class.

On top of the class sit the two entry points the execution layer
calls:

* `Rlp.encode x`: the bytes, through `shape` and `Spec.Encode`.
* `Rlp.decode b`: the value, through `Spec.Decode` and `fromItem`.

`Rlp.Error` joins `DecodeError` and `SchemaError` into the one
error type `Rlp.decode` reports. The hash of an encoding is
`Hasher.hash (Rlp.encode x)` on the consumer side, through the
shared `Hasher` class (planned for `EthCommon`); LeanRlp defines no
hash entry point (ARCHITECTURE.md §3).

Filled in PLAN.md Stage 5.
-/

set_option autoImplicit false

namespace LeanRlp

end LeanRlp
