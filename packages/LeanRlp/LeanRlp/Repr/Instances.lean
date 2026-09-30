import LeanRlp.Repr.Class

/-!
# `LeanRlp.Repr.Instances`: `RlpRepr` for the standard library

One instance per type the execution specs name as a field
(ARCHITECTURE.md §2.3): `ByteArray`, `Vector UInt8 n`, `Nat`, `UInt8` to
`UInt64`, `BitVec n`, `Bool`, `List α`, `Array α`, `Option α`,
`Item`, and products.

The product instance flattens, so
`Rlp.encode (chainId, address, nonce)` is the three-item list the
EIP-7702 message needs. The signing hashes and the CREATE address
use it and declare no structure.

A consumer adds an instance for its own `U256` or `Address` in its
own package. LeanRlp never names an execution-layer type.

Filled in PLAN.md Stage 5.
-/

set_option autoImplicit false

namespace LeanRlp

end LeanRlp
