import LeanRlpTests.Known

/-!
# `LeanRlpTests`: gates for the RLP codec

The test library, a separate `lean_lib` from `LeanRlp` so the main
build stays fast, in the pattern of `LeanSha256Tests`. Three kinds of
gate land here, one per plan stage:

* Known answers: `LeanRlpTests.Known` holds the examples from the
  RLP specification, and the five item-layer inputs of
  ARCHITECTURE.md §7, each expected to fail with its
  `DecodeError` constructor. The scalar-layer row of that table is a
  Stage 4 gate, with its own `SchemaError`.
* RLPTests fixtures (Stage 2): the `rlp_vectors` runner reads the
  three `ethereum/tests` files at a pinned tag.
* Real shapes (Stage 6): fixture blocks round-trip, and test
  structures with the Amsterdam field lists meet the Python oracle.

Build with `lake build LeanRlpTests` or `just rlp-test`.
-/

set_option autoImplicit false
