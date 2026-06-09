import LeanPoseidon

/-!
# `LeanPoseidonTests.Ffi`: `@[extern]` bindings to the Rust `zkhash` oracle

The differential conformance test (`Differential.lean`) needs a *trusted*
external Poseidon2 to compare against. That oracle is the HorizenLabs
`zkhash` crate, vendored under `rust-oracle/` and linked as a static
library (see `../lakefile.lean`). This file is the Lean ↔ Rust boundary.

## The Lean idioms here

* `@[extern "sym"] opaque f : T` declares `f : T` whose *runtime*
  implementation is the named C symbol, while the *kernel* treats `f` as
  fully opaque (no reduction, no defeq with anything). Exactly what we want
  for an FFI primitive that must never enter a proof term, and indeed this
  oracle never does: it backs the differential *executable* only.
* `@&` marks the argument *borrowed*, Lean passes it without bumping the
  refcount; the Rust side receives it as a `b_lean_obj_arg` and only reads.

## The ABI

Field elements are marshalled as fixed 32-byte **big-endian** buffers via
`Bn254Fr.toBytes` / `Bn254Fr.ofBytes?` (the single canonical codec, pinned
big-endian; see `LeanPoseidon.Field`). `ffiPermuteRaw` takes a 96-byte
`ByteArray` (3 field elements) and returns a 96-byte `ByteArray` (the
permuted state). The wrapper `ffiPermute` lifts that to `Vector Bn254Fr 3`, so
the differential test compares like with like. Because the wrapper round-
trips through `Bn254Fr.toBytes` / `Bn254Fr.ofBytes?`, a successful differential run
*also* confirms the byte-codec endianness agrees with the reference.
-/

set_option autoImplicit false

namespace LeanPoseidonTests

open LeanPoseidon

/-- Raw FFI permutation (BN254 t=3): 96-byte big-endian input `ByteArray`
(3 field elements) → 96-byte big-endian output. Runtime implementation is
`csrc/poseidon_shim.c`'s `lean_poseidon2_bn254_permute` over the Rust oracle. -/
@[extern "lean_poseidon2_bn254_permute"]
opaque ffiPermuteRaw (input : @& ByteArray) : ByteArray

/-- Raw FFI permutation (BLS12-381 t=3), same 96-byte ABI, second field. -/
@[extern "lean_poseidon2_bls12_t3_permute"]
opaque ffiPermuteRawBls12 (input : @& ByteArray) : ByteArray

/-- Pack a width-3 `Fp p` state to 96 big-endian bytes, call the given raw
oracle entrypoint, and unpack. Generic over the field (the only per-field
piece is which raw entrypoint is passed), mirroring the Lean side's field
abstraction. `get!` **panics** on a decode failure rather than defaulting.
The oracle always returns canonical residues (`< p`), so a `none` here would
mean a broken ABI/codec, exactly the defect this harness should surface
loudly, not absorb. -/
def ffiPermuteWith {p : Nat} [NeZero p]
    (raw : ByteArray → ByteArray) (st : Vector (Fp p) 3) : Vector (Fp p) 3 :=
  let input := st[0].toBytes ++ st[1].toBytes ++ st[2].toBytes
  let out := raw input
  Vector.ofFn (fun i =>
    (Fp.ofBytes? (out.extract (i.val * 32) (i.val * 32 + 32))).get!)

/-- The BN254 t=3 oracle permutation on a width-3 state. -/
def ffiPermute (st : Vector Bn254Fr 3) : Vector Bn254Fr 3 := ffiPermuteWith ffiPermuteRaw st

/-- The BLS12-381 t=3 oracle permutation on a width-3 state. -/
def ffiPermuteBls12 (st : Vector Bls12Fr 3) : Vector Bls12Fr 3 := ffiPermuteWith ffiPermuteRawBls12 st

end LeanPoseidonTests
