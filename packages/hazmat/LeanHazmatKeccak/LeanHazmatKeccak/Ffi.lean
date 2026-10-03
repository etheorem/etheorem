/-!
# `LeanHazmatKeccak.Ffi`: Keccak-256 behind `@[extern]`

One `@[extern] opaque` declaration bridges Lean to the C shim in
`csrc/keccak_shim.c`: Keccak-256, the execution layer's most-used hash
(the `KECCAK256` opcode, address derivation, storage slots, the MPT
trie, RLP hashing).

This module deliberately holds **only** the FFI binding. Composition
(address derivation = `keccak256(pubkey)[12:]`, precompile output
encoding) is the consumer's concern, per the LeanHazmat "raw
primitives, not assembled precompiles" rule
(packages/hazmat/docs/ARCHITECTURE.md §4).

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatKeccak`); the
declaration lives under the *brand* namespace `LeanHazmat.Keccak`. The
two are decoupled exactly as SizzLean decouples the file path
`SizzLean/Hasher/Sha256.lean` from its `SizzLean.Hasher` namespace
(ARCHITECTURE.md §3.3).

## Keccak-256, not SHA3-256

Ethereum's digest uses the **original Keccak padding** (`0x01`), not
FIPS 202's `0x06`. The two functions differ on every input, so no
SHA3 implementation substitutes for this one (the reason the plan
rejects OpenSSL SHA3). The vendored keccak-tiny implements the
Keccak-f[1600] permutation and a delimiter-parametrized sponge; the
shim calls the sponge with rate 136 and delimiter `0x01`.

## Trust boundary (ARCHITECTURE.md §10)

No pure-Lean reference exists for Keccak-256; the binding is an opaque
`@[extern]` boundary. The empirical trust assumption, *that the
vendored keccak-tiny (rev `64b66475…`) implements Keccak-f[1600] and
the sponge correctly, and that the shim selects the 0x01 padding*, is
validated only against the published vectors in
`LeanHazmatKeccakTests/`, including the EVM's canonical constants
(the empty-input digest `c5d246…a470` and the empty trie root
`56e81f…b421`).

## Lean idioms used here

* `@[extern "C-symbol"] opaque foo : T`: declare `foo : T` such that
  the *runtime* implementation is the named C symbol, while the
  *kernel* treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else). Exactly what an FFI
  primitive we don't want to reduce inside proofs needs.
* `@&` on a function argument marks it as *borrowed*. Lean's runtime
  does not bump the refcount when passing it in. The C side receives
  a `b_lean_obj_arg` for these.
-/

set_option autoImplicit false

namespace LeanHazmat.Keccak

/-- 32-byte Keccak-256 digest of an arbitrary-length input (rate 136,
original Keccak `0x01` padding). Runtime implementation is
`csrc/keccak_shim.c`'s `lean_hazmat_keccak256_hash`, which drives the
vendored keccak-tiny sponge.

This is the EVM's hash function, **not** SHA3-256 (different padding,
so a different function on every input).

**Trust assumption:** the vendored coruus/keccak-tiny (rev
`64b66475…`) implements Keccak-f[1600] and the sponge correctly.
Validated by the published vectors in
`LeanHazmatKeccakTests/Vectors.lean`. -/
@[extern "lean_hazmat_keccak256_hash"]
opaque keccak256 (input : @& ByteArray) : ByteArray

end LeanHazmat.Keccak
