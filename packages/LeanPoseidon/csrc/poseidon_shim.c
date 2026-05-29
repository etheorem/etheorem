// Lean ↔ Rust ABI shim for the Poseidon2 conformance oracle.
//
// The pure-Lean `LeanPoseidonTests.Ffi.ffiPermuteRaw` is declared
// `@[extern "lean_poseidon2_bn254_permute"]`; Lean calls this C symbol
// with a borrowed `ByteArray` and expects an owned `ByteArray` back. The
// field math lives in the vendored Rust `zkhash` oracle, reached through
// the raw-pointer entrypoint `poseidon_oracle_permute_be`.
//
// This shim exists (rather than a pure-Rust `@[extern]` function) because
// Lean's `ByteArray` accessors — `lean_alloc_sarray`, `lean_sarray_cptr` —
// are `static inline` in `lean.h` and thus not linkable symbols a Rust
// `extern "C"` block could reference. The C compiler inlines them here.
// Mirrors `SizzLean`'s `csrc/sha256_shim.c`; the difference is the heavy
// lifting is in a cargo-built Rust archive, not hand-written C.

#include <lean/lean.h>
#include <stdint.h>

// Implemented in rust-oracle/src/lib.rs (linked from libposeidon_oracle.a):
// each reads 96 big-endian input bytes and writes the 96-byte permuted state
// for the corresponding field's t=3 Poseidon2 instance.
extern void poseidon_oracle_permute_be(const uint8_t *in_ptr, uint8_t *out_ptr);
extern void poseidon_oracle_bls12_t3_permute_be(const uint8_t *in_ptr, uint8_t *out_ptr);

// 96-byte (3 × 32, big-endian) input ByteArray → 96-byte output ByteArray.
// `input` is borrowed (Lean `@&`); the returned array is freshly owned.
LEAN_EXPORT lean_obj_res lean_poseidon2_bn254_permute(b_lean_obj_arg input) {
    lean_object *out = lean_alloc_sarray(/* elem_size */ 1, /* size */ 96, /* capacity */ 96);
    poseidon_oracle_permute_be(lean_sarray_cptr(input), lean_sarray_cptr(out));
    return out;
}

// Same ABI, BLS12-381 t=3 instance.
LEAN_EXPORT lean_obj_res lean_poseidon2_bls12_t3_permute(b_lean_obj_arg input) {
    lean_object *out = lean_alloc_sarray(/* elem_size */ 1, /* size */ 96, /* capacity */ 96);
    poseidon_oracle_bls12_t3_permute_be(lean_sarray_cptr(input), lean_sarray_cptr(out));
    return out;
}
