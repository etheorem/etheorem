//! Poseidon2 BN254 (t=3) conformance oracle — a thin `extern "C"` wrapper
//! over HorizenLabs `zkhash`, used only for differential testing against
//! the pure-Lean `LeanPoseidon` implementation. Never on the shipped path.
//!
//! ## ABI
//!
//! Field elements are marshalled as fixed 32-byte **big-endian** buffers
//! (matching `LeanPoseidon.Fp.toBytes` / `ofBytes?`, pinned big-endian via
//! ark-ff's `from_be_bytes_mod_order` / `to_bytes_be`). The entrypoint
//! `poseidon_oracle_permute_be` reads 96 input bytes (3 field elements)
//! and writes 96 output bytes (the permuted state) through raw pointers.
//!
//! This crate deliberately knows **nothing** about Lean's object ABI: the
//! `lean_object`/`ByteArray` marshalling lives in the small C shim
//! `csrc/poseidon_shim.c`, which can use `lean.h`'s `static inline`
//! `ByteArray` accessors (`lean_alloc_sarray`, `lean_sarray_cptr`) — those
//! are not linkable symbols, so a pure-Rust shim cannot call them. The C
//! shim calls the raw `permute_be` function exported here.

use std::sync::Arc;
use zkhash::ark_ff::{BigInteger, PrimeField};
use zkhash::poseidon2::poseidon2::Poseidon2;
use zkhash::poseidon2::poseidon2_instance_bls12::POSEIDON2_BLS_3_PARAMS;
use zkhash::poseidon2::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS;
use zkhash::poseidon2::poseidon2_params::Poseidon2Params;

/// Permutation over big-endian 96-byte buffers (3 × 32), generic over the
/// prime field `G` and its `t = 3` Poseidon2 params — so a new field is a
/// new call site, not new code (mirroring the Lean side's field
/// abstraction). 96 bytes suit any field with `r < 2²⁵⁶` (BN254, BLS12-381,
/// …); `to_bytes_be` output is right-aligned into each 32-byte slot.
fn permute_be_with<G: PrimeField>(params: &Arc<Poseidon2Params<G>>, input: &[u8; 96]) -> [u8; 96] {
    let read = |i: usize| G::from_be_bytes_mod_order(&input[i * 32..i * 32 + 32]);
    let state = [read(0), read(1), read(2)];
    let out = Poseidon2::new(params).permutation(&state);
    let mut buf = [0u8; 96];
    for k in 0..3 {
        let be = out[k].into_bigint().to_bytes_be();
        buf[k * 32 + (32 - be.len())..(k + 1) * 32].copy_from_slice(&be);
    }
    buf
}

/// BN254 t=3 — the shipped default. Testable without any FFI runtime.
pub fn permute_be(input: &[u8; 96]) -> [u8; 96] {
    permute_be_with(&POSEIDON2_BN256_PARAMS, input)
}

/// Raw C ABI entrypoint (BN254 t=3): read 96 big-endian bytes from `in_ptr`,
/// write the 96-byte permuted state to `out_ptr` (caller-allocated). Called
/// by the C shim `lean_poseidon2_bn254_permute`.
///
/// # Safety
/// `in_ptr` and `out_ptr` must each point to at least 96 valid bytes.
#[no_mangle]
pub unsafe extern "C" fn poseidon_oracle_permute_be(in_ptr: *const u8, out_ptr: *mut u8) {
    let mut input = [0u8; 96];
    core::ptr::copy_nonoverlapping(in_ptr, input.as_mut_ptr(), 96);
    let out = permute_be_with(&POSEIDON2_BN256_PARAMS, &input);
    core::ptr::copy_nonoverlapping(out.as_ptr(), out_ptr, 96);
}

/// Raw C ABI entrypoint (BLS12-381 t=3) — a second field, same 96-byte ABI
/// (BLS12-381 `Fr` is 255-bit). Called by `lean_poseidon2_bls12_t3_permute`.
///
/// # Safety
/// `in_ptr` and `out_ptr` must each point to at least 96 valid bytes.
#[no_mangle]
pub unsafe extern "C" fn poseidon_oracle_bls12_t3_permute_be(in_ptr: *const u8, out_ptr: *mut u8) {
    let mut input = [0u8; 96];
    core::ptr::copy_nonoverlapping(in_ptr, input.as_mut_ptr(), 96);
    let out = permute_be_with(&POSEIDON2_BLS_3_PARAMS, &input);
    core::ptr::copy_nonoverlapping(out.as_ptr(), out_ptr, 96);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn anchor_input() -> [u8; 96] {
        // state [0, 1, 2], big-endian.
        let mut input = [0u8; 96];
        input[63] = 1;
        input[95] = 2;
        input
    }
    fn hex0(out: &[u8; 96]) -> String {
        out[0..32].iter().map(|b| format!("{:02x}", b)).collect()
    }

    #[test]
    fn bn254_anchor() {
        assert_eq!(
            hex0(&permute_be_with(&POSEIDON2_BN256_PARAMS, &anchor_input())),
            "0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033"
        );
    }

    #[test]
    fn bls12_anchor() {
        assert_eq!(
            hex0(&permute_be_with(&POSEIDON2_BLS_3_PARAMS, &anchor_input())),
            "1b152349b1950b6a8ca75ee4407b6e26ca5cca5650534e56ef3fd45761fbf5f0"
        );
    }
}
