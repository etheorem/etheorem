import LeanPoseidon.Poseidon2.Permutation

/-!
# `LeanPoseidon.Compress`: the 2-to-1 compression function

`compress (a, b)` is the fixed-width 2-to-1 primitive a binary Merkle
tree uses for an interior node: it seeds a width-3 state from `a`, `b`,
and a zero capacity slot, runs the permutation, and projects out element
0. This is exactly `zkhash`'s `MerkleTreeHash::compress` for the BN254
t=3 instance, `permutation([a, b, 0])[0]`, and is the reason the `t = 3`
width was chosen (rate-2 / 2-to-1).

It is the EIP-7864-shaped node primitive, the one piece of this library
with an unambiguous, externally-pinned definition (so its KATs below come
straight from `zkhash`). The sponge over arbitrary input lives in
`Sponge.lean`.
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

/-- 2-to-1 compression: `permute([left, right, 0])[0]`. The third state
slot (the *capacity*, held back from input) is initialised to `0` and the
single output element is projected from position 0, the `zkhash`
`MerkleTreeHash` convention. -/
def compress (left right : Bn254Fr) : Bn254Fr :=
  (permute bn254Params (#v[left, right, Bn254Fr.ofNat 0]))[0]

/-! ## KATs (from HorizenLabs `zkhash` v0.2.0, BN254 t=3)

Each is `permutation([a, b, 0])[0]` computed by the reference and checked
here via `native_decide`. `compress 0 0` also coincides with the
permutation anchor's `[0,0,0]` output, by construction. -/

example : compress (Bn254Fr.ofNat 0) (Bn254Fr.ofNat 0)
    = Bn254Fr.ofNat 0x2ed1da00b14d635bd35b88ab49390d5c13c90da7e9e3a5f1ea69cd87a0aa3e82 := by
  native_decide

example : compress (Bn254Fr.ofNat 1) (Bn254Fr.ofNat 2)
    = Bn254Fr.ofNat 0x2afac3bdc3663b71eefeecdf21b147d0ba7dd7a169a7757c05ed6bfb065bffd2 := by
  native_decide

example : compress (Bn254Fr.ofNat 3) (Bn254Fr.ofNat 4)
    = Bn254Fr.ofNat 0x0f2021db8d04204e74cec23e5bd3fe4562e2cac46ab33fe7310325c5b0d0b1eb := by
  native_decide

example : compress (Bn254Fr.ofNat 0xdeadbeef) (Bn254Fr.ofNat 0xcafe)
    = Bn254Fr.ofNat 0x25658bd09fc86ce1a2d80944427f8a055c135b2e06a216519261b684bc30912e := by
  native_decide

end LeanPoseidon.Poseidon2
