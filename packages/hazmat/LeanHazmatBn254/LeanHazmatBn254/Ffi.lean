/-!
# `LeanHazmatBn254.Ffi`: alt_bn128 (BN254) behind `@[extern]`

Seven `@[extern] opaque` declarations bridge Lean to the C++ shim in
`csrc/bn254_shim.cpp`, which wraps the vendored herumi/mcl for the
execution-layer alt_bn128 primitives:

* `g1Add` / `g1Mul`: the EIP-196 ECADD / ECMUL primitives.
* `g2Add` / `g2Mul`: their EIP-197 G2 counterparts.
* `millerLoopVec`: `prodᵢ millerLoop(g1ᵢ, g2ᵢ)` in GT, the batched
  pairing inner product.
* `finalExp`: the pairing's final exponentiation.
* `gtIsOne`: the pairing-check predicate.

The EIP-197 pairing check (0x08) composes these in the caller:
`gtIsOne (finalExp (millerLoopVec pairs))`. The input parse, the gas
schedule, and the `0x…01` output encoding are consumer concerns
(packages/hazmat/docs/ARCHITECTURE.md §4).

The composition has one caller duty: `millerLoopVec` answers the
empty `ByteArray` on any bad length or invalid point, and `gtIsOne`
collapses that sentinel to `false`. EIP-197 fails the precompile on
invalid input, so a caller must reject the empty result before
reading `gtIsOne`'s `Bool`; a bare `false` would otherwise report a
successful "product is not one" for input the EIP says must fail.

## Encodings

* Field elements and scalars: 32-byte big-endian; coordinates must be
  `< p` (rejected otherwise), scalars are reduced mod the group order
  (EIP-196 allows any 256-bit scalar).
* G1: 64 bytes `x ‖ y`; the point at infinity is all zeros (EIP-196).
* G2: 128 bytes `(xₐ ‖ x_b) ‖ (yₐ ‖ y_b)` where the coordinate is
  `x_b + xₐ·i`, the EIP-197 order (imaginary half first); the shim
  swaps into mcl's (real, imag) order.
* GT: 384 bytes, mcl's GT serialization (twelve 32-byte big-endian Fp
  coefficients). The encoding round-trips through this family's own
  functions, which is all a pairing-check consumer needs.
* G2 deserialization checks the order-r subgroup (EIP-197's
  membership rule); G1 needs only the curve equation (cofactor 1).

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatBn254`); the
declarations live under the *brand* namespace `LeanHazmat.Bn254`. The
two are decoupled exactly as SizzLean decouples the file path
`SizzLean/Hasher/Sha256.lean` from its `SizzLean.Hasher` namespace
(ARCHITECTURE.md §3.3).

## Trust boundary (ARCHITECTURE.md §10)

No pure-Lean reference exists for BN254 pairing computation; each
binding is an opaque `@[extern]` boundary. The empirical trust
assumption, *that the vendored herumi/mcl (v4.10) implements the
alt_bn128 curve and its optimal ate pairing correctly*, is validated
only against the published EIP-196/197 vectors in
`LeanHazmatBn254Tests/` (generated from `ethereum/py_ecc`, the
implementation EIP-197 itself references).

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

namespace LeanHazmat.Bn254

/-- EIP-196 ECADD: add two G1 points (64 bytes `x ‖ y` each,
infinity = all zeros). Empty `ByteArray` on a bad length or an
invalid (off-curve, out-of-range) point.

**Trust assumption:** the vendored mcl (v4.10) computes alt_bn128 G1
addition correctly. Validated by `LeanHazmatBn254Tests/Vectors.lean`. -/
@[extern "lean_hazmat_bn254_g1_add"]
opaque g1Add (a : @& ByteArray) (b : @& ByteArray) : ByteArray

/-- EIP-196 ECMUL: scalar-multiply a G1 point by a 32-byte big-endian
scalar, reduced mod the group order (any 256-bit value is legal per
the EIP). Empty `ByteArray` on a bad length or an invalid point.

**Trust assumption:** same library as `g1Add`. Validated by
`LeanHazmatBn254Tests/Vectors.lean`. -/
@[extern "lean_hazmat_bn254_g1_mul"]
opaque g1Mul (a : @& ByteArray) (k : @& ByteArray) : ByteArray

/-- EIP-197 G2 addition (128-byte points, EIP-197 encoding, subgroup
membership enforced). Empty `ByteArray` on bad input.

**Trust assumption:** same library as `g1Add`. Validated by
`LeanHazmatBn254Tests/Vectors.lean`. -/
@[extern "lean_hazmat_bn254_g2_add"]
opaque g2Add (a : @& ByteArray) (b : @& ByteArray) : ByteArray

/-- EIP-197 G2 scalar multiplication. Empty `ByteArray` on bad input.

**Trust assumption:** same library as `g1Add`. Validated by
`LeanHazmatBn254Tests/Vectors.lean`. -/
@[extern "lean_hazmat_bn254_g2_mul"]
opaque g2Mul (a : @& ByteArray) (k : @& ByteArray) : ByteArray

/-- The pairing inner product `prodᵢ e'(g1ᵢ, g2ᵢ)` (the miller-loop
product, *without* the final exponentiation), in mcl's GT
serialization (384 bytes, twelve 32-byte big-endian Fp coefficients).
The two arrays share one length; the empty pair set answers the GT
identity, so the EIP-197 empty-input rule composes naturally.
Empty `ByteArray` on any bad length or invalid point, including a
point rejected midway through the array. A pairing-check caller must
reject the empty result before `gtIsOne` reads a `Bool` from it (see
the module note).

**Trust assumption:** same library as `g1Add`. Validated by the
pairing cases in `LeanHazmatBn254Tests/Vectors.lean`. -/
@[extern "lean_hazmat_bn254_miller_loop_vec"]
opaque millerLoopVec (g1s : @& Array ByteArray)
    (g2s : @& Array ByteArray) : ByteArray

/-- The pairing's final exponentiation (GT → GT), on mcl's GT
serialization. Any 384-byte input of in-range Fp coefficients decodes
to some Fp12 element; it need not be a GT element (the codomain
restriction is the caller's composition to enforce). Empty
`ByteArray` on a bad length.

**Trust assumption:** same library as `g1Add`. Validated by the
pairing cases in `LeanHazmatBn254Tests/Vectors.lean`. -/
@[extern "lean_hazmat_bn254_final_exp"]
opaque finalExp (gt : @& ByteArray) : ByteArray

/-- Is this GT element one? The EIP-197 pairing check is
`gtIsOne (finalExp (millerLoopVec pairs))`. `Bool` has no error
channel, so `false` covers both "not one" and a malformed input,
including the empty `ByteArray` an earlier stage returns on rejected
input. EIP-197 fails the precompile on invalid input, so a
pairing-check caller must reject the empty result first; a bare
`false` otherwise reads as a successful "product is not one" (see
the module note).

**Trust assumption:** same library as `g1Add`. Validated by the
pairing cases in `LeanHazmatBn254Tests/Vectors.lean`. -/
@[extern "lean_hazmat_bn254_gt_is_one"]
opaque gtIsOne (gt : @& ByteArray) : Bool

end LeanHazmat.Bn254
