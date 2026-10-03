/-!
# `LeanHazmatBlake2f.Ffi`: the BLAKE2b `F` compression behind `@[extern]`

One `@[extern] opaque` declaration bridges Lean to the C shim in
`csrc/blake2f_shim.c`: the rounds-parametrized BLAKE2b `F` compression
function, the raw primitive behind the Ethereum execution-layer
BLAKE2f precompile (EIP-152).

This module deliberately holds **only** the FFI binding. Composition
into the precompile (the 213-byte input parse `rounds ‖ h ‖ m ‖ t0 ‖
t1 ‖ f`, the gas schedule, and the failure behaviour: EIP-152 reverts
on malformed input) is the consumer's concern, per the LeanHazmat "raw
primitives, not assembled precompiles" rule (packages/hazmat/docs/ARCHITECTURE.md §4).
This binding's own failure surface is the empty `ByteArray` on a wrong
`h` / `m` length.

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatBlake2f`); the
declaration lives under the *brand* namespace `LeanHazmat.Blake2f`.
The two are decoupled exactly as SizzLean decouples the file path
`SizzLean/Hasher/Sha256.lean` from its `SizzLean.Hasher` namespace
(ARCHITECTURE.md §3.3).

## Trust boundary (ARCHITECTURE.md §10)

`opaque` keeps the kernel from attempting to reduce the compression
during proof checking; `@[extern]` instructs the compiler to emit a
direct call to the named C symbol at runtime. Unlike every other
LeanHazmat family, this one has **no third-party library** behind it:
EIP-152 needs raw `F` (arbitrary `rounds`, the final-block flag), which
no standard BLAKE2 library exposes, and the function is small enough
(RFC 7693 sections 3.1-3.2, ~60 lines) to hold in-repo. The empirical trust
assumption, *that `csrc/blake2f_shim.c` implements RFC 7693's `F`
correctly*, is validated only by the official EIP-152 test vectors in
`LeanHazmatBlake2fTests/`, and is the single line item this family
contributes to the TCB.

## Lean idioms used here

* `@[extern "C-symbol"] opaque foo : T`: declare `foo : T` such that
  the *runtime* implementation is the named C symbol, while the
  *kernel* treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else). Exactly what an FFI
  primitive we don't want to reduce inside proofs needs.
* `@&` on a function argument marks it as *borrowed*. Lean's runtime
  does not bump the refcount when passing it in. The C side receives
  a `b_lean_obj_arg` for these. `UInt32` / `UInt64` / `Bool`
  arguments lower to plain `uint32_t` / `uint64_t` / `uint8_t`
  parameters, no boxing.
-/

set_option autoImplicit false

namespace LeanHazmat.Blake2f

/-- The BLAKE2b `F` compression function (RFC 7693 section 3.2), the
primitive behind the execution-layer BLAKE2f precompile (EIP-152).

`h` is the 64-byte chaining state, `m` the 128-byte message block
(both read as little-endian `u64` words), `t0` / `t1` the 128-bit
offset counter, `last` the final-block flag, and `rounds` the number
of rounds (the ten-round sigma schedule cycles, so any count is
valid). The result is the updated 64-byte state after `rounds` rounds
and the XOR feed-forward. Empty `ByteArray` if `h` is not 64 bytes or
`m` is not 128 bytes.

The EIP-152 precompile input is exactly
`rounds(4, big-endian) ‖ h ‖ m ‖ t0(8, little-endian) ‖ t1(8,
little-endian) ‖ f(1)`; splitting it and decoding the fields stays
with the caller.

**Trust assumption:** the in-repo `csrc/blake2f_shim.c` implements
RFC 7693's `F` correctly. No third-party library is involved;
validated by the official EIP-152 vectors in
`LeanHazmatBlake2fTests/Vectors.lean` (rounds 0, 1, 12, and
`0xffffffff`, both `f` values). -/
@[extern "lean_hazmat_blake2f_compress"]
opaque blake2fCompress (rounds : UInt32) (h : @& ByteArray)
    (m : @& ByteArray) (t0 t1 : UInt64) (last : Bool) : ByteArray

end LeanHazmat.Blake2f
