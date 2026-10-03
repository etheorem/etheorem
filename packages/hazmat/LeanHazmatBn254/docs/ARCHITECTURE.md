# LeanHazmatBn254: Architecture

The single-family trust-boundary record for `LeanHazmatBn254`. The
cross-family view is
[`../../docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md);
this file records *this* family's library, pin, and, the reason this
family needed its own stage, the C++ build shape.

## What this package is

Raw alt_bn128 primitives in namespace `LeanHazmat.Bn254`:

| Primitive | C symbol |
| --- | --- |
| `g1Add` / `g1Mul` | `lean_hazmat_bn254_g1_add` / `…_g1_mul` |
| `g2Add` / `g2Mul` | `lean_hazmat_bn254_g2_add` / `…_g2_mul` |
| `millerLoopVec` | `lean_hazmat_bn254_miller_loop_vec` |
| `finalExp` | `lean_hazmat_bn254_final_exp` |
| `gtIsOne` | `lean_hazmat_bn254_gt_is_one` |

The EIP-197 pairing check composes in the caller:
`gtIsOne (finalExp (millerLoopVec pairs))`. Input parse, gas, and the
`0x…01` output encoding stay with the consumer. Validation semantics at
the boundary: coordinates ≥ p and off-curve points are rejected;
G2 additionally checks the order-r subgroup (`mclBn_verifyOrderG2(1)`,
pinned by the init-once), which is EIP-197's membership rule; scalars are
reduced mod the group order (EIP-196 allows any 256-bit value).

## Backend & pin

**herumi/mcl**, tag **`v4.10`**, vendored (`just hazmat-bn254-vendor`).

## Build shape

* **One translation unit.** mcl's whole `mclBn*` C API comes out of
  `src/fp.cpp` at the 256-bit instantiation (`-DMCL_FP_BIT=256
  -DMCL_FR_BIT=256`, no GMP); `src/bn_c256.cpp` in the tree is an empty
  placeholder. Upstream's `sample/eip-196.cpp` is the reference for the
  EL-encoding conversion this shim implements.
* **Portable bignum.** `-DMCL_BINT_ASM=0`: upstream's default bignum
  primitives need x64 assembly or LLVM-IR objects; the generic C path
  keeps the archive portable and dependency-free. `-DMCL_DONT_USE_XBYAK`
  skips upstream's JIT-assembler path for the same reason.
* **The C++ runtime is compiled out.** mcl's compiled code would
  reference the libstdc++ ABI (std::string, hash-map internals,
  iostream's static init, operator new), and link args do not
  propagate across `require` (PLAN.md Stage 0), so a consumer flag was
  never viable. The build therefore switches the runtime off at the
  source level: `-fno-exceptions -fno-rtti -fno-threadsafe-statics`
  plus `-DCYBOZU_DONT_USE_EXCEPTION -DCYBOZU_DONT_USE_STRING
  -DMCL_DONT_USE_CSPRNG -DMCL_DONT_USE_XBYAK`. Under those flags the
  compiled code references only libc and libgcc (`nm -u` verified at
  design time): no operator new, no iostream, no exception machinery,
  no libstdc++ / libc++ anywhere. mcl's error paths, which would
  throw, become aborts through the CYBOZU mapping; they fire only on
  internal errors (allocation failure, malformed internal state),
  never on the inputs this surface accepts.
* The shim is `.cpp` with `extern "C"` `LEAN_EXPORT` entry points; the
  `mclBn_init` guard is `pthread_once` (exactly one caller
  initializes from any thread; every other one waits). After init the
  shim pins `mclBn_verifyOrderG1(0)` / `mclBn_verifyOrderG2(1)`, never
  left to a library default: BN254 G1 has cofactor 1, so the on-curve
  check already proves membership and an order check would add a
  scalar multiplication by r to every G1 read for no gain, while the
  EIP-197 G2 membership rule needs the subgroup check.

## Trust boundary

No pure-Lean reference exists; each binding is an opaque `@[extern]`
boundary. The empirical trust assumption is *that the vendored mcl
implements the alt_bn128 curve and its optimal ate pairing correctly*,
validated only by `LeanHazmatBn254Tests`, whose ground truth is
**ethereum/py_ecc** (the implementation EIP-197 itself links):

* **Point arithmetic anchors**: G1 and G2 doubling, addition, scalar
  multiplication (small, `(q-1)`, and zero → infinity), and
  infinity-absorbing additions.
* **Pairing checks**: the two-pair case whose discrete-log sum
  vanishes (`2·3 + 3·(q-2) = 3q ≡ 0 mod q`) passes; a non-vanishing
  one fails; the empty pair set is one (the EIP-197 empty-input rule);
  the infinity pair is trivially true; a non-degenerate single pairing
  is not one.
* **Negatives**: an off-curve G1 point, a G2 point outside the
  order-r subgroup, and a length mismatch yield the
  empty `ByteArray`.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for an FFI KAT.

Note on the two orders: py_ecc's FQ2 coefficient order is (real, imag) while
EIP-197 encodes (imag, real). The vector generator swaps, the shim
swaps, and the vectors pin the EIP order. GT (384 bytes) is mcl's
serialization; it round-trips through this family's own functions,
which is all a pairing-check consumer needs.

## Validation vectors: pin

Generated from ethereum/py_ecc at authoring time and hard-coded into
`LeanHazmatBn254Tests/Vectors.lean`, keeping the build hermetic.
