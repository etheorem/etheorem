import LeanHazmatKeccak
import LeanHazmatSecp256k1
import LeanHazmatBn254
import LeanHazmatBlake2f
import LeanHazmatRipemd160
import LeanHazmatModexp
import LeanHazmatP256

/-!
# `LeanHazmatExecution`: the execution crypto layer in one import

The aggregator meta-package over the seven execution-layer LeanHazmat
families (packages/hazmat/docs/ARCHITECTURE.md §3.4). It declares no code of
its own; importing it brings every EL family's `LeanHazmat.*` names
into scope:

* `LeanHazmat.Keccak`, Keccak-256 (keccak-tiny): `keccak256`.
* `LeanHazmat.Secp256k1`, ECDSA recovery / verification
  (libsecp256k1): `ecdsaRecover`, `ecdsaVerify`.
* `LeanHazmat.Bn254`, alt_bn128 (mcl): `g1Add` / `g1Mul` /
  `g2Add` / `g2Mul`, the pairing pieces `millerLoopVec`,
  `finalExp`, `gtIsOne`.
* `LeanHazmat.Blake2f`, EIP-152: `blake2fCompress`.
* `LeanHazmat.Ripemd160`, precompile 0x03: `ripemd160`.
* `LeanHazmat.Modexp`, precompile 0x05: `modExp`.
* `LeanHazmat.P256`, EIP-7951: `p256Verify`.

Three more EL precompiles reuse consensus packages at zero new
dependencies: SHA-256 (0x02) → `LeanHazmat.Sha256`, KZG point
evaluation (0x0a) → `LeanHazmat.Kzg`, EIP-2537 BLS → `LeanHazmat.Bls`
(import `LeanHazmatConsensus` or the top-level `LeanHazmat` umbrella
for those).

## The import gate

The `example`s at the bottom pin every family's `LeanHazmat.*` name:
drop an `import` above and the build fails here, instead of staying
green with a family silently missing from the surface.

The vendored families need their `just hazmat-*-vendor` fetches before
`lake build`, see each package's README.
-/

set_option autoImplicit false

-- One type-level pin per family: the composition checks the name is
-- in scope through this root and has the documented primitive's type.
-- Definitional, never evaluated.
example : ByteArray → ByteArray := LeanHazmat.Keccak.keccak256
example : ByteArray → ByteArray → ByteArray → UInt32 → ByteArray :=
  LeanHazmat.Secp256k1.ecdsaRecover
example : ByteArray → ByteArray → ByteArray :=
  LeanHazmat.Bn254.g1Add
example : UInt32 → ByteArray → ByteArray → UInt64 → UInt64 → Bool →
    ByteArray :=
  LeanHazmat.Blake2f.blake2fCompress
example : ByteArray → ByteArray := LeanHazmat.Ripemd160.ripemd160
example : ByteArray → ByteArray → ByteArray → ByteArray :=
  LeanHazmat.Modexp.modExp
example : ByteArray → ByteArray → ByteArray → ByteArray → ByteArray →
    Bool :=
  LeanHazmat.P256.p256Verify
