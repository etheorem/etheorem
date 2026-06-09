import LeanPoseidonTests.Kat
import LeanPoseidonTests.Ffi
import LeanPoseidonTests.Differential

/-!
# `LeanPoseidonTests`: Poseidon2 conformance gates (library root)

Poseidon2 has no centralised official KAT suite the way SHA-256 has NIST
CAVP, so conformance here is *differential*: agree with a trusted external
implementation (HorizenLabs `zkhash`) over many inputs, plus committed
fixed anchors. This test library collects the gates that are heavier than
the single inline anchor in `LeanPoseidon.Permutation`:

* `LeanPoseidonTests.Kat`: committed `zkhash` BN254 t=3 permutation /
  `compress` vectors via `native_decide`. **No Rust toolchain**, fires on
  `lake build LeanPoseidonTests` (`just test-poseidon-vectors`).
* `LeanPoseidonTests.Ffi` / `LeanPoseidonTests.Differential`: the
  `@[extern]` oracle bindings and the seeded-random differential test,
  driven by the `poseidon_fuzz` executable (`just fuzz-poseidon`). These
  are the only part that needs a Rust toolchain (cargo), and they are
  *linked* only into that executable, never at library-build time.

Splitting these out keeps `lake build LeanPoseidon` fast and Rust-free for
downstream consumers, mirroring how `LeanSha256` keeps its 129-vector NIST
CAVP batch out of the default build.
-/
