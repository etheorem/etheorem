# LeanImtPlus

Pure Lean 4 implementation of the LeanIMT+ tree and unified proof format from
[`vplasencia/leanimt-plus`](https://github.com/vplasencia/leanimt-plus).

The tree, proof, and verifier are generic over a small package-owned `Hasher`
interface. No SizzLean dependency is involved. Three adapters are shipped:

- `Sha256Spec`: pure `LeanSha256`, using the reference 216-bit circuit format;
- `Sha256Ffi`: the same commitments through OpenSSL-backed `LeanHazmatSha256`;
- `Poseidon2`: BN254 field digests through `LeanPoseidon.Poseidon2.compress`.

The package provides ordered insertion, permanent tombstone removal, in-place
update, promotion of unpaired Merkle nodes, unified membership and
non-membership proofs, root-bound verification, and typed rejection errors.
The reference uses an AVL predecessor index; this implementation currently
uses a linear scan while preserving physical leaves, roots, and proofs.

## Example

```lean
import LeanImtPlus

open LeanImtPlus

def membershipExample : Except TreeError Bool := do
  let tree ← (Tree.empty Sha256Spec).insertMany #[10, 25, 7, 3, 41, 18]
  let proof ← tree.generateProof 25
  return (verifyProof proof).isOk
```

`import LeanImtPlus` includes the generic core and pure SHA-256 adapter. Other
backends are opt-in:

```lean
import LeanImtPlus.Hasher.Sha256Ffi
import LeanImtPlus.Hasher.Poseidon2
```

Select them with `Tree.empty Sha256Ffi` or `Tree.empty Poseidon2`. `Proof H`
carries the digest type and committed root selected by `H`; `recomputeRoot`
exposes root reconstruction for wrappers that manage the public root
separately.

## Build and test

```bash
lake build LeanImtPlus
lake build LeanImtPlusTests
# or
just leanimt-plus-test
```

The tests retain the reference SHA-256 fixture, exercise the full lifecycle
with all three adapters, require pure and FFI SHA-256 commitments to agree,
and cover non-membership positions, removal, update, root tampering, tombstone
replay, range bounds, malformed paths, and mutation errors.
