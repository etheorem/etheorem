import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving
import SizzLean.Spec.SSZError
import SizzLean.Hasher.Class
import SizzLean.Hasher.Sha256
import SizzLean.Hasher.Sha256Spec
import SizzLean.Hasher.Sha256Equiv
import SizzLean.Hasher.Sha256Batch
import SizzLean.Cache.MerkleTree.HashCons
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update

/-!
# `SizzLean`: library root

This file is the umbrella import. The re-exports above are the
library's *public surface*, names a user is expected to write in
their own code. They map one-to-one onto the sections of
[`MANUAL.md`](../MANUAL.md):

* `Repr/Class`, `Repr/Instances`, `Repr/Deriving`: the `SSZRepr`
  class, the built-in field-type instances (`Bool`, `UIntN`,
  `BitVec 128/256`, `Vector`, `SSZList`, `Bitvector`, `Bitlist`),
  and the `deriving SSZRepr` handler.
* `Spec/SSZError`: the deserialise-error sum returned by
  `SSZ.deserialize`.
* `Hasher/Class`, `Hasher/Sha256`, `Hasher/Sha256Spec`: the
  `Hasher` typeclass and its two shipping instances. The FFI
  `Sha256` instance delegates to the `LeanHazmatSha256` package
  (`LeanHazmat.Sha256.sha256Hash` / `sha256Combine`); the bindings
  themselves no longer live in SizzLean (hazmat-docs/ARCHITECTURE.md
  §9), only the typeclass glue.
* `Hasher/Sha256Batch`: the pure-Lean reference
  (`sha256BatchCombineSpec`) and the `sha256BatchCombine_eq_spec`
  axiom for the FFI batched sibling-combine
  (`LeanHazmat.Sha256.sha256BatchCombine`).
* `Hasher/Sha256Equiv`: the named FFI ≡ pure-Lean equivalence
  axioms (`sha256Hash_eq_spec`, `sha256Combine_eq_spec`;
  `sha256BatchCombine_eq_spec` lives next to the reference def in
  `Sha256Batch`), rewrite-targets for proofs that need FFI hashes to
  reduce. The SizzLean-side trust-boundary inventory is recoverable
  via `grep -rEn '^axiom '` over `packages/SizzLean` (the `@[extern]`
  bindings live in `packages/LeanHazmatSha256`).
* `Cache/TreeBacked`: `CachedSSZ`, the cached-only one-flavour
  type, with `CachedSSZ.ofValue` and `CachedSSZ.hashTreeRoot`.
* `Cache/Box`: `SSZ.Box`, the closed union of cached + uncached
  flavours, plus the four smart constructors `SSZ.FastBox`,
  `SSZ.PureBox`, `SSZ.CachedBox`, `SSZ.UncachedBox`.
* `Cache/Update`: the `sszUpdate` macro.

Internal modules (the spec universe `SSZType` with its
serialise/deserialise/hashTreeRoot operations, the proof artefacts
in `Proofs/`, the Merkle-tree machinery in `Cache/MerkleTree/`,
the `UncachedSSZ` structure that backs `SSZ.PureBox` /
`SSZ.UncachedBox`) are *transitively* pulled in via the public
files above and remain importable by qualified path for advanced
uses or by sibling packages (`LeanEthCS` reaches into
`Spec/Serialize` etc. directly from its `deriving SSZRepr`
handler infrastructure). They are deliberately not listed here so
this file reads as the user's mental model of the library.

Acceptance / property-test gates live in a separate `lean_lib`
(`SizzLeanTests`); the default `lake build` skips them and they
fire via `lake build SizzLeanTests` (or `just test-ssz`).
-/
