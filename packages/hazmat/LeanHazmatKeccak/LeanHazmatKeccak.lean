import LeanHazmatKeccak.Ffi

/-!
# `LeanHazmatKeccak`: library root

FFI binding for **Keccak-256**, the execution layer's most-used
primitive: the `KECCAK256` opcode (0x20), address derivation, storage
slot hashing, the MPT trie, and RLP hashing all run through it.
Wrapped behind `@[extern]` under the `LeanHazmat.Keccak` brand
namespace. Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) crypto family.

`import LeanHazmatKeccak` brings the public surface into scope:

* `keccak256`: 32-byte digest, rate 136, original Keccak `0x01`
  padding. **Not** SHA3-256 (different padding, a different function
  on every input).

See [`LeanHazmatKeccak/Ffi.lean`](LeanHazmatKeccak/Ffi.lean) for the
binding and its trust assumption, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's trust
boundary (library, rev pin, validation vectors).

## Vendoring

The keccak-tiny single-file implementation (CC0, David Leon Gil) is
**vendored**: `just hazmat-keccak-vendor` fetches the pinned rev into a
gitignored `vendor/keccak-tiny/` before `lake build`
(packages/hazmat/docs/ARCHITECTURE.md §6). The upstream repo tags no releases,
so the pin is a commit rev, recorded in the recipe. The shim
translation unit `#include`s the vendored `.c` unmodified (its sponge
is `static`), so the vendored code stays byte-identical to the pin.

## Trust boundary

Unlike SHA-256, Keccak-256 has no pure-Lean reference; the binding is
an opaque `@[extern]` boundary validated only against the published
vectors (`LeanHazmatKeccakTests`).

Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatKeccakTests`); the default `lake build` skips them and they
fire via `lake build LeanHazmatKeccakTests`.
-/
