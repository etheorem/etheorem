# LeanPoseidon: Implementation Plan

This document sequences the work that [`ARCHITECTURE.md`](ARCHITECTURE.md)
describes, the LeanPoseidon library's plan. Each stage has a goal, the
concrete deliverables it ships, an acceptance criterion (one observable
that says the stage is done), and notes on dependencies, parallelism, and
risk.

The sibling package `LeanPoseidonProofs` appears only in Phase 3, where the
equivalence proof needs it (and mathlib). The rest of the monorepo
(`LeanSha256` / `SizzLean` / `EthCLLib` / `EthCLSpecs`) does not appear at all:
LeanPoseidon is a standalone island (ARCHITECTURE.md §"Relationship to the rest of the
monorepo"), parallel to `LeanSha256` and consumed by nothing yet.

The sequencing matches §13 of ARCHITECTURE.md: Phase 1 lands the
mathlib-free, kernel-reducible core (field → params → layers → permutation
→ public API) with the anchor known-answer test (KAT) as a build gate;
Phase 2 adds the Rust FFI oracle and differential conformance; Phase 3
adds the `LeanPoseidonProofs` package and proves the shipped fast layers equal
the textbook dense reference; Phase 4 generalises widths and fields (optional);
Phase 5 finishes the docs. The guiding principle is the same one the
rest of the monorepo follows: **ship a reducible core, validate it
empirically against a trusted external implementation, then invest in the
machine-checked equivalence**, so the proof effort targets a
conformance-validated implementation, not a speculative one.

No time estimates. These depend on developer capacity and how much of the
toolchain (Lake `extern_lib` for the Rust target, the mathlib pin, `ring`)
needs discovery vs. is already familiar.

---

## Stage 0: Project bootstrap

**Goal.** Establish the build, lint, and CI baseline every later stage
assumes, for a brand-new subpackage.

**Deliverables.**
- `packages/LeanPoseidon/lakefile.lean`: procedural (needed for the Phase 2
  cargo/`extern_lib` target; the same justification as `SizzLean`'s C
  shim). At Stage 0 it declares the package, `licenseFiles :=
  #["../../LICENSE"]`, and a single empty `lean_lib LeanPoseidon` rooted at
  `LeanPoseidon.lean`. The cargo target and the `LeanPoseidonTests` lib / exe are
  added in Phase 2.
- `packages/LeanPoseidon/LeanPoseidon.lean`: library-root skeleton (module
  docstring + the re-export imports added as modules land).
- Umbrella `lakefile.toml`: add the `[[require]] LeanPoseidon` block. (The
  `LeanPoseidonProofs` require is added in Phase 3 when that package exists.)
- A project-wide `set_option autoImplicit false` discipline (per
  CLAUDE.md): each new file opens with this option.
- README skeleton pointing at ARCHITECTURE.md / PLAN.md, noting the
  package implements Poseidon2 and linking Nethermind's `Poseidon.lean`
  for v1.
- Justfile recipes `gen-poseidon-params`, `test-poseidon`, `fuzz-poseidon`
  (stubs wired as the underlying targets land), mirroring `gen-cavp` /
  `test-sha256`. CI (`lean_action_ci.yml`) gains `lake build LeanPoseidon`;
  every CI step that has a Justfile recipe goes through `just <recipe>`.

**Acceptance.** `lake build LeanPoseidon` succeeds on a clean checkout; the
umbrella `lake build` still succeeds; CI green.

**Notes.** No external dependencies yet, neither the Rust crate nor
mathlib. Keep the procedural lakefile minimal; it grows only the cargo
target in Phase 2.

---

## Phase 1: Core (no FFI, no proofs)

Lands the entire shipped public API as pure, mathlib-free, reducible Lean.
At the end of this phase `lake build LeanPoseidon` computes a correct
permutation and the anchor KAT passes; the library is usable as a
reference even before conformance and proofs land.

### Stage 1: The field `Bn254Fr`

**Goal.** A minimal BN254 scalar field with the arithmetic the permutation
needs, plus the canonical byte codec that pins endianness once. Named
`Bn254Fr` (the BN254 *scalar* field `Fr`); as of Phase 4 Stage 10a it is
`abbrev Bn254Fr := Fp bn254FrModulus` over the modulus-parameterised
`Fp (p)` (ARCHITECTURE.md §3).

**Deliverables.**
- `packages/LeanPoseidon/LeanPoseidon/Field.lean`: `structure Bn254Fr` (a `Nat` below
  the modulus `p`), `add` / `sub` / `neg` / `mul` / `pow` (each `mod p`),
  `HAdd` / `HMul` / `HPow` instances; `toBytes : Bn254Fr → ByteArray` and
  `ofBytes? : ByteArray → Option Bn254Fr` (32-byte, endianness pinned against
  the §6 big-endian anchor; `ofBytes?` partial because a 32-byte value can
  exceed `p`).
- Module docstring glossing `Bn254Fr` for the crypto reader (why a subtype, why
  `Nat`/GMP, why `ofBytes?` is `Option`).
- `#guard` identities: a few field-arithmetic facts (e.g. `p − 1 + 1 = 0`,
  a known `x^5`) and `ofBytes? (toBytes x) = some x` round-trips.

**Acceptance.** `lake build LeanPoseidon` succeeds; the `#guard`s pass.

**Risk.** Low. Straight arithmetic on `Nat`. The only judgement call is
the byte-codec endianness, which the anchor KAT (Stage 4) will confirm.

### Stage 2: Parameters + the BN254 t=3 instance

**Goal.** Capture a Poseidon2 instance as data and generate the BN254 t=3
constants from the pinned reference (transcription is correctness-critical,
so it is mechanised).

**Deliverables.**
- `packages/LeanPoseidon/LeanPoseidon/Poseidon2/Params.lean`: `structure Params R`
  (`t`, `fullRounds`, `partialRounds`, `sboxDegree`, `roundConstants`,
  `intDiag`) and the concrete BN254 t=3 instance.
- `packages/LeanPoseidon/scripts/gen_poseidon_params.py`: emits the
  constants from a pinned HorizenLabs reference commit (stdlib-only
  Python; wrapped as `just gen-poseidon-params`). The pinned commit is
  recorded in the script header.
- `#guard`s on the shape: `roundConstants.size = 80`, `intDiag.size = 3`,
  `sboxDegree = 5`.

**Acceptance.** `lake build LeanPoseidon` succeeds; the size `#guard`s pass;
re-running the generator reproduces `Params.lean` byte-identically.

**Risk.** Medium. *Transcription is the highest-value-to-get-right item
in the core.* Mitigation: generate, don't hand-type; the anchor KAT
(Stage 4) and the differential test (Stage 7) catch any mistranscription.

### Stage 3: Linear layers (fast + reference)

**Goal.** Both the shipped cheap layers and the textbook dense layers, so
Phase 3 can prove them equal.

**Deliverables.**
- `packages/LeanPoseidon/LeanPoseidon/Poseidon2/LinearLayers.lean`: `mulExternalFast` /
  `mulInternalFast` (sum-plus-scaled forms) and `mulExternalRef` /
  `mulInternalRef` (literal dense `t×t` products), all generic over `R`
  and all **public** (LeanPoseidonProofs imports them).
- Module docstring with the duality table (ARCHITECTURE.md §5) and the
  `circ(2,1,1)` / `J + diag` derivations for t=3.
- `#guard`s: on the concrete BN254 t=3 params, `mulExternalFast = …Ref`
  and `mulInternalFast = …Ref` on a couple of sample states (a sanity
  check before the general proof in Phase 3).

**Acceptance.** `lake build LeanPoseidon` succeeds; the sample-state `#guard`s
agree between fast and reference.

**Risk.** Low–medium. The dense reference is mechanical; the fast forms
must match the chosen matrices exactly. The `#guard` cross-check is the
early guard, the Phase 3 theorem the real one.

### Stage 4: The permutation + anchor KAT

**Goal.** The full Poseidon2 schedule (fast layers), a structurally
parallel dense `permuteRef`, and the build-time anchor gate.

**Deliverables.**
- `packages/LeanPoseidon/LeanPoseidon/Poseidon2/Permutation.lean`: a shared round schedule
  parameterised over the linear-layer ops, instantiated as `permute`
  (fast) and `permuteRef` (dense) so they differ *only* in the layer
  calls (this factoring is what makes the Phase 3 congruence clean).
  Structural/size lemmas as needed.
- The anchor-KAT `native_decide` example: input `[0,1,2]` → the three
  expected BN254 t=3 permutation outputs (ARCHITECTURE.md §6).
- Module docstring glossing full vs partial rounds, ARK, the S-box, and
  the `native_decide` axiom note.

**Acceptance.** `lake build LeanPoseidon` runs the anchor KAT and it passes.
(This simultaneously validates Stages 1–3: a wrong field codec, constant,
or layer fails here.)

**Risk.** Medium. The round schedule must match the reference's ordering
(initial `M_E`, the full/partial/full split, where each constant is
added). The anchor KAT is the catch-all.

### Stage 5: Public API: `compress` + `hash`

**Goal.** The two shipped entrypoints over the permutation.

**Deliverables.**
- `packages/LeanPoseidon/LeanPoseidon/Poseidon2/Compress.lean`: `compress (left right :
  Bn254Fr) : Bn254Fr`, the 2-to-1 binary-Merkle primitive, following the pinned
  reference's capacity init + squeeze projection.
- `packages/LeanPoseidon/LeanPoseidon/Poseidon2/Sponge.lean`: `hash : Array Bn254Fr → Array Bn254Fr`,
  rate `t−1` / capacity 1 sponge.
- `packages/LeanPoseidon/LeanPoseidon.lean`: re-export `Field` / `Params` /
  `LinearLayers` / `Permutation` / `Compress` / `Sponge`.
- An `example` / `#guard` per entrypoint against a known reference value.

**Acceptance.** `lake build LeanPoseidon` succeeds; the `compress` / `hash`
examples pass.

**Risk.** Low–medium. Both are thin over `permute`; the risk is matching
the reference's sponge padding / capacity convention, nailed by the
examples and re-confirmed by the Phase 2 KATs.

**Phase 1 exit gate.** `lake build LeanPoseidon` green and mathlib-free; the
anchor KAT and the `compress` / `hash` examples pass; the core is a usable
pure-Lean Poseidon2 reference. Conformance against an external oracle and
the equivalence proof come next.

---

## Phase 2: Conformance (FFI oracle + differential testing)

Poseidon2 has no centralised official KAT suite, so conformance is
differential: agree with a trusted external implementation over many
seeded-random inputs, plus committed fixed anchors. The oracle is
test-only, never the shipped path, never in a proof.

### Stage 6: Rust oracle + Lake wiring

**Goal.** Vendor the trusted implementation and link it as an
`extern_lib`.

**Deliverables.**
- `packages/LeanPoseidon/rust-oracle/`: `Cargo.toml` (dep `zkhash`,
  `crate-type = ["staticlib"]`), committed `Cargo.lock`, `src/lib.rs` with
  `#[no_mangle] extern "C"` entrypoints over the 32-byte field-element
  ABI; `rust-oracle/target/` gitignored.
- `packages/LeanPoseidon/lakefile.lean`: a `target` shelling
  `cargo build --release` (emitting `libposeidon_oracle.a`), an
  `extern_lib` adopting that archive, and `moreLinkArgs` for the Rust
  runtime's native deps (`-lpthread -ldl -lm`, possibly `-lgcc_s`). Add
  the `lean_lib LeanPoseidonTests` (package-prefixed) and the `poseidon_fuzz`
  `lean_exe`.
- `packages/LeanPoseidon/LeanPoseidonTests/Ffi.lean`: `@[extern] opaque`
  bindings; the ABI contract (field elements marshalled via
  `Bn254Fr.toBytes` / `Bn254Fr.ofBytes?`, endianness pinned).

**Acceptance.** `lake build LeanPoseidonTests` builds the oracle and links;
a smoke `#eval`/`example` shows the FFI permutation of `[0,1,2]` equals the
anchor.

**Risk.** Medium. Lake's cargo integration and the Rust-staticlib link
surface are the fiddly part (ARCHITECTURE.md §8). Mitigations: pin the
crate; `Cargo.lock` committed; resolve link errors via `moreLinkArgs`, not
ad-hoc shell.

**Notes.** This is the only stage that introduces a non-Lean toolchain
dependency (Rust/cargo in CI). It is confined to the `LeanPoseidonTests` /
`poseidon_fuzz` job. `lake build LeanPoseidon` and `LeanPoseidonProofs` need no
Rust. Document the requirement in the README.

### Stage 7: Differential test + committed KATs

**Goal.** The live conformance gate and the no-toolchain-needed anchors.

**Deliverables.**
- `packages/LeanPoseidon/LeanPoseidonTests/Differential.lean`: a pure-Lean
  seeded splitmix PRNG generating deterministic "random" field elements;
  the `poseidon_fuzz` `IO` exe running both implementations and asserting
  `leanPermute == ffiPermute` over N trials (e.g. 10 000), `log()`-ing the
  trial count (no silent caps).
- `packages/LeanPoseidon/LeanPoseidonTests/Kat.lean`: the committed HorizenLabs
  fixed vectors via `native_decide` (fire even without Rust present).

**Acceptance.** `lake build LeanPoseidonTests && lake exe poseidon_fuzz` is
green: the committed KATs pass and N seeded-random inputs all satisfy
`leanPermute == ffiPermute`. Sanity: an external value
(Nethermind / nim-poseidon2 BN254 t=3) reproduces.

**Risk.** Low–medium. The differential harness is small; the substantive
risk (mistranscribed constants) was front-loaded to Stage 2 and is exactly
what this stage catches.

**Phase 2 exit gate.** Differential test green over N trials; committed
KATs pass; the Rust dependency is confined to the fuzz job. The pure-Lean
implementation is now conformance-validated against a trusted oracle,
the foundation Phase 3's proof investment builds on.

---

## Phase 3: Equivalence proofs (mathlib)

> **✅ Done.** The binding decision, the mathlib ↔ toolchain pin, resolved
> cleanly: mathlib's `v4.29.1` tag has `lean-toolchain`
> `leanprover/lean4:v4.29.1`, an *exact* match with the repo, so no
> toolchain bump was needed and `lake exe cache get` fetches prebuilt
> oleans (nothing compiled from scratch). `packages/LeanPoseidonProofs` is
> a standalone, mathlib-bearing package (the monorepo's only mathlib
> dependency), kept out of the umbrella so the core and every other gate
> stay mathlib-free. `CommRing (Fp p)` is transported from `ZMod p` (one
> instance for both fields), the two layer identities close by `ring` (after
> `Vector.ext` + `interval_cases`), and `permute = permuteRef` follows by
> congruence through `permuteWith`, with a **verified-clean axiom
> footprint** (`[propext, Classical.choice, Quot.sound]`; no FFI, no
> `ofReduceBool`). The de-risking above (the `*Fast`/`*Ref` factoring, the
> conformance-validated implementation) made the proof the small, drop-in
> step it was designed to be.

The closing correctness phase: prove the shipped fast linear layers equal
the textbook dense reference, hence the whole permutations coincide. This
is the machine-checked form of Poseidon2's central optimisation claim.
Positioned after conformance so the proof targets a validated
implementation.

### Stage 8: `LeanPoseidonProofs` package + `CommRing (Fp p)` ✅ done

**Goal.** Stand up the mathlib-bearing package and give the field its ring
structure.

**Shipped.**
- `packages/LeanPoseidonProofs/lakefile.toml`: `[[require]] LeanPoseidon`
  (path `../LeanPoseidon`) + `[[require]] mathlib` (git, `rev = "v4.29.1"`);
  `licenseFiles = ["../../LICENSE"]`. The package is **standalone** (not
  added to the umbrella, see ARCHITECTURE.md §11), so mathlib stays out of
  the root; `lake update` was run *in the package* and its
  `lake-manifest.json` is committed (a `.gitignore` exception) to pin the
  exact mathlib + transitive revs. `lake exe cache get` fetches prebuilt
  oleans (the `v4.29.1` toolchain match means no from-scratch build).
- `packages/LeanPoseidonProofs/LeanPoseidonProofs/FpCommRing.lean`:
  `instance [NeZero p] : CommRing (Fp p)`, transported from `ZMod p` along
  `a ↦ (a.val : ZMod p)` via `Function.Injective.commRing` (so the core's
  own `Fp` arithmetic remains the ring operations). Generic in `p` ⇒ one
  instance for `Bn254Fr` and `Bls12Fr`.

**Acceptance (met).** `lake build LeanPoseidonProofs` compiles with mathlib
resolved from cache; the `CommRing (Fp p)` instance type-checks (and powers
`ring` on `Fp`-arithmetic in Stage 9).

### Stage 9: Equivalence theorems ✅ done

**Goal.** Prove the layers equal generically, then the permutations.

**Shipped.**
- `packages/LeanPoseidonProofs/LeanPoseidonProofs/Equivalence.lean`:
  `mulExternalFast_eq_ref` and `mulInternalFast_eq_ref` over a generic
  `[CommRing R]` (closed by `Vector.ext` + `interval_cases` then `ring`),
  `permute_eq_permuteRef` by `funext` + congruence through `permuteWith`,
  and `permute_eq_permuteRef_bn254` / `…_bls12` specialisations.

**Acceptance (met).** The theorems compile with no `sorry`; `#print axioms`
on each shows exactly `[propext, Classical.choice, Quot.sound]`, **no FFI
axiom, no `Lean.ofReduceBool`** (verified during review).

**Phase 3 exit gate (met).** `permute = permuteRef` proved with a clean,
verified axiom footprint; `just test-poseidon-proofs` green. The "fast path
is faithful" result is shipped.

---

## Phase 4: Generalise widths and fields (optional follow-up)

**Goal.** Demonstrate the Open/Closed claim: new widths *and* new fields
are new data/instances, with no edits to the generic layers or proofs.

### Stage 10a: Abstract the prime field ✅ done

**Deliverables (shipped).**
- `Field.lean` generalises the concrete field to a modulus-parameterised
  `structure Fp (p : Nat)` (a `ZMod`-style bounded-`Nat`; arithmetic +
  instances + byte codec derived once over `{p} [NeZero p]`, `NeZero` being
  a Lean-core class), with the default recovered as
  `abbrev Bn254Fr := Fp bn254FrModulus` (ARCHITECTURE.md §3 *Abstracting the
  field*). Adding a field is then a modulus + its `NeZero` instance, not a
  copy of the arithmetic. Qualified `Bn254Fr.{ofNat, toBytes, ofBytes?}` are
  thin `abbrev` re-exports, so no call site changed.
- A `PrimeField` typeclass was the alternative shape; the parameterised
  structure was preferred (single canonical representation). A generic
  `Fp 7` `#guard` exercises the abstraction at a second modulus.

**Acceptance (met).** `permute` / `compress` / the anchor KAT compile and
pass **unchanged** over `Bn254Fr := Fp bn254FrModulus`; the 100 000-trial
differential still agrees with the oracle, the hot path stays
`Nat`/GMP-backed (the reducible `abbrev` carries no Montgomery / no
typeclass-method indirection at the leaves). The abstraction is structural
only, never a representation change.

### Stage 10b: Additional instances

**Field axis: ✅ done (BLS12-381 `Fr`, t=3).** A *second field* now ships,
demonstrating the field abstraction end to end with zero changes to the
generic `permute` / layers:
- `Field.lean` adds `blsFrModulus` + `NeZero` + `abbrev Bls12Fr := Fp
  blsFrModulus` + re-exports (the whole field is ~6 lines, new data, no
  arithmetic).
- `gen_poseidon_params.py` is now data-driven over an `INSTANCES` list and
  emits both `bn254Params : Params Bn254Fr` and `bls12Params : Params
  Bls12Fr` from `poseidon2_bn256.json` / `poseidon2_bls12.json` (both
  machine-extracted from `zkhash` v0.2.0).
- **Anchor KAT** for BLS12 t=3 (`Poseidon2/Permutation.lean`), **committed
  KATs** (`Kat.lean`), and the **differential test** all run the *same*
  generic `permute` / generic harness over `Bls12Fr`. The Rust oracle gained
  a `poseidon_oracle_bls12_t3_permute_be` entrypoint (generic
  `permute_be_with<G>`); `runDifferential` is generic over the field and runs
  **both** fields (10 000+ trials each, all agreeing).

**Width axis: ⏸ deferred (the harder part).** Adding `t ≠ 3` requires
generalising the layers/permutation from the concrete `Vector R 3` to
`Vector R t` (and, for `t ≥ 4`, the `M4`-based external matrix rather than
`circ`). `t = 2` is tractable (its fast forms match t=3), but this is a
refactor of the verified core rather than pure new data, so it is held under
the same deferral discipline. The field axis above already validates the
abstraction approach.

**Acceptance (met for the field axis).** A second field (BLS12-381 `Fr`) has
a passing anchor KAT, committed KATs, and 10 000+ differential trials; the
existing BN254 core compiles and passes **unchanged** (the layers are
generic over `R`, the field is configuration).

**Risk.** Low for fields (additive, new data, done). Moderate for widths
(core `t`-generalisation), which is why widths stay deferred.

---

## Phase 5: Docs

### Stage 11: README + monorepo docs

**Deliverables.**
- `packages/LeanPoseidon/README.md`: public overview: what it implements
  (Poseidon2), the `compress` / `hash` surface, the conformance + proof
  story, the require snippet, and the Nethermind `Poseidon.lean` link for
  v1.
- Root `README.md`, `CLAUDE.md` ("three libraries" → updated count; mathlib
  dep note), and `monorepo-arch.md` (the standalone-island graph)
  updated.

**Acceptance.** Docs land; the umbrella build stays green; a reader can go
from the README to a working `compress` call.

**Risk.** Low.

---

## Phase 6: Structural-correctness proofs (✅ done)

The proof investment after Phase 3. Where Phase 3 certified the linear-layer
*optimisation*, Phase 6 certifies the permutation's **structural correctness**,
that it is an actual bijection, plus the sponge's padding hypothesis and a
decidable parameter check. **All four targets are shipped** (in
`LeanPoseidonProofs`), building green with a verified-clean axiom footprint.

**Strategy: prove on the reference, transport to the shipped path.**
`permute` and `permuteRef` differ *only* in the linear layers (the S-box, the
ARK additions, and the schedule are the shared `permuteWith`), and they are
already proved equal (`permute_eq_permuteRef`, Phase 3). So structural
properties are proved on the **dense `permuteRef`**, where the layers are
genuine matrix–vector products and mathlib's `Matrix.det` /
"`IsUnit (det M) ⇒ mulVec` bijective" machinery applies directly. They are
then transported to the shipped `permute` by a one-line rewrite through the
existing equivalence. This is the reference implementation earning its keep a
second time (ARCHITECTURE.md §9).

**Primality: decided.** Bijectivity needs `Field (Fp p)`, hence
`Fact (Nat.Prime p)`, which the core's `CommRing (Fp p)` deliberately does not
assume (`native_decide` cannot help here; `Nat.Prime`'s decidability is trial
division, infeasible at 254 bits). Generic structural theorems are stated over
`[Fact (Nat.Prime p)]` and keep the clean
`[propext, Classical.choice, Quot.sound]` footprint; the concrete `…_bn254` /
`…_bls12` specialisations get the `Fact` from a single **cited axiom**,
`axiom bn254FrModulus_prime : Nat.Prime bn254FrModulus` (and the BLS12
sibling), referencing the canonical modulus def and attested by the curve
construction + EIP-196/197. These are standardised, literature-vetted primes
(prime *by curve construction*, not numbers we chose), so a cited axiom is a
sound import in the same family as the project's existing `ofReduceBool` / FFI
concessions, bounded by an explicit policy (*standardised prime-field moduli
only; arbitrary primality facts must be proved*) and swappable in one line for
the Verified-zkEVM `CompPoly` Pratt/Lucas certificate later. The axiom's blast
radius is exactly the two specialisations.

**Targets (all shipped).**
1. ✅ **`permute` is a bijection**: `permute_bijective_bn254` /
   `permute_bijective_bls12` (`Bijective.lean`). S-box `x⁵` bijective
   (`gcd(5, p−1) = 1`, `decide`); external/internal dense layers invertible
   (`det = 4` / `det = 7` ≠ 0, `decide`); ARK translations bijective; composed
   over `permuteWith` via a `List.foldl`-based fold-of-bijections lemma; then
   transported to `permute` through `permute_eq_permuteRef`.
2. ✅ **Sponge `pad` injectivity**: `pad_injective` (`Padding.lean`). No
   primality; the marker `1 ≠ 0` pins the parity, `List.append_inj_left` strips
   the suffix. Axiom footprint completely clean (`[propext, Choice, Quot.sound]`).
3. ✅ **`compress` not collision-resistant in isolation**:
   `compress_not_injective` (`Bijective.lean`): the 2-to-1 map has collisions by
   pigeonhole (`Nat.card_le_card_of_injective` + `p < p²`). The structural reason
   a Merkle node needs leaf pre-hashing + domain separation, not `compress`
   alone (ARCHITECTURE.md §7).
4. ✅ **Decidable round-count check**: `meetsFloor` + `#guard`s
   (`RoundCount.lean`): the shipped `R_F = 8`, `R_P = 56` clear the reference
   script's *statistical* (`R_F_1`) and *interpolation* (`R_F_2`, via `Nat.clog`)
   minimum-round bounds at 128-bit security, for both instances. Certifies the
   *published security floor*, a different axis than the differential test's
   "matches `zkhash`". Scope: the two crisply-recastable bounds (the Gröbner
   `R_F_3..5` + binomial cost rest on the reference's float evaluation and are
   not re-encoded); it does **not** prove the inequalities imply security.

**Acceptance (met).** `Bijective (permute bn254Params)` / `…bls12Params` and
`Function.Injective pad` proved with **no `sorry`**, no `native_decide`; the
round-count `#guard`s pass. `#print axioms` verified: the generic theorems are
`[propext, Classical.choice, Quot.sound]`; the concrete specialisations add
**exactly** the one cited primality axiom (`bn254FrModulus_prime` /
`blsFrModulus_prime`) and **nothing FFI / `ofReduceBool`**; `pad_injective`
cites no primality axiom at all.

**Shipped files** (`packages/LeanPoseidonProofs/LeanPoseidonProofs/`):
`Primality.lean` (cited axioms + `Fact` instances), `FpField.lean`
(`Field (Fp p)` from `[Fact (Nat.Prime p)]`, reusing the `CommRing` parent,
no diamond), `Bijective.lean` (S-box / layer / round / schedule bijectivity →
`permute_bijective_{bn254,bls12}` + `compress_not_injective`), `Padding.lean`
(`pad_injective`), `RoundCount.lean` (`meetsFloor` `#guard`s). `FpCommRing.lean`
de-privatised its `toZMod` helpers so `FpField` reuses them.

### Out of scope for now: sponge indifferentiability (try in the future)

The natural *crypto-grade* result is conditional: *if* `permute` is modelled
as an ideal/random permutation, *then* the sponge `hash` is indifferentiable
from a random oracle up to the capacity bound (Bertoni–Daemen–Peeters–Van
Assche; machine-checked for Keccak in EasyCrypt). It is **deliberately not in
the works**: it is game-based reasoning in the random-permutation model
(EasyCrypt / VCVio territory, not yet ported to a sponge in Lean), it is a
statement about an *idealised* permutation rather than the concrete one, and
it does not fit this library's kernel-reducible, identity-style proofs. It is
recorded here as a possible future direction, something we *could* try later,
not a planned phase. (Hard boundary: unconditional collision/preimage
resistance of the concrete permutation is **not** a theorem at all; it rests
on best-known-attack cryptanalysis, which is what the EF Poseidon Initiative
assesses.)

---

## Deferred: SizzLean `Hasher` bridge (not planned)

Wiring a `Hasher Poseidon` instance into `SizzLean`, so SSZ Merkleization
could be driven by LeanPoseidon, is **not on this plan**, on the
spec-is-the-source-of-truth principle (ARCHITECTURE.md §"Relationship to
the rest of the monorepo"):

- EIP-7864's hash function is non-final (BLAKE3 placeholder; Poseidon2 a
  candidate under security review);
- the `bytes → field` encoding for state-tree leaves is *explicitly
  undetermined* upstream; and
- SSZ feeds its `Hasher` arbitrary 32-byte chunks, but BN254's modulus is
  ~254-bit, so any binding must choose an encoding with real correctness
  consequences (reduce mod r is lossy; reject ≥ r is partial; limb-split
  changes the width story).

No project has decided this, so inventing it here would be the "don't
invent ahead of the spec" smell. **When EIP-7864 settles a hash *and* an
encoding**, the bridge is a clean Open/Closed one-instance addition: a
pure-Lean `SizzLean/Hasher/Poseidon.lean` calling `LeanPoseidon.compress`
(no FFI, no axiom; SSZ roots under LeanPoseidon would be provable by plain
`native_decide`), reusing `Bn254Fr`'s byte codec. Until then, `SizzLean` stays
untouched and its `Hasher` class's existing future-`Poseidon2` comment
stays aspirational. This is the analogue of `SizzLean`'s "Approach C
`profile%` macro, not planned" item: a well-understood future extension
deliberately left unbuilt until its upstream consumer is concrete.

---

## Cross-cutting concerns (apply to every stage)

- **Literate by default** (CLAUDE.md). Every new `*.lean` file opens with
  a `/-! … -/` module docstring framing it for both Lean-fluent and
  crypto-fluent readers; every public declaration carries a `/--`
  *why*-docstring; each public entrypoint gets an `example` / `#guard`.
- **No `sorry` in committed code.** A `TODO` plus a tracking note is
  acceptable for a single-commit WIP; CI should reject `sorry` on `main`.
- **`set_option autoImplicit false` per file.**
- **Strict structural recursion.** No `partial def` unless termination
  genuinely cannot be shown; prefer `termination_by` + `decreasing_by`.
- **No committed `#eval` / `#check` / `#print`.** Use `example : … := by …`
  or `#guard` for build-time assertions. (`#print axioms` is run during
  review to confirm the Stage 9 footprint, not committed.)
- **The FFI oracle is test-only.** It never appears in the shipped API or a
  proof term; the Rust toolchain stays confined to the `poseidon_fuzz` job.

## Key risks

- **Mathlib ↔ toolchain pin (Phase 3).** ✅ *Resolved.* mathlib's `v4.29.1`
  tag has `lean-toolchain` `leanprover/lean4:v4.29.1`, an exact match with
  the repo, so no toolchain bump was needed and `lake exe cache get` uses
  prebuilt oleans. The hand-prove fallback was not needed.
- **`CommRing (Fp p)` route.** ✅ *Decided.* `Function.Injective.commRing`
  transport from `ZMod p` (keeping the core's `Fp` ops), generic in `p`,
  one instance for both fields.
- **Parameter transcription (Stage 2).** Correctness-critical; mechanised
  via `gen_poseidon_params.py` against a pinned commit and caught by the
  anchor KAT + differential test.
- **FFI ABI endianness (Stage 6).** The `Bn254Fr` byte codec and the Rust
  `extern "C"` ABI must agree, or the differential test passes on garbage.
  Pinned in `Field.lean` against the big-endian anchor; the differential
  test confirms it.
- **Rust-staticlib link surface (Stage 6).** Cargo emits the archive;
  `extern_lib` adopts it and `moreLinkArgs` supplies the Rust runtime's
  native deps, not `buildStaticLib` (the C-shim shape does not transfer).
- **Width-source discrepancy** (t=3 vs t=4 in the literature). We pin t=3
  (Merkle compression) and keep `Params` generic so t=4 is a later
  instance (Phase 4).

## Status snapshot

| Phase | Stages | Status |
| --- | --- | --- |
| 0: Bootstrap | Stage 0 | ✅ done: `lake build LeanPoseidon` + umbrella green |
| 1: Core | Stages 1–5 | ✅ done: anchor KAT + compress KATs + all `#guard`s pass; mathlib-free |
| 2: Conformance (FFI oracle + differential) | Stages 6–7 | ✅ done: committed KATs pass; differential test green over 100 000 seeded-random trials vs `zkhash`; Rust confined to `poseidon_fuzz` |
| 3: Equivalence proofs (mathlib) | Stages 8–9 | ✅ done: `CommRing (Fp p)` + `permute = permuteRef` (both fields); axiom footprint verified clean (`propext`/`Classical.choice`/`Quot.sound`); standalone `LeanPoseidonProofs`, `v4.29.1` pin |
| 4: Generalise widths and fields (optional) | Stages 10a–10b | 10a ✅ done (`Fp (p)`); 10b field axis ✅ done (BLS12-381 `Fr`); 10b width axis (`t ≠ 3`) ⏸ deferred |
| 5: Docs | Stage 11 | ✅ done: README + root README / CLAUDE.md / monorepo-arch.md + this doc |
| 6: Structural-correctness proofs | Targets 1–4 (bijectivity, `pad` injectivity, `compress` non-injectivity, round-count `#guard`) | ✅ done: `permute_bijective_{bn254,bls12}` + `compress_not_injective` + `pad_injective` + `meetsFloor` `#guard`s; axioms verified `[propext, Choice, Quot.sound]` + one cited primality axiom on the concrete specialisations, no FFI/`ofReduceBool` |
| Deferred | SizzLean `Hasher` bridge | not planned (gated on EIP-7864) |
| Deferred | Sponge indifferentiability | not in the works, possible future (idealised-permutation; EasyCrypt / VCVio territory) |

### Deviations from the original design (recorded as built)

- **The concrete field is named `Bn254Fr`, not `Fp`**: it is specifically
  the BN254 *scalar* field `Fr` (order `bn254FrModulus`, the group order
  `r`), so the generic-sounding `Fp` would mislead. The field is now
  abstracted (Phase 4 Stage 10a, done): `Fp (p : Nat)` is the parameterised
  prime field and `abbrev Bn254Fr := Fp bn254FrModulus` the default, keeping
  the `Nat`/GMP hot path (ARCHITECTURE.md §3 *Abstracting the field*).
- **Layers/permutation specialised to `t = 3`** (`Vector R 3`, not the
  abstract `Vector R p.t`), generic over `R`; `t`-genericity is the Phase-4
  follow-up. S-box specialised to `d = 5`. (ARCHITECTURE.md §5.)
- **A small C ABI shim** (`csrc/poseidon_shim.c`) marshals Lean's
  `ByteArray` to/from a raw-pointer Rust entrypoint, because `lean.h`'s
  `ByteArray` accessors are `static inline` (not linkable from Rust). Two
  `extern_lib`s (shim + cargo archive); core libs non-precompiled so only
  `poseidon_fuzz` links them. (ARCHITECTURE.md §8.)
- **Sponge `hash` external KAT deferred**: `compress` is pinned + KAT'd, but
  no upstream Poseidon2 sponge / EIP-7864 encoding exists to test `hash`
  against, so it ships with a documented convention + internal-consistency
  gate. (ARCHITECTURE.md §7.)
- **Committed KATs are generated from the oracle** and checked in (the
  `Kat.lean` analogue of `LeanSha256`'s generated `Nist.lean`); the pinned
  constants live in `scripts/poseidon2_bn256.json` (and `…_bls12.json`).
- **`LeanPoseidonProofs` is standalone, not in the umbrella `[[require]]`**
  (the original plan added it). Keeping it out of the umbrella isolates the
  entire mathlib dependency to that one package and its one CI job, so the
  root build and every other gate stay mathlib-free. This strengthens the
  isolation goal. (ARCHITECTURE.md §11.)
