# Etheorem: Agent Notes

A Lean 4 project for Ethereum consensus-spec types and SSZ
([Simple Serialize](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md)).
Goal: a faithful, formally verifiable encoder / decoder / Merkleization for
SSZ types plus the consensus-spec container surface (Phase0 → Gloas).

The Lake package is `Etheorem`; it ships several libraries:
**`LeanSha256`** (pure-Lean SHA-256), the **`LeanHazmat`** FFI crypto
families (SHA-256 / BLS / KZG), **`SizzLean`** (the SSZ library),
**`EthCLLib`** + **`EthCLSpecs`** (the consensus-spec framework and the
Fulu / Gloas fork bodies built on it, which declare their containers
in-spec), and **`LeanPoseidon`**
(a pure-Lean Poseidon2 hash, a standalone island parallel to `LeanSha256`,
it depends on nothing in the monorepo and nothing depends on it yet;
see [`packages/LeanPoseidon/docs/ARCHITECTURE.md`](packages/LeanPoseidon/docs/ARCHITECTURE.md)).
Mentions of "SizzLean" elsewhere in this file refer to the SSZ library
specifically, not to the project as a whole.

The upstream repository is <https://github.com/etheorem/etheorem>.
Use that when issuing `gh` commands or constructing PR / issue
links.

## Principles

These are not new ideas. They are the standard names for what good Lean
libraries already do. They show up below as concrete conventions; this section
is the *why* so edge cases can be judged on principle, not by pattern-matching.

- **Literate by default.** SSZ-in-Lean sits at a small intersection: most
  readers will know one side but not the other, so comments should teach the
  language and the spec as the file unfolds, not merely label what's there.
  Use module docstrings (`/-! … -/`) to frame each file against the spec
  section it implements, declaration docstrings (`/-- … -/`) for the *why*
  of every public definition, and `example` blocks for usage the
  typechecker keeps honest. Annotate non-obvious Lean idioms
  (`Decidable.decide`, explicit `motive`, custom `where` clauses) the first
  time they appear in a module, not the fifth; same for spec terms a
  Lean-fluent reader won't recognize. The cost is paid once at write time;
  the dividend compounds with every new contributor.

  Explain non-obvious *inferences* with the same rigor as non-obvious idioms.
  Lean infers a lot, types, terms, instances, motives, and most of it is
  unremarkable, but some of it is load-bearing and not recoverable from
  reading the surface code: `let x : ConcreteType := y` coercions that force
  defeq reduction across a mutual-block boundary; dependent pattern
  destructures (`vs.1` / `vs.2` on a `Prod`-chain that came from unfolding
  an `interp` arm); named-argument typeclass synthesis (`(H := H)` when the
  parameter is a phantom tag the methods don't consume); the inferred
  `Fin n` parameter of a `Vector.ofFn` lambda; the synthesised bound proof
  inside `b[i]'h`. When the inference is the load-bearing thing a reader
  needs to follow, name what Lean inferred and *why* in a one-line comment,
  don't restate types the RHS already makes obvious. Type-annotate
  intermediate `let` / `have` bindings whose type changes the meaning of
  subsequent code (e.g. `let xs : List t.interp := v.toList`); leave
  inference for the cases that read cleanly without help.
- **Single Responsibility (SRP).** Each file, namespace, and definition does
  one thing. If `SizzLean/Encoding.lean` ends up holding serialization,
  deserialization, *and* merkleization for every type, split it. A 1000-line
  module is the same smell as a 1000-line function, just at a different scale.
- **Open/Closed (OCP).** Extend by adding new code, not by editing existing
  code. New SSZ types should land as new instances of an `SSZ` typeclass,
  not as another arm of a giant `match` in a central encoder. If adding
  `Bitlist` requires editing `Vector`, the abstraction is wrong.
- **Dependency Inversion (DIP).** Code against typeclass interfaces, not
  concrete representations. Tests for a `Container` should depend on the
  `SSZ` interface (round-trip, root), not on the byte layout of one specific
  encoder. `variable {α : Type} [SSZ α]` over `(x : SpecificStruct)`.
- **DRY: one canonical home per fact.** A type's field list is defined once;
  encode / decode / `hashTreeRoot` instances are `deriving`d or generated
  from that single source. Wire-format constants (`uint64` width, chunk size,
  Merkle padding) live in one module and are imported, not re-typed.
- **No hidden coupling.** Lean has no mutable globals, but `set_option` and
  `open` at file scope leak into every importer. Keep `open` and option
  toggles tight to the section that needs them. Don't rely on import order
  for correctness.
- **Configure, don't integrate.** `lakefile.toml` is declarative, keep it
  that way. If a build step starts to feel like a shell script glued onto
  Lake, push it into Lake's API or a small Lean script invoked via
  `lake env lean --run …`, not ad-hoc Make/bash.
- **Spec is the source of truth.** Behavior comes from the consensus-specs
  SSZ doc and the official test vectors. When other implementations disagree
  with the spec, the spec wins; we record the discrepancy, we don't paper
  over it.
- **Lean on Lean.** Prefer what the language gives you over hand-rolled
  equivalents: `deriving` instances, `simp` lemmas, `Decidable` + `decide`
  for finite goals, structural recursion over `partial def`. Reach for
  `batteries` before re-implementing a list utility; reach for `mathlib`
  only when the math actually demands it.
- **Strict checking is a force multiplier.** Lean's type system catches an
  enormous class of bugs *for free*, but only if you don't disarm it.
  Prefer `set_option autoImplicit false` per file; treat `sorry`, unused
  variables, and linter warnings as build failures in spirit even when CI
  doesn't yet enforce it. The cost of strictness is paid once; the cost of
  a missed implicit is paid forever.
- **Stringly-typed is a smell.** Tag SSZ kinds with an inductive
  (`SSZType.uint64 | .vector … | .container …`), not with `String`. If
  you find yourself comparing strings in load-bearing code, the type is
  asking to be promoted.

These map onto the usual references: Fowler's *Refactoring* (smells), Hunt &
Thomas's *The Pragmatic Programmer* (DRY, orthogonality), Martin's
*Clean Code* / *Clean Architecture* (SRP, DIP), and Meyer's *Object-Oriented
Software Construction* (Open/Closed). They are adapted to a dependently typed,
proof-carrying setting where typeclasses do most of the work that interfaces
and patterns do elsewhere.

## Layout

Lake monorepo layout. Four subpackages under `packages/`, each
with its own lakefile; an umbrella `lakefile.toml` at the root
coordinates them via `[[require]]` blocks.

```
.
├── lakefile.toml                # Umbrella (TOML, declarative)
├── lean-toolchain               # Pinned toolchain; CI reads this. Bump deliberately.
├── README.md / CLAUDE.md       # Repo-wide overview + conventions
├── docs/                       # Repo-wide design docs (monorepo-arch.md)
├── scripts/                     # requirements.txt (conformance-harness Python deps)
├── packages/
│   ├── LeanSha256/              # Pure-Lean SHA-256 reference; no FFI.
│   │   ├── lakefile.toml
│   │   ├── LeanSha256.lean / LeanSha256/ / cavp/ / Tests/ / README.md
│   ├── SizzLean/                # SSZ library + cache + FFI hasher.
│   │   ├── lakefile.lean        # Procedural — needed for the C shim target.
│   │   ├── csrc/sha256_shim.c
│   │   ├── docs/                # ARCHITECTURE.md, PLAN.md, research/ (SizzLean-scoped)
│   │   ├── SizzLean.lean / SizzLean/ / Tests/ / README.md
│   ├── EthCLLib/                # Consensus-spec framework / DSL (fork forms, effect monad, container front-end).
│   │   ├── lakefile.toml
│   │   ├── EthCLLib.lean / EthCLLib/ / Tests/
│   ├── EthCLSpecs/              # Fulu / Gloas fork bodies + the pyspec_server conformance runner.
│   │   ├── lakefile.toml
│   │   ├── EthCLSpecs.lean / EthCLSpecs/ / PySpecTests/ / docs/ / README.md
│   └── LeanPoseidon/            # Pure-Lean Poseidon2 (BN254 t=3); standalone island.
│       ├── lakefile.lean        # Procedural — C ABI shim + cargo (zkhash) extern_libs.
│       ├── csrc/poseidon_shim.c / rust-oracle/  # test-only differential oracle
│       ├── docs/                # ARCHITECTURE.md, PLAN.md (LeanPoseidon-scoped)
│       ├── LeanPoseidon.lean / LeanPoseidon/ / LeanPoseidonTests/ / README.md
└── .github/workflows/           # `leanprover/lean-action@v1` runs `lake build`.
```

The umbrella package is named `Etheorem`. The SSZ library
library inside it is named `SizzLean`. When this file mentions
"SizzLean" elsewhere, that's the library, not the project as a
whole.

The SizzLean library's design docs live under
[`packages/SizzLean/docs/`](packages/SizzLean/docs/):
[`ARCHITECTURE.md`](packages/SizzLean/docs/ARCHITECTURE.md) binds
the SSZ-library design (the `SSZType` universe, `SSZRepr`
typeclass + deriving handler, cached Merkle tree, FFI SHA-256,
trust boundary, the per-subpackage layout under `packages/`),
[`PLAN.md`](packages/SizzLean/docs/PLAN.md) sequences SizzLean's
work into stages with concrete deliverables and acceptance
criteria. [`docs/monorepo-arch.md`](docs/monorepo-arch.md)
documents how the monorepo's three-subpackage shape works.
This file (CLAUDE.md) is binding on style, conventions, and
discipline across all subpackages; when those overlap with
architectural decisions, ARCHITECTURE.md wins on substance and
CLAUDE.md wins on form.

## Conventions

- **Module names mirror file paths.** `SizzLean/Foo/Bar.lean` ⇒ `import SizzLean.Foo.Bar`.
  Files and directories are PascalCase.
- **`import` must be the first thing in a file**, before any `/-! … -/` module
  docstring, before any `set_option`. Lean rejects imports placed later.
- **Library root re-exports.** New top-level submodules go into `SizzLean.lean`
  as `import SizzLean.Foo`. Internal-only helpers don't need to be re-exported.
- **Naming:** types, structures, inductives, namespaces → `PascalCase`;
  defs, theorems, fields, variables → `lowerCamelCase`.
- **Namespacing.** Wrap declarations in `namespace SizzLean … end SizzLean`
  (or a sub-namespace) so the public API is `SizzLean.foo`, not bare `foo`.
- **Doc comments:** `/-- … -/` on declarations, `/-! … -/` for module-level
  prose. Skip comments that just restate the code.
- **No committed `#eval` / `#check` / `#print`.** Use `example : … := by …` or
  `#guard` for assertions you want the build to enforce.
- **Tactic style:** prefer structured `by` blocks; use `<;>` and `· …` bullets
  rather than long `;`-chains. `decide` / `native_decide` are fine for finite
  goals, note `native_decide` trusts the compiler.
- **`partial def` only when termination really can't be shown.** Prefer
  structural recursion or `termination_by` + `decreasing_by`.
- **Function-body readability.** For worked before/after examples of these
  conventions applied inside a definition (paragraphing phases, naming
  intermediates, section comments, when to split), see
  [`docs/CODING_STYLE.md`](docs/CODING_STYLE.md). That file shows; this file
  states the rule.

### Proofs involving SSZ hashes

Pick the tactic by what the goal needs and which hasher tag is in
scope. The four cases:

1. **Symbolic state-transition proofs (no concrete hash bytes
   needed).** Both sides invoke the same opaque
   `Hasher.hash` / `Hasher.combine` on the same buffers, equality
   follows definitionally regardless of what bytes the hasher
   produces. Close with `rfl` / `simp` / `unfold`. `Sha256`'s
   opacity is fine; no axioms needed. **Most state-transition
   theorems live here.**

2. **Goals where a hash has to reduce to concrete bytes (FFI
   hasher).** E.g. *"this state has root `0xAB…`"*. `Sha256` is
   `@[extern] opaque`, so kernel `decide` cannot close. Default
   tactic: **`native_decide`**. Adds one `Lean.ofReduceBool`
   axiom per call; evaluates via compiled FFI; fast.

3. **Goals that want symbolic-then-computational manipulation on
   an FFI-hashed term.** Rewrite the FFI calls into their
   pure-Lean equivalents via the two named axioms in
   `Hasher/Sha256Equiv.lean` (`sha256Hash_eq_spec`,
   `sha256Combine_eq_spec`), then close with `native_decide`.
   `#axioms` cites the two equivalence axioms + the
   compiler axiom, all three named and auditable.

4. **`Sha256Spec`-flavoured goals.** Pure-Lean SHA-256 reduces in
   the kernel, use **`decide`** (no compiler axiom). Slower
   (the kernel reduces hundreds of instructions per hash block);
   reserve for theorems where compiler trust is unacceptable.

Default rule: **prefer `native_decide` over kernel `decide` when
the goal involves any `Sha256` (FFI) hashing**. For non-hash
decidable goals (Nat comparisons, structural enums, finite
bitvector reasoning), kernel `decide` is fine, no compiler
axiom needed.

When the FFI-equivalence axioms are used, document why in the
theorem's docstring, they're a real trust commitment, and a
future reader inspecting `#axioms` should see context for *which*
empirical assumption is being relied on.

## Workflow

```bash
lake build              # Build the library. Run after every change.
lake build SizzLean.X   # Build a single module.
lake clean              # Wipe .lake/build (rarely needed).
lake update             # Refresh lake-manifest.json after editing deps.
lake env lean --run …   # Run a Lean script with the package env.
```

CI (`.github/workflows/lean_action_ci.yml`) just runs `lake build` on the
pinned toolchain, keep the local build green and CI follows.

## Dependencies

One Lean dependency: **`mathlib`**, used by `LeanPoseidonProofs` alone (see
below). If you add another (e.g. `batteries`):

1. Add a `[[require]]` block to `lakefile.toml`.
2. Run `lake update` and commit the resulting `lake-manifest.json`.
3. Pin the dep's git rev, don't track a branch.

Adding mathlib is a heavy commitment (long compile, toolchain coupling). Don't
pull it in for trivia; reach for `batteries` first if a small extension suffices.
The monorepo's mathlib dependency is **`LeanPoseidonProofs`** (the Poseidon2
fast-≡-reference equivalence proof), and it is deliberately **contained**: a
*standalone* package (not in the umbrella `[[require]]`s), pinned to mathlib's
`v4.29.1` tag (an exact toolchain match, so `lake exe cache get` uses prebuilt
oleans, nothing compiles from scratch), with its own committed
`lake-manifest.json`. So mathlib never touches the SSZ chain, the
`LeanPoseidon` core, the root build, or any CI job other than the dedicated
`poseidon-proofs` one. Build it with `just test-poseidon-proofs`. See
[`packages/LeanPoseidon/docs/PLAN.md`](packages/LeanPoseidon/docs/PLAN.md) Phase 3.

`LeanPoseidon`'s differential-test oracle vendors the Rust `zkhash` crate
(pinned in `rust-oracle/Cargo.lock`); that is a **test-only, cargo-managed**
dependency confined to the `poseidon_fuzz` executable, not a Lean/Lake
dependency, and never on any shipped or proof path.

## SSZ scope (what this library will cover)

Track the [consensus-specs SSZ doc](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md)
as the source of truth. Roughly:

- Basic types: `uintN` (8/16/32/64/128/256), `Bool`.
- Composite: `Vector`, `List`, `Bitvector`, `Bitlist`, `Container`, `Union`.
- Operations: `serialize`, `deserialize`, `hash_tree_root` (merkleization).
- Test vectors from `ethereum/consensus-spec-tests` once the core types land.

When in doubt about behavior, defer to the spec and the official test vectors,
not to other implementations.

## Don'ts

- Don't edit `.lake/` or `lake-manifest.json` by hand.
- Don't add procedural Lake configuration when the declarative form
  suffices. The project's package metadata, `lean_lib` declaration,
  and dependencies stay minimal and declarative. `lakefile.lean` is
  permitted *only* for build targets the declarative form cannot
  express (C-source compilation, code generation, dynamic git
  targets). Stage 9's `sha256_shim` C build is the standing example.
  Lake doesn't support both `lakefile.toml` and `lakefile.lean`
  in one package, so when one procedural target is needed the whole
  config moves to `lakefile.lean` (kept ≤30 lines).
- Don't bump `lean-toolchain` casually, it cascades through CI and any deps.
- Don't leave `sorry` in committed code without a `TODO` and a tracking note.

## Writing Style & Structural Constraints for Documentation

Applies to comments in code and in other documentation files. Also, when writting in github issues and PRs.

### Sentence Construction (Hard Enforcement)

- **No contrastive negation or antithesis.** Never use patterns like "It's not about X, it's about Y" or "X, not Y, not Z." State the positive reality directly and cleanly, without defensive framing.

### Punctuation & Sentence Structure

- **No em-dashes for subphrases.** Never use em-dashes (—) or hyphens (-, --) to set off parenthetical thoughts, interruptions, or subphrases.
- **Use commas instead.** Set off descriptive tangents or subphrases with commas (apposition).
  - Bad: "The strategy—though risky—yielded massive results."
  - Good: "The strategy, though risky, yielded massive results."
- **Keep sentences clean.** If a subphrase needs more than two commas to execute, split it into two distinct, clean sentences instead of one complex sentence.

### Structural Rhythm & Voice

- **Vary sentence length.** Alternate between short, punchy sentences (under 5 words) and longer, flowing ones. Never write three sentences of similar length in a row.
- **No statement-explanation loops.** Do not state a fact or opinion and then spend the next sentence explaining, justifying, or restating it in other words. Every sentence must introduce new information or advance the point.
- **Active voice.** Write in the active voice. Avoid clinical, detached, or overly academic prose.

### Banned Formatting & Bookends

- **No filler openers.** Skip introductions like "Sure, here is..." or "Let's dive in." Start directly with the first relevant sentence.
- **No summary closers.** Do not write a concluding summary paragraph or use phrases like "In conclusion," "Ultimately," "In essence," or "At the end of the day." Stop writing when the content ends.

### Banned AI Vocabulary

Never use the following. Replace them with simple, plain English alternatives.

- **Verbs / transitions:** delve, utilize, leverage, facilitate, maximize, embrace, foster, emphasize, furthermore, moreover, additionally.
- **Nouns / metaphors:** tapestry, landscape, realm, arena, symphony, testament, beacon, journey, roadmap, game-changer, paradigm shift.
- **Adjectives:** robust, seamless, cutting-edge, innovative, multifaceted, crucial, pivotal, deep dive.
