# SizzLean: Manual

A user's guide to writing code against SizzLean.

## Contents

1. [Write the spec once, pick the backend later](#write-the-spec-once-pick-the-backend-later)
2. [Defining your own containers](#defining-your-own-containers)
3. [Hash-tree roots](#hash-tree-roots)
4. [Field reads and updates](#field-reads-and-updates)
5. [Proving things about your spec](#proving-things-about-your-spec)
6. [Running the tests](#running-the-tests)
7. [Importing the library](#importing-the-library)
8. [API reference](#api-reference)

## Write the spec once, pick the backend later

SizzLean's user surface is **`SSZ.Box H T`**, one type that
wraps any SSZ value `T` and lets you pick the *cache flavour*
(cached for production, uncached for proofs) and the *hasher*
(`Sha256` FFI by default, `Sha256Spec` for kernel-reducible
proofs, or any other `Hasher` instance) at the call site.

Write your spec generic in `SSZ.Box H T`; the same source code
serves the production path and the proof path. No duplicated
logic between the two.

### Worked example

A consensus-spec-shaped container:

```lean
structure Fork where
  previousVersion : Vector UInt8 4
  currentVersion  : Vector UInt8 4
  epoch           : UInt64
deriving SSZRepr
```

A small state-transition function on it, generic in the cache
flavour and in the hasher:

```lean
def bumpEpoch {H : Type} [Hasher H] (f : SSZ.Box H Fork) (newEpoch : UInt64) :
    SSZ.Box H Fork :=
  sszUpdate f with epoch := newEpoch
```

That's it, one function body. Drive it four ways depending on
what you need:

```lean
def f0 : Fork := { previousVersion := Vector.replicate 4 0x11
                   currentVersion  := Vector.replicate 4 0x22
                   epoch           := 5 }

-- Production: cached, FFI SHA-256 — fast root reads
#eval (bumpEpoch (SSZ.FastBox f0) 42).hashTreeRoot

-- Proof: uncached, FFI SHA-256 — close goals with `rfl` on
-- the view, `native_decide` on the root bytes
example :
    (bumpEpoch (SSZ.PureBox f0) 42).view = { f0 with epoch := 42 } := by
  rfl
```

For full control, including swapping in a pure-Lean hasher for
kernel-reducible proofs of concrete root bytes, or a future
post-quantum hasher, there are hasher-explicit constructors:

```lean
-- Cached, with a chosen hasher (here the pure-Lean SHA-256
-- reference). Same generic `bumpEpoch` — only the wrap differs.
#eval (bumpEpoch (SSZ.CachedBox Sha256Spec f0) 42).hashTreeRoot

-- Uncached, with a chosen hasher. Now the whole pipeline
-- (deserialise, update, root) reduces in the Lean kernel without
-- a single FFI call — `decide` works without any compiler axiom.
example :
    (bumpEpoch (SSZ.UncachedBox Sha256Spec f0) 42).hashTreeRoot
      = (SSZ.UncachedBox Sha256Spec ({ f0 with epoch := 42 } : Fork)).hashTreeRoot := by
  rfl
```

The *same* `bumpEpoch` is called every time. The only thing that
changes is the wrap at the call site.

### Two axes: flavour and hasher

Every call site picks one option on each of two independent
axes.

**Flavour**: cached vs uncached:

| | cached (`SSZ.FastBox` / `SSZ.CachedBox`) | uncached (`SSZ.PureBox` / `SSZ.UncachedBox`) |
|---|---|---|
| Use it for | running real code | writing theorems and proofs |
| Updates after the first one | O(path from the changed field to the root) | trivial struct rewrite |
| Reading the root | O(1), pre-computed, cached | recomputed each call |

In a production pipeline you wrap with the cached flavour once,
then run many `sszUpdate`s on the result, the cache pays for
itself across the second and subsequent root computations. In a
proof you wrap with the uncached flavour because you want every
`hashTreeRoot` call to be transparent to the kernel; closing a
theorem with `rfl` or `decide` is then routine.

**Hasher**: `Sha256` (default, FFI) vs anything else:

| Hasher | When to pick it |
|---|---|
| `Sha256` (default, what `SSZ.FastBox v` / `SSZ.PureBox v` use) | running real code; proofs about concrete root bytes via `native_decide` (one compiler axiom per call) |
| `Sha256Spec` (pure-Lean reference) | proofs where you want hashes to reduce *in the kernel*, with no compiler axiom, close goals with plain `decide` (or `rfl` when both sides hash the same buffers symbolically) |
| any future `Hasher` instance (e.g. Poseidon2) | adopt by writing your spec generic in `H` today; only the wrap at the call site changes when the new hasher arrives |

You don't have to choose globally on either axis. The same spec
body, `bumpEpoch` above, accepts every combination, and
switching is one expression at the call site.

## Defining your own containers

Containers are Lean structures with `deriving SSZRepr`:

```lean
structure Validator where
  pubkey                       : Vector UInt8 48
  withdrawalCredentials        : Vector UInt8 32
  effectiveBalance             : UInt64
  slashed                      : Bool
  activationEligibilityEpoch   : UInt64
  activationEpoch              : UInt64
  exitEpoch                    : UInt64
  withdrawableEpoch            : UInt64
deriving SSZRepr
```

`deriving SSZRepr` is the entire ceremony. From it you get:

* Full compatibility with `SSZ.Box` and the `sszUpdate` / `sszGet`
  macros for reads, writes, root reads, and serialisation.
* The three central correctness theorems (round-trip,
  non-malleability, size bound).
* The underlying spec functions
  (`SSZ.serialize` / `SSZ.deserialize` / `SSZ.hashTreeRoot`), you
  use these only at the IO boundary: serialising to bytes for
  the wire, or deserialising incoming bytes back into a Lean
  value before wrapping in `SSZ.Box`.

Field types must themselves have `SSZRepr` instances. Out of the
box that covers: `UInt8/16/32/64`, `Bool`, `Vector T N`,
`SSZList T cap`, `Bitvector N`, `Bitlist N`, and any other
`structure … deriving SSZRepr` you've defined yourself.

Preset-parameterised containers (those whose layout depends on
`MAX_VALIDATORS_PER_COMMITTEE` etc.) use the
`ssz_struct_for_presets` macro from the sister `LeanEthCS`
package rather than a plain `structure`, see the consensus-spec
containers in [`LeanEthCS/Forks/`](../LeanEthCS/LeanEthCS/Forks/)
for the pattern.

## Hash-tree roots

Read the 32-byte hash-tree root from any `SSZ.Box` via the
`.hashTreeRoot` projection. The cached flavour returns a
pre-computed root in O(1); the uncached flavour re-runs the spec
each call (kernel-reducible).

```lean
-- On a cached box — reads the cached root, O(1)
(SSZ.FastBox v).hashTreeRoot

-- On an uncached box — runs the spec each call, kernel-reducible
(SSZ.PureBox v).hashTreeRoot
```

For comparing a computed root against a concrete byte string in
a theorem (e.g. "this state has root `0xAB…`"), see
[Proving things about your spec](#proving-things-about-your-spec)
below for the right tactic.

## Field reads and updates

Reads and writes on a boxed SSZ value go through a pair of
macros, `sszGet` for reads and `sszUpdate` for writes, so user
code never has to name the internal `.view` projection. Both
share the same dotted-and-indexed path syntax, so the read and
the write of a given field read identically apart from the
keyword and the `:= value` clause:

```lean
let e  := sszGet    b epoch                  -- read
let b' := sszUpdate b with epoch := e + 1    -- write
```

### `sszGet`: reads

`sszGet base path` expands to `base.view.path` purely
syntactically, so `rfl` / `decide` / `simp` proofs about reads
close exactly as if the projection chain were written by hand.

```lean
sszGet b epoch                          -- flat field
sszGet b header.slot                    -- nested field
sszGet b validators[i]                  -- vector index
sszGet b validators[i].effectiveBalance -- index + field
```

Reads bypass the cache entirely (they only consult the
value-level `view`), so the cached and uncached flavours give
identical read behaviour.

### `sszUpdate`: writes

The single update entry point. Accepts any `SSZ.Box`-wrapped
value, whether produced by `SSZ.FastBox`, `SSZ.PureBox`,
`SSZ.CachedBox`, or `SSZ.UncachedBox`, or threaded in as a
generic `SSZ.Box H T` parameter. Same syntax, the right update
strategy fires automatically:

```lean
-- Single-field update
let f' := sszUpdate f with epoch := 42

-- Multi-field update — overlapping path prefixes are rehashed
-- only once
let f' := sszUpdate f with
  epoch           := 42,
  currentVersion  := Vector.replicate 4 0xff

-- Indexed update on a vector / list field
let s' := sszUpdate s with
  validators[i].effectiveBalance := newBalance
```

The flavour of the input is preserved across updates: an
`SSZ.FastBox`-built value stays Fast through every `sszUpdate`;
the same for `SSZ.PureBox`.

**Cross-statement batching is automatic.** On the cached side,
each `sszUpdate` statement accumulates into a pending overlay
rather than walking the Merkle spine on the spot. The spine
walk happens at the next root read. So a chain

```lean
let s := sszUpdate s with x := 1
let s := sszUpdate s with y := 2
let s := sszUpdate s with z := 3
-- one root read here
let root := s.hashTreeRoot
```

produces *one* spine walk at the read, not three. The uncached
flavour emits struct rewrites with no pending state, so `rfl` /
`decide` proofs reduce identically.

### Serialising and deserialising

`SSZ.Box` carries the spec serialiser through `.serialize`:

```lean
let bytes := (SSZ.FastBox f0).serialize
```

Each smart constructor has a matching `.deserialize` static
method that reads wire bytes directly into a Box. The pair reads
symmetrically: bytes go out via `box.serialize`, come back in
via `SSZ.FastBox.deserialize`:

```lean
def roundtrip (bytes : ByteArray) : Except SSZError ByteArray := do
  let box     ← SSZ.FastBox.deserialize (T := Fork) bytes
  let updated := sszUpdate box with epoch := 99
  return updated.serialize
```

`SSZ.FastBox.deserialize` returns
`Except SSZError (SSZ.Box Sha256 T)`. The error propagates
through if the buffer is malformed, matching `SSZ.deserialize`'s
shape on plain `T`.

The `(T := Fork)` annotation tells the elaborator which
container's `SSZRepr` to dispatch through. If the target type
is already constrained by the surrounding context (a typed
parameter, a function return type), the annotation isn't
needed.

### Gating round-trips at build time

A natural smoke test for an integration is to assert
`deserialize (serialize x) = .ok x` at compile time via
`native_decide`, so the build fails if the round-trip breaks:

```lean
-- ⚠️ This does NOT compile.
example : SSZ.deserialize (SSZ.serialize myPair) = .ok myPair := by
  native_decide
```

This fails to elaborate with `failed to synthesize Decidable (…
= Except.ok …)`. The reason is that `SSZ.deserialize` returns
`Except SSZError T`, and core Lean does not ship a
`DecidableEq (Except ε α)` instance. Even when `ε` and `α` are
both `DecidableEq`, the equality on `Except` is not
auto-derivable. So `native_decide` cannot find a `Decidable`
instance for the goal.

Three idioms work:

1. **`SSZ.roundtrip` propositional proof**: closes the
   equation as a proof term, not by computation, so no
   `Decidable` instance is required. The shape is what
   SizzLean's internal tests use
   (`packages/SizzLean/SizzLeanTests/ReprExamples.lean`):

   ```lean
   example (p : Pair) : SSZ.deserialize (SSZ.serialize p) = .ok p :=
     SSZ.roundtrip
       (.containerFixed (.cons .uintN64 rfl (.cons .uintN32 rfl .nil))) p
   ```

   The trade-off: you supply the `BasicSupported`-shape witness
   by hand (the `.containerFixed …` term). For ad-hoc smoke
   tests, this is more typing than most users want.

2. **`Bool`-shaped predicate**: convert the round-trip to a
   computation that returns `Bool`, then gate on `= true`. `Bool`
   equality is trivially `Decidable`, so `native_decide` evaluates
   the whole thing at build time:

   ```lean
   def roundTripsOk : Bool :=
     match SSZ.deserialize (T := Pair) (SSZ.serialize myPair) with
     | .ok p    => p.a == myPair.a && p.b == myPair.b
     | .error _ => false

   example : roundTripsOk = true := by native_decide
   ```

   Concise, no `BasicSupported` witness needed. The check is
   structural-equal on each field. If you add a field later
   you need to extend the comparison.

3. **Trust the library's own gates**: `lake build SizzLeanTests`
   runs `SSZ.roundtrip` over every `BasicSupported` shape on the
   built-in types and the example containers in `ReprExamples.lean`.
   The three central theorems
   (`SSZ.decode_encode` / `SSZ.serialize_injective` /
   `SSZ.encode_size_le_max`) are proved universally over
   `SSZType.BasicSupported`, so the round-trip property is
   already a theorem of the library for every container whose
   shape sits in `BasicSupported`, with no per-container assertion
   needed in your downstream code unless you want the build to
   break on your specific container's wire layout.

Prefer (2) for one-off smoke tests; (1) when you want a real
theorem statement in your downstream code; (3) when you don't
need a per-container assertion at all.

## Proving things about your spec

Four standard idioms cover almost every goal you'll write that
involves `hashTreeRoot`. Pick by what the goal needs:

| Goal shape | Tactic | Notes |
|---|---|---|
| Symbolic state-transition equality, both sides hash the same buffers; no concrete bytes needed | `rfl` / `simp` / `unfold` | no extra trust commitment |
| FFI-hashed term must reduce to concrete bytes (e.g. *"this state's root is `0xAB…`"*) | `native_decide` | adds the standard `Lean.ofReduceBool` compiler axiom |
| FFI-hashed term you want to manipulate symbolically before evaluating | rewrite with `sha256Hash_eq_spec` / `sha256Combine_eq_spec`, then `native_decide` | cites the two named FFI ≡ pure-Lean equivalence axioms, both auditable by name |
| Pure-Lean hashed term (built via `SSZ.UncachedBox Sha256Spec` or `SSZ.CachedBox Sha256Spec`) → concrete bytes | `decide` (kernel reduction) | no compiler axiom, no FFI; slower but maximum trust |

Rule of thumb: **use `native_decide` whenever a goal needs an
FFI hash to reduce to bytes**; use `rfl` when both sides hash the
same buffers symbolically. Use plain `decide` for non-hash
decidable goals (Nat comparisons, structural enums, finite
bitvector reasoning), those don't need any compiler axiom.

When you reach for the FFI-equivalence axioms in case (3),
document why in the theorem's docstring. They're a real trust
commitment, and a future reader inspecting `#axioms` should find
context for which empirical assumption is being relied on.

## Running the tests

SizzLean ships three test surfaces. All are driven from the
top-level `just` interface.

### Library-internal property tests (`just test-ssz`)

`native_decide`-backed examples covering SHA-256 vectors, hasher
equivalence, randomised `setAt`, cache coherence on example
containers, and `sszUpdate` cases. Each fires at build time, so a
green build is a passed test suite.

```bash
just test-ssz
```

Fast, under a minute on a warm cache.

### Full NIST CAVP SHA-256 vectors (`just test-sha256`)

The 129 byte-oriented CAVP vectors (65 ShortMsg + 64 LongMsg)
fired as `native_decide` assertions against the pure-Lean
SHA-256 reference. Lives in its own lib because the full sweep
takes ~108 s; smaller anchor gates still fire on the default
build.

```bash
just test-sha256
```

### Upstream `ethereum/consensus-spec-tests` vectors

Drives a CLI tool against the official upstream archives, with a
live tqdm progress bar showing per-case throughput.

```bash
# Generic SSZ wire-format tests (uints, vectors, bitlist, …).
# Quick sample by default:
just official-ssz-vector-tests

# Full generic sweep — 1865 / 1865 cases:
just official-ssz-vector-tests-generic-full

# Per-fork consensus-container tests (BeaconState, attestations, …).
# Quick sample across all forks Phase 0 → Fulu:
just official-ssz-vector-tests-static

# Full static sweep, minimal preset, every fork — 38991 / 38991 cases:
just official-ssz-vector-tests-static-full

# Mainnet preset — heavy; run before a release:
just official-ssz-vector-tests-static-mainnet

# Focused subset by shape glob:
just official-ssz-vector-tests-include 'generic:uints/*'

# Everything from the upstream corpus (generic full + static
# minimal full):
just official-ssz-vector-tests-all
```

First run downloads + extracts the upstream archive (~hundreds
of MB) into `~/.cache/sizzlean/`. Subsequent runs hit the cache.

The Python venv (with `cramjam`, `tqdm`, `PyYAML`) is created
by `just setup-python` once.

### Everything local (`just test`)

```bash
just test
```

Runs `test-sha256`, `test-ssz`, and `test-eth` (which is just
`lake build LeanEthCS`, where every `deriving SSZRepr` in the
consensus-spec containers is a compile-time gate). The
upstream-vector recipes are *not* in `just test`, they're
opt-in because each requires downloaded archives and runs
against external data.

## Importing the library

One import line at the top of your file gives you the full
user-facing surface:

* **The Box type and its four smart constructors**:
  `SSZ.Box`, `SSZ.FastBox` / `SSZ.PureBox` (Sha256-pinned),
  `SSZ.CachedBox` / `SSZ.UncachedBox` (hasher-explicit).
* **Reads and updates**: the `sszGet` and `sszUpdate` macros.
* **Container deriving**: `deriving SSZRepr` on your own
  structures.
* **Field-type instances**: `Vector`, `SSZList`, `Bitvector`,
  `Bitlist`.
* **Hasher tags**: `Sha256` (FFI), `Sha256Spec` (pure-Lean).
* **IO-boundary functions**: `SSZ.deserialize`, `SSZError`.

All available from:

```lean
import SizzLean
```

The consensus-spec containers themselves live in the sibling
`LeanEthCS` package; add an `[[require]]` for it in your
`lakefile.toml` and import what you need from
`LeanEthCS.Forks.<Fork>.<Container>`.

## API reference

The full user-facing surface, organised by what you reach for it
for. Examples assume the `Fork` container from the worked example
earlier in the manual and the `import SizzLean` line in scope.

Three sections:

1. **[Creating containers](#creating-containers)**: the building
   blocks for defining your own SSZ-encodable types.
2. **[The Box interface](#the-box-interface)**: the single
   user-facing entry point: constructors, the read / write /
   root / serialise operations, and the IO-boundary
   deserialiser.
3. **[Miscellaneous](#miscellaneous)**: hasher tags and the
   FFI-equivalence axioms; cross-cutting infrastructure.

### Creating containers

The pieces you compose into your own SSZ types.

#### `SSZRepr`

Typeclass that turns a Lean type into an SSZ-encodable type. You
rarely write an instance by hand, `deriving SSZRepr` synthesises
it, but you do mention `[SSZRepr T]` in generic-`T` binders.

```lean
def encode {H T : Type} [Hasher H] [SSZRepr T] (b : SSZ.Box H T) : ByteArray :=
  b.serialize
```

#### `deriving SSZRepr`

One-line derive that synthesises `SSZRepr` for any structure
whose fields all have `SSZRepr` instances themselves. From the
synthesised instance you get full compatibility with `SSZ.Box`,
`sszUpdate`, `sszGet`, `.hashTreeRoot`, and `.serialize`.

```lean
structure Validator where
  pubkey : Vector UInt8 48
  effectiveBalance : UInt64
deriving SSZRepr
```

#### `SSZList α cap`

Variable-length list of `α` with maximum length `cap`.
Implemented as `{ xs : Array α // xs.size ≤ cap }`, Lean's array
plus a size proof.

```lean
structure Batch where
  validators : SSZList Validator 1024
deriving SSZRepr
```

#### `SSZList.get!`, `SSZList.set!`, `SSZList.size`

Element access / replacement / length. `get!` returns `default`
on out-of-bounds; `set!` is a no-op on out-of-bounds and
preserves the cap proof either way. `size` is the runtime
length.

```lean
let v   := xs.get! 3
let xs' := xs.set! 3 newV
let n   := xs.size
```

#### `Bitvector n`

Fixed-length bit array of exactly `n` bits.

```lean
structure Aggregate where
  attestations : Bitvector 256
deriving SSZRepr
```

#### `Bitlist cap`

Variable-length bit array with maximum length `cap`. Distinct
from `SSZList Bool cap` because the SSZ wire format packs bits
into bytes and uses a trailing-`1` delimiter.

```lean
structure SyncCommitteeContribution where
  aggregationBits : Bitlist 128
deriving SSZRepr
```

### The Box interface

The single user-facing entry point. All operations on an SSZ
value go through `SSZ.Box H T`: construct with one of the four
smart constructors, then read with `sszGet`, write with
`sszUpdate`, take the root with `.hashTreeRoot`, and serialise
with `.serialize`.

#### `SSZ.Box`

Closed inductive over the two cache flavours (cached + uncached).
Used as a parameter type in spec functions that should accept
either flavour at the call site. Constructors are internal,
build a `Box` via one of the four smart constructors below.

```lean
def bumpEpoch {H : Type} [Hasher H]
    (f : SSZ.Box H Fork) (n : UInt64) : SSZ.Box H Fork :=
  sszUpdate f with epoch := n
```

#### `SSZ.FastBox`

Sha256-pinned cached smart constructor. The production default:
FFI-hashed, O(1) root reads, O(log N) updates.

```lean
let b := SSZ.FastBox f0
#eval b.hashTreeRoot
```

#### `SSZ.PureBox`

Sha256-pinned uncached smart constructor. The proof-side
companion to `FastBox` when one body must serve both call sites.
Each `hashTreeRoot` re-runs the spec, so there's no cache
invariant to thread through theorems.

```lean
let b := SSZ.PureBox f0
example : b.view = f0 := by rfl
```

#### `SSZ.CachedBox`

Hasher-explicit cached smart constructor, like `FastBox` but
the caller picks the `Hasher`. The right entry point when a
spec function is written generic in `H` and you want the cached
flavour with a non-default hasher.

```lean
#eval (SSZ.CachedBox Sha256Spec f0).hashTreeRoot
```

#### `SSZ.UncachedBox`

Hasher-explicit uncached smart constructor, like `PureBox` but
the caller picks the `Hasher`. With `Sha256Spec` the whole
hashing pipeline reduces in the kernel without an FFI hop.

```lean
example :
    (SSZ.UncachedBox Sha256Spec f0).hashTreeRoot
      = (SSZ.UncachedBox Sha256Spec f0).hashTreeRoot := by rfl
```

#### `sszGet`

Macro for field reads, the read-side companion of `sszUpdate`,
hiding the internal `.view` projection. Path syntax mirrors
`sszUpdate` exactly: head field, then any number of `.field` or
`[i]` segments.

```lean
sszGet b epoch                          -- flat field
sszGet b header.slot                    -- nested field
sszGet b validators[i]                  -- vector index
sszGet b validators[i].effectiveBalance -- index + field
```

Expands purely syntactically to `b.view.<path>`, so `rfl` /
`decide` / `simp` proofs about reads close exactly as if you had
written the projection chain by hand, the macro is invisible
to Lean's kernel.

#### `sszUpdate`

Macro for field updates. Accepts any `SSZ.Box`-wrapped value and
emits the right update path automatically. Merkle-aware partial
rehash on cached values, trivial struct rewrite on uncached
values. Supports single-field, multi-field (overlapping paths
rehashed once), and indexed-field updates on vectors/lists.

```lean
-- Single
let f' := sszUpdate s with epoch := 42

-- Multi — overlapping path prefixes rehash once
let f' := sszUpdate s with
  epoch          := 42,
  currentVersion := Vector.replicate 4 0xff

-- Indexed
let s' := sszUpdate state with
  validators[i].effectiveBalance := newBalance
```

#### `.hashTreeRoot`

Reads the hash-tree root of a `Box`. The cached arm returns the
pre-computed root in O(1); the uncached arm re-runs the spec.

```lean
#eval (SSZ.FastBox f0).hashTreeRoot
#eval (SSZ.PureBox f0).hashTreeRoot
```

#### `.serialize`

Encodes a `Box` to its SSZ wire-format bytes. Always succeeds,
SSZ encoding is total. Works identically on cached and uncached
flavours.

```lean
#eval (SSZ.FastBox f0).serialize
```

#### `.view`

Lower-level escape hatch, projects the underlying Lean value
out of a `Box`. Works on any of the four `*Box` flavours via
dot notation. Use this when a lemma or external function takes
plain `T` and you need to feed it the unwrapped value directly;
for ordinary reads, reach for `sszGet` instead.

```lean
#check (SSZ.FastBox f0).view   -- : Fork
```

#### `SSZ.FastBox.deserialize`

The IO-side companion to `SSZ.FastBox v`. Takes wire bytes and
produces `Except SSZError (SSZ.Box Sha256 T)`, reading
symmetrically with `.serialize` on the way out.

```lean
SSZ.FastBox.deserialize (T := Fork) bytes
```

A matching `.deserialize` exists for each of the other smart
constructors: `SSZ.PureBox.deserialize`,
`SSZ.CachedBox.deserialize H`, and `SSZ.UncachedBox.deserialize H`,
all with the same `Except SSZError (SSZ.Box _ T)` shape. Reach for
those only when the call site genuinely needs a non-production
flavour or a non-default hasher.

The underlying `SSZ.deserialize : ByteArray → Except SSZError T`
spec function is still available for cases where you need a
plain `T` (e.g. feeding a lemma that operates on bare values),
but `SSZ.FastBox.deserialize` is the recommended entry point for
normal code.

#### `SSZError`

Sum of deserialise-error shapes (truncation, oversize, bad
offsets, etc.). Pattern-match on it for fine-grained handling
or just `repr` it for diagnostics.

```lean
def explain : SSZError → String := fun e => s!"deserialize: {repr e}"
```

### Miscellaneous

Cross-cutting infrastructure used through the Box interface,
hasher tags and the FFI ≡ pure-Lean equivalence axioms.

#### `Hasher`

Typeclass with the two methods (`hash`, `combine`) every SSZ
hashing site goes through. You rarely instantiate it, you reach
for a tag like `Sha256`, but generic spec functions take
`[Hasher H]` to stay hasher-flexible.

```lean
def myBoxedFork {H : Type} [Hasher H] (f : Fork) : SSZ.Box H Fork :=
  SSZ.CachedBox H f
```

#### `Sha256`

Empty `inductive` tag whose `Hasher` instance delegates to the
FFI SHA-256 shim (OpenSSL). Production default. Opaque to the
Lean kernel. Kernel-`decide` can't reduce its hashes, so use
`native_decide` when concrete bytes are required in a proof.

```lean
#eval (SSZ.CachedBox Sha256 f0).hashTreeRoot
```

#### `Sha256Spec`

Empty `inductive` tag whose `Hasher` instance delegates to the
pure-Lean SHA-256 reference (from the sibling `LeanSha256`
library). Kernel-reducible. `decide` works on its outputs
without a compiler axiom; the trade-off is the kernel has to
walk the SHA-256 compression function each call (slower).

```lean
example : (SSZ.UncachedBox Sha256Spec f0).hashTreeRoot = <concrete-bytes> := by
  decide   -- no `native_decide` needed; no compiler axiom
```

#### `sha256Hash_eq_spec`, `sha256Combine_eq_spec`

Two named axioms asserting that the FFI primitives
(`sha256Hash`, `sha256Combine`) agree pointwise with the pure-
Lean reference (`LeanSha256.hash`, `LeanSha256.combine`). Use as
rewrite targets when a proof needs to manipulate an FFI-hashed
term symbolically before evaluating with `native_decide`.

```lean
example (b : ByteArray) :
    sha256Hash b = LeanSha256.hash b := by
  rw [sha256Hash_eq_spec]
```
