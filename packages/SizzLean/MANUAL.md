# SizzLean: Manual

A user's guide to writing code against SizzLean.

## Contents

1. [Choosing a mode](#choosing-a-mode)
2. [Defining your own containers](#defining-your-own-containers)
3. [Hash-tree roots](#hash-tree-roots)
4. [Field reads and updates](#field-reads-and-updates)
5. [Proving things about your spec](#proving-things-about-your-spec)
6. [Running the tests](#running-the-tests)
7. [Importing the library](#importing-the-library)
8. [API reference](#api-reference)

## Choosing a mode

SizzLean gives you three ways to hold an SSZ value. All three
compute the same bytes and the same roots. They differ in the
type you hold and in what a root read costs.

| Mode | Type the user holds | Reads and writes | Root | Use it for |
|---|---|---|---|---|
| Plain value | `T` with `[SSZRepr T]` | `v.field`, `{ v with field := x }`, `.set!`, `.modify`, `push?` | `SSZ.hashTreeRoot H v`, full merkleization per call | spec code, proofs, small states; the CL specs use it |
| Box | `SSZ.Box H T` | `sszGet` / `sszUpdate` | `.hashTreeRoot`, flavour picked at the wrap | one source that runs cached in production and uncached in proofs |
| Cache only | `CachedSSZ H T` / `TreeBacked` | `sszGet` / `sszUpdate` | O(1) read after an O(log N) spine rehash | hot paths that root a large value many times |

The plain mode needs no type of its own: you hold the structure
that derives `SSZRepr`. It is the verified core, and the library
proves or tests the other two modes against it. Start there, and
wrap in a box or a cache only when a measured root cost asks for
it.

### The plain mode

A consensus-spec-shaped container:

```lean
structure Fork where
  previousVersion : Vector UInt8 4
  currentVersion  : Vector UInt8 4
  epoch           : UInt64
deriving SSZRepr
```

A small state transition on it. Lean's own record syntax does the
write, so the body names no SizzLean function:

```lean
def bumpEpoch (f : Fork) (e : UInt64) : Fork :=
  { f with epoch := e }
```

The root comes from `SSZ.hashTreeRoot`. Its first explicit
argument is the hasher tag:

```lean
def f0 : Fork := { previousVersion := Vector.replicate 4 0x11
                   currentVersion  := Vector.replicate 4 0x22
                   epoch           := 5 }

-- Full merkleization of the new value, FFI SHA-256.
#eval SSZ.hashTreeRoot Sha256 (bumpEpoch f0 42)

-- Both sides hash the same value, so `rfl` closes the goal
-- with no hash computed.
example :
    SSZ.hashTreeRoot Sha256 (bumpEpoch f0 42)
      = SSZ.hashTreeRoot Sha256 ({ f0 with epoch := 42 } : Fork) := by
  rfl
```

Swap `Sha256` for `Sha256Spec` and the hash runs in pure Lean:
`native_decide` still checks concrete root bytes, and the proof
then trusts no FFI, only `native_decide`'s own compiler axiom.
`decide` cannot reduce the merkleization itself; see
[Proving things about your spec](#proving-things-about-your-spec)
for the tactic each goal shape needs. The value itself does not
change.

### The box mode

The box mode wraps the value in **`SSZ.Box H T`**. The type lets
you pick the *cache flavour* (cached for production, uncached for
proofs) and the *hasher* (`Sha256` FFI by default, `Sha256Spec`
for FFI-free proofs, or any other `Hasher` instance) at
the call site. Write the spec generic in `SSZ.Box H T`, and the
same source serves the production path and the proof path.

The same transition, written against the box:

```lean
def bumpEpochBox {H : Type} [Hasher H] (f : SSZ.Box H Fork) (newEpoch : UInt64) :
    SSZ.Box H Fork :=
  sszUpdate f with epoch := newEpoch
```

Drive the one body four ways:

```lean
-- Production: cached, FFI SHA-256, fast root reads
#eval (bumpEpochBox (SSZ.FastBox f0) 42).hashTreeRoot.1

-- Proof: uncached, FFI SHA-256. Close goals with `rfl` on
-- the view, `native_decide` on the root bytes
example :
    (bumpEpochBox (SSZ.PureBox f0) 42).view = { f0 with epoch := 42 } := by
  rfl
```

For full control, including a pure-Lean hasher that keeps the FFI
out of your proofs' trusted base, or a future
post-quantum hasher, there are hasher-explicit constructors:

```lean
-- Cached, with a chosen hasher (here the pure-Lean SHA-256
-- reference). Same generic `bumpEpochBox`, only the wrap differs.
#eval (bumpEpochBox (SSZ.CachedBox Sha256Spec f0) 42).hashTreeRoot.1

-- Uncached, with a chosen hasher. The whole pipeline
-- (deserialise, update, root) runs in pure Lean, with no FFI
-- call; `native_decide` on its results adds only its own
-- compiler axiom.
example :
    (bumpEpochBox (SSZ.UncachedBox Sha256Spec f0) 42).hashTreeRoot
      = (SSZ.UncachedBox Sha256Spec ({ f0 with epoch := 42 } : Fork)).hashTreeRoot := by
  rfl
```

The *same* `bumpEpochBox` runs every time. Only the wrap at the
call site changes.

#### Two axes: flavour and hasher

Every box call site picks one option on each of two independent
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
`hashTreeRoot` call to reduce like an ordinary function of the
value. Close symbolic equalities with `rfl`, or use
`native_decide` for concrete bytes.

**Hasher**: `Sha256` (default, FFI) vs anything else:

| Hasher | When to pick it |
|---|---|
| `Sha256` (default, what `SSZ.FastBox v` / `SSZ.PureBox v` use) | running real code; proofs about concrete root bytes via `native_decide` (one compiler axiom per call, plus `sha256Combine_eq_spec` and `sha256BatchCombine_eq_spec` through the hasher instance) |
| `Sha256Spec` (pure-Lean reference) | proofs about concrete root bytes with the FFI out of the trusted base: `native_decide` adds only its own compiler axiom, no FFI-equivalence axioms (or `rfl` when both sides hash the same buffers symbolically) |
| any future `Hasher` instance (e.g. Poseidon2) | adopt by writing your spec generic in `H` today; only the wrap at the call site changes when the new hasher arrives |

The hasher axis applies to plain values too: it is the first
argument of `SSZ.hashTreeRoot`.

You don't have to choose globally on either axis. The same spec
body, `bumpEpochBox` above, accepts every combination, and
switching is one expression at the call site.

### The cache-only mode

`CachedSSZ H T` (an `abbrev` for `TreeBacked H T`, in
`SizzLean.Cache`) is the cached flavour without the box around
it. Build one with `CachedSSZ.ofValue H v`, write with
`sszUpdate`, and read the root with `CachedSSZ.hashTreeRoot`,
which returns the root and the updated cache as a pair. Use it on
a hot path that roots one large value many times and has no proof
side to serve.

```lean
def cachedRoot : ByteArray :=
  (CachedSSZ.hashTreeRoot
    (sszUpdate (CachedSSZ.ofValue Sha256 f0) with epoch := 42)).1

-- Same root as the plain mode computed above
#eval cachedRoot == SSZ.hashTreeRoot Sha256 (bumpEpoch f0 42)
-- true
```

One naming trap: after an `sszUpdate`, hold the result under the
`CachedSSZ` name before reading the root with dot notation. The
macro types its result as the internal `TreeBacked`, whose
namespace spells the reader `.hashTreeRootCached`, so a bare
`let c := sszUpdate c with …` makes `c.hashTreeRoot` fail to
resolve. Either ascribe the `let`
(`let c : CachedSSZ Sha256 Fork := sszUpdate …`), call
`CachedSSZ.hashTreeRoot c`, or use `c.hashTreeRootCached`; all
three read the same root.

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

* The full plain-value surface: `SSZ.serialize v` encodes to wire
  bytes, `SSZ.deserialize bytes` decodes them, and
  `SSZ.hashTreeRoot H v` merkleizes. Reads and writes are Lean's
  own field projections and record updates. Spec code, proofs and
  the IO boundary can all stop here.
* The three central correctness theorems (round-trip,
  non-malleability, size bound), stated on these functions.
* Full compatibility with `SSZ.Box`, `CachedSSZ` and the
  `sszUpdate` / `sszGet` macros, for when you want the cached
  modes.

```lean
let bytes := SSZ.serialize v                        -- ByteArray
let back  := SSZ.deserialize (T := Validator) bytes -- Except SSZError Validator
let root  := SSZ.hashTreeRoot Sha256 v              -- 32-byte ByteArray
```

Field types must themselves have `SSZRepr` instances. Out of the
box that covers: `UInt8/16/32/64`, `Bool`, `Vector T N`,
`SSZList T cap`, `Bitvector N`, `Bitlist N`, and any other
`structure … deriving SSZRepr` you've defined yourself.

Preset-parameterised containers (those whose layout depends on
`MAX_VALIDATORS_PER_COMMITTEE` etc.) use the `forkstruct` /
`forkcontainer` DSL from the sister `EthCLLib` framework rather
than a plain `structure`, see the consensus-spec containers in
[`EthCLSpecs/Fulu/`](../EthCLSpecs/EthCLSpecs/Fulu/) for the
pattern.

## Hash-tree roots

On a plain value, `SSZ.hashTreeRoot H v` returns the 32-byte root.
It merkleizes the whole value on each call. The merkleization is a
well-founded recursion, so kernel `decide` cannot reduce it to
bytes; `native_decide` evaluates it with either hasher.

```lean
SSZ.hashTreeRoot Sha256 v       -- FFI SHA-256
SSZ.hashTreeRoot Sha256Spec v   -- pure-Lean SHA-256, no FFI trusted
```

On an `SSZ.Box`, read the root via `.hashTreeRoot`. It returns
a pair: the root, and the box with its cache filled. Keep the
second part to reuse the cache. The cached flavour returns a
pre-computed root in O(1); the uncached flavour re-runs the spec
each call.

```lean
-- On a cached box — reads the cached root, O(1)
(SSZ.FastBox v).hashTreeRoot

-- On an uncached box — runs the spec each call
(SSZ.PureBox v).hashTreeRoot
```

For comparing a computed root against a concrete byte string in
a theorem (e.g. "this state has root `0xAB…`"), see
[Proving things about your spec](#proving-things-about-your-spec)
below for the right tactic.

## Field reads and updates

### Plain values: record syntax

A plain value needs no macro. Lean's field projection reads, and
its record update writes:

```lean
let e  := f.epoch                         -- read
let f' := { f with epoch := e + 1 }       -- write
let f' := { f with                        -- several fields at once
             epoch := 42, currentVersion := Vector.replicate 4 0xff }
```

The collection types add methods for one element:

```lean
-- Read and replace element `i` of an `SSZList`
let v   := s.validators.get! i
let s'  := { s with validators := s.validators.set! i v' }

-- Read-modify-write of element `i`: names the field and the index once
let s'  := { s with validators := s.validators.modify i fun v =>
                { v with effectiveBalance := v.effectiveBalance + amount } }

-- Append, `none` when the list is at its cap
let vs? := s.validators.push? v
```

`get!` needs an `Inhabited` instance for the element type (it
returns `default` on a miss), so derive it too: `deriving
SSZRepr, Inhabited` on your container. `set!`, `modify` and
`push?` need no instance. `modify` exists on `SSZList`,
`ProgressiveList` and `Vector`.
Out of range it returns the collection unchanged, as `set!`
does. See [`.modify`](#modify) in the API reference.

### On a box: `sszGet` and `sszUpdate`

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

#### `sszGet`: reads

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

#### `sszUpdate`: writes

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
let s : SSZ.Box Sha256 T := sszUpdate s with x := 1
let s : SSZ.Box Sha256 T := sszUpdate s with y := 2
let s : SSZ.Box Sha256 T := sszUpdate s with z := 3
-- one root read here
let (root, s) := s.hashTreeRoot
```

produces *one* spine walk at the read, not three. Ascribe each
chained `let` (here `T` is your container, `Sha256` your hasher):
the macro reads the base's static type, and an unascribed `let`
holding an earlier `sszUpdate` result leaves it unresolved, so
the next `sszUpdate` in the chain fails to elaborate. The
uncached flavour emits struct rewrites with no pending state, so
`rfl` / `decide` proofs reduce identically.

### Serialising and deserialising

On a plain value, use `SSZ.serialize` and `SSZ.deserialize`:

```lean
def roundtrip (bytes : ByteArray) : Except SSZError ByteArray := do
  let f ← SSZ.deserialize (T := Fork) bytes
  return SSZ.serialize (bumpEpoch f 99)
```

`SSZ.Box` carries the spec serialiser through `.serialize`:

```lean
let bytes := (SSZ.FastBox f0).serialize
```

Each smart constructor has a matching `.deserialize` static
method that reads wire bytes directly into a Box. The pair reads
symmetrically: bytes go out via `box.serialize`, come back in
via `SSZ.FastBox.deserialize`:

```lean
def roundtripBox (bytes : ByteArray) : Except SSZError ByteArray := do
  let box     ← SSZ.FastBox.deserialize (T := Fork) bytes
  let updated := sszUpdate box with epoch := 99
  return updated.serialize
```

`SSZ.FastBox.deserialize` returns
`Except SSZError (SSZ.Box Sha256 T)`. The error propagates
through if the buffer is malformed, the same shape as
`SSZ.deserialize` on plain `T`.

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
   import SizzLean.Proofs.SizeBound   -- for `encodedFits_of_maxByteLength_lt`

   example (p : Pair) : SSZ.deserialize (SSZ.serialize p) = .ok p :=
     SSZ.roundtrip p (by decide)
       (SizzLean.Proofs.encodedFits_of_maxByteLength_lt
         (by decide) (SSZRepr.toRepr p) (by decide))
   ```

   `SSZ.roundtrip` takes two hypotheses. The first is the
   `BasicSupported` gate on the schema. `BasicSupported` is
   decidable (`Spec/BasicSupportedDecide.lean`), so `by decide`
   proves it for any closed schema, a 38-field `BeaconState`
   included. The second is the size bound
   `(SSZ.serialize p).size < MAX_LENGTH`. For a fixed-size schema
   `encodedFits_of_maxByteLength_lt` derives it from the schema's
   maximum size, as above. For a variable-size schema it is a fact
   about the value, so you pass it in as a hypothesis.

   `SSZ.serialize_injective` takes the same two hypotheses and
   proves non-malleability: two values with the same encoding are
   equal.

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
   (`Proofs.decode_encode` / `Proofs.serialize_injective` /
   `Proofs.encode_size_le_max`) are proved universally over
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
| FFI-hashed term must reduce to concrete bytes (e.g. *"this state's root is `0xAB…`"*) | `native_decide` | cites a compiler axiom plus `sha256Combine_eq_spec` and `sha256BatchCombine_eq_spec` through the `Sha256` instance |
| FFI-hashed term you want to manipulate symbolically before evaluating | rewrite with `sha256Hash_eq_spec`, `sha256Combine_eq_spec` or `sha256BatchCombine_eq_spec` as needed, then `native_decide` | cites the rewrite axioms used, the `Sha256` instance's two equivalence axioms when that instance occurs, and a compiler axiom |
| Pure-Lean hashed term (`SSZ.hashTreeRoot Sha256Spec v`, or a box built via `SSZ.UncachedBox Sha256Spec` / `SSZ.CachedBox Sha256Spec`) → concrete bytes | `native_decide` | the hash runs in pure Lean, so the FFI-equivalence axioms drop out; the `native_decide` compiler axiom stays |

One limit to know: kernel `decide` cannot reduce a concrete-root
goal under any hasher. The merkleization on top of the hasher
primitives is a well-founded recursion (`Spec/HashTreeRoot.lean`),
and `decide` does not unfold it, so reduction gets stuck even
when the hasher itself is pure Lean. Goals about the primitives
alone, such as a bare `Hasher.hash (H := Sha256Spec) b`, do close
by plain `decide`. For the whole root, `native_decide` is the
tactic, with either hasher.

Inspect a named theorem with `#print axioms theoremName` to see
its trust assumptions. On the pinned toolchain, the compiler axiom
prints as `theoremName._native.native_decide.ax_1_1`.

On plain values the first row is the common case. A plain
transition is a function from `T` to `T`, so a theorem about it
states an equation between values and closes by `rfl` or `simp`.
A root equation needs no hash computed when both sides hash the
same value:

```lean
example (f : Fork) (e : UInt64) : (bumpEpoch f e).epoch = e := rfl

example :
    SSZ.hashTreeRoot Sha256 (bumpEpoch f0 42)
      = SSZ.hashTreeRoot Sha256 ({ f0 with epoch := 42 } : Fork) := by
  rfl
```

There is no wrap and no cache invariant to carry. The box modes
reach the same statements through `.view`.

Rule of thumb: **use `native_decide` whenever a goal needs a
hash to reduce to bytes, with either hasher**; use `rfl` when
both sides hash the
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

### Library-internal property tests (`just sizzlean-test`)

`native_decide`-backed examples covering SHA-256 vectors, hasher
equivalence, randomised `setAt`, cache coherence on example
containers, and `sszUpdate` cases. Each fires at build time, so a
green build is a passed test suite.

```bash
just sizzlean-test
```

Fast, under a minute on a warm cache.

### Full NIST CAVP SHA-256 vectors (`just leansha256-test`)

The 129 byte-oriented CAVP vectors (65 ShortMsg + 64 LongMsg)
fired as `native_decide` assertions against the pure-Lean
SHA-256 reference. Lives in its own lib because the full sweep
takes ~108 s; smaller anchor gates still fire on the default
build.

```bash
just leansha256-test
```

### Upstream `ethereum/consensus-spec-tests` vectors

Two pytest harnesses drive a CLI runner against the pyspec
upstream archives. The fork-agnostic `ssz_generic` wire-format
suite runs from SizzLean against the `ssz_generic_runner` exe;
the per-fork `ssz_static` consensus-container suite runs from
EthCLSpecs against the `pyspec_server` exe (Fulu, Gloas, and Heze).

```bash
# Generic SSZ wire-format tests (uints, vectors, bitlist, …).
# Quick dev subset by default:
just sizzlean-pyspec

# Full generic sweep:
just sizzlean-pyspec-full

# Per-fork consensus-container tests (BeaconState, attestations, …).
# Quick dev subset on Fulu minimal by default:
just ethcl-pyspec

# Pass pytest args for more, e.g. a focused glob or a different fork:
just sizzlean-pyspec "--subset=0 -n auto"
just ethcl-pyspec "--fork=gloas"

# The complete in-scope EthCLSpecs sweep (all three forks, both presets):
just ethcl-pyspec-full
```

First run downloads + extracts the upstream archive (~hundreds
of MB) into `~/.cache/sizzlean/`. Subsequent runs hit the cache.

The Python venv (with `cramjam`, `tqdm`, `PyYAML`, `pytest`) is
created by `just setup-python` once.

### Everything local (`just test`)

```bash
just test
```

Runs the per-package in-Lean gates (`leansha256-test`, `sizzlean-test`,
and the crypto / Poseidon anchors). The consensus-spec libraries
have their own `just ethcl-test` recipe, where every `deriving
SSZRepr` in the in-spec containers is a compile-time gate. The
upstream-vector recipes are *not* in `just test`, they're
opt-in because each requires downloaded archives and runs
against external data.

## Importing the library

One import line at the top of your file gives you the full
user-facing surface:

* **Plain values**: `SSZ.serialize`, `SSZ.deserialize`,
  `SSZ.hashTreeRoot`, `SSZError`, and the collection methods
  (`get!`, `set!`, `modify`, `push?`).
* **The Box type and its four smart constructors**:
  `SSZ.Box`, `SSZ.FastBox` / `SSZ.PureBox` (Sha256-pinned),
  `SSZ.CachedBox` / `SSZ.UncachedBox` (hasher-explicit).
* **Reads and updates**: the `sszGet` and `sszUpdate` macros.
* **Container deriving**: `deriving SSZRepr` on your own
  structures.
* **Field-type instances**: `Vector`, `SSZList`, `Bitvector`,
  `Bitlist`.
* **Hasher tags**: `Sha256` (FFI), `Sha256Spec` (pure-Lean).
* **The cache-only type**: `CachedSSZ` in `SizzLean.Cache`.

All available from:

```lean
import SizzLean
```

The bare names this manual writes (`Sha256`, `SSZList`,
`SSZError`, `CachedSSZ`, `sszGet`, `sszUpdate`) sit in
sub-namespaces, so add these `open` lines too:

```lean
open SizzLean        -- the `SSZ.*` surface, the `Hasher` class
open SizzLean.Hasher -- the hasher tags `Sha256`, `Sha256Spec`
open SizzLean.Repr   -- the collection types `SSZList`, `Bitvector`, `Bitlist`
open SizzLean.Spec   -- the error type `SSZError`
open SizzLean.Cache  -- `CachedSSZ`, the `sszGet` / `sszUpdate` macros
```

The consensus-spec containers themselves live in the sibling
`EthCLSpecs` package; add an `[[require]]` for it in your
`lakefile.toml` and import what you need from
`EthCLSpecs.Fulu.<Container>` or `EthCLSpecs.Gloas.<Container>`.

## API reference

The full user-facing surface, organised by what you reach for it
for. Examples assume the `Fork` container from the worked example
earlier in the manual and the import and `open` lines from
[Importing the library](#importing-the-library) in scope.

Four sections:

1. **[Creating containers](#creating-containers)**: the building
   blocks for defining your own SSZ-encodable types.
2. **[Plain values](#plain-values)**: the root, serialise and
   deserialise functions on a plain `T`, and `modify`.
3. **[The Box interface](#the-box-interface)**: the box
   constructors, the read / write / root / serialise operations,
   and the box deserialisers.
4. **[Miscellaneous](#miscellaneous)**: the error type
   `SSZError`, hasher tags and the FFI-equivalence axioms;
   cross-cutting infrastructure.

### Creating containers

The pieces you compose into your own SSZ types.

#### `SSZRepr`

Typeclass that turns a Lean type into an SSZ-encodable type. You
rarely write an instance by hand, `deriving SSZRepr` synthesises
it, but you do mention `[SSZRepr T]` in generic-`T` binders.

```lean
def encode {T : Type} [SSZRepr T] (x : T) : ByteArray :=
  SSZ.serialize x
```

#### `deriving SSZRepr`

One-line derive that synthesises `SSZRepr` for any structure
whose fields all have `SSZRepr` instances themselves. From the
synthesised instance you get `SSZ.serialize`, `SSZ.deserialize`
and `SSZ.hashTreeRoot` on the plain value, and full
compatibility with `SSZ.Box`, `sszUpdate`, `sszGet`,
`.hashTreeRoot`, and `.serialize`.

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

#### `SSZList.get!`, `SSZList.set!`, `SSZList.modify`, `SSZList.size`

Element access / replacement / read-modify-write / length.
`get!` returns `default` on out-of-bounds, which is why it needs
an `Inhabited` instance for the element type (`deriving
SSZRepr, Inhabited` on your container covers it). `set!` and
`modify` are no-ops on out-of-bounds and preserve the cap proof
either way. `modify i f` replaces element `i` with `f` applied to it.
`size` is the runtime length.

```lean
let v   := xs.get! 3
let xs' := xs.set! 3 newV
let xs' := xs.modify 3 (fun v => { v with effectiveBalance := 0 })
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

### Plain values

The functions on a plain `T` with `[SSZRepr T]`. They live in
the `SSZ` namespace. Reads and writes need no function: use
`v.field` and `{ v with field := x }`.

#### `SSZ.hashTreeRoot`

`SSZ.hashTreeRoot H v` merkleizes `v` with the hasher `H` and
returns the 32-byte root. It recomputes the whole tree on each
call. With `Sha256Spec` the hash runs in pure Lean, so a
`native_decide` proof about its output trusts no FFI.

```lean
#eval SSZ.hashTreeRoot Sha256 f0

-- Setting the epoch to its current value preserves the root.
-- Both sides use `Sha256Spec`, so the proof cites no FFI axiom.
example :
    SSZ.hashTreeRoot Sha256Spec (bumpEpoch f0 5)
      = SSZ.hashTreeRoot Sha256Spec f0 := by
  native_decide
```

#### `SSZ.serialize`

Encodes a plain value to its SSZ wire-format bytes. SSZ encoding
is total, so it always succeeds.

```lean
#eval SSZ.serialize f0
```

#### `SSZ.deserialize`

Decodes wire bytes into a plain value. It returns
`Except SSZError T`. Name `T` when the context does not fix it.

```lean
SSZ.deserialize (T := Fork) bytes
```

#### `.modify`

`xs.modify i f` replaces element `i` of a collection with `f`
applied to it, and returns the collection unchanged when `i` is
out of range. It exists on `SSZList`, `ProgressiveList` and
`Vector`, so a read-modify-write names the field and the index
once. `modify` moves the element out of the array before it calls
`f`, so `f` can update a large element in place. The lemmas in
`SizzLean.Proofs.CollectionModify` restate it as `set!`.

```lean
def topUp (b : Batch) (i : Nat) (amount : UInt64) : Batch :=
  { b with validators := b.validators.modify i fun v =>
      { v with effectiveBalance := v.effectiveBalance + amount } }
```

### The Box interface

All operations on a boxed value go through `SSZ.Box H T`:
construct with one of the four smart constructors, then read
with `sszGet`, write with `sszUpdate`, take the root with
`.hashTreeRoot`, and serialise with `.serialize`.

#### `SSZ.Box`

Closed inductive over the two cache flavours (cached + uncached).
Used as a parameter type in spec functions that should accept
either flavour at the call site. Constructors are internal,
build a `Box` via one of the four smart constructors below.

```lean
def bumpEpochBox {H : Type} [Hasher H]
    (f : SSZ.Box H Fork) (n : UInt64) : SSZ.Box H Fork :=
  sszUpdate f with epoch := n
```

#### `SSZ.FastBox`

Sha256-pinned cached smart constructor. The production default:
FFI-hashed, O(1) root reads, O(log N) updates.

```lean
let b := SSZ.FastBox f0
#eval b.hashTreeRoot.1
```

`consing := true` opts the box into the hash-cons cache, so many
similar states kept resident share their common subtrees. The
flag is set once and follows the box through every `sszUpdate`.
Leave it off for a single resident state: there is nothing to
share, and each fresh cell then pays a cache lookup.

```lean
let archived := SSZ.FastBox f0 (consing := true)
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
flavour with a non-default hasher. Takes the same `consing`
opt-in as `FastBox`.

```lean
#eval (SSZ.CachedBox Sha256Spec f0).hashTreeRoot.1
```

#### `SSZ.UncachedBox`

Hasher-explicit uncached smart constructor, like `PureBox` but
the caller picks the `Hasher`. With `Sha256Spec` the whole
hashing pipeline runs in pure Lean, without an FFI hop.

```lean
example :
    (SSZ.UncachedBox Sha256Spec f0).hashTreeRoot.1
      = SSZ.hashTreeRoot Sha256Spec f0 := by native_decide
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

Reads the hash-tree root of a `Box`. It returns the pair
`(root, box)`, and the returned box carries the filled cache. The
cached arm returns the pre-computed root in O(1); the uncached
arm re-runs the spec.

```lean
#eval (SSZ.FastBox f0).hashTreeRoot.1
#eval (SSZ.PureBox f0).hashTreeRoot.1
```

#### `.serialize`

Encodes a `Box` to its SSZ wire-format bytes. Always succeeds,
SSZ encoding is total. Works identically on cached and uncached
flavours.

```lean
#eval (SSZ.FastBox f0).serialize
```

#### `.view`

Lower-level access: projects the underlying Lean value
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

When you hold plain values, use
[`SSZ.deserialize`](#sszdeserialize) instead. It returns the
plain `T`.

### Miscellaneous

Cross-cutting infrastructure used by every mode: the error type
`SSZError`, the hasher tags
and the FFI ≡ pure-Lean equivalence axioms.

#### `SSZError`

Sum of deserialise-error shapes (truncation, oversize, bad
offsets, etc.). Returned by the plain `SSZ.deserialize` and by
every box deserialiser. Pattern-match on it for fine-grained
handling or just `repr` it for diagnostics.

```lean
def explain : SSZError → String := fun e => s!"deserialize: {repr e}"
```

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
#eval (SSZ.CachedBox Sha256 f0).hashTreeRoot.1
```

#### `Sha256Spec`

Empty `inductive` tag whose `Hasher` instance delegates to the
pure-Lean SHA-256 reference (from the sibling `LeanSha256`
library). Its hashing primitives reduce in the kernel, so a bare
`Hasher.hash (H := Sha256Spec)` goal closes by plain `decide`;
the merkleization on top is a well-founded recursion, so a
concrete-root goal closes by `native_decide` instead. The
trade-off is speed versus proof trust: `native_decide`'s compiler
axiom stays, but the FFI and the FFI-equivalence axioms drop out,
and the pure-Lean hash costs a walk of the SHA-256 compression
function each call (slower).

```lean
example :
    (SSZ.UncachedBox Sha256Spec f0).hashTreeRoot.1
      = SSZ.hashTreeRoot Sha256Spec f0 := by
  native_decide   -- pure Lean: no FFI, no FFI-equivalence axioms
```

#### `sha256Hash_eq_spec`, `sha256Combine_eq_spec`, `sha256BatchCombine_eq_spec`

Three named axioms asserting that the FFI primitives agree with
the pure-Lean reference. `sha256Hash_eq_spec` and
`sha256Combine_eq_spec` cover scalar hashing and combining.
`sha256BatchCombine_eq_spec` covers batched combining against
`sha256BatchCombineSpec`, which maps `LeanSha256.combine` over
pairs. Use them as rewrite targets before `native_decide` when a
proof needs to manipulate an FFI-hashed term symbolically.

The `Sha256` instance proves its `batchCombine_eq` field from
`sha256Combine_eq_spec` and `sha256BatchCombine_eq_spec`.
A concrete-root proof using that instance cites both axioms,
even without an explicit rewrite.

```lean
example (b : ByteArray) :
    LeanHazmat.Sha256.sha256Hash b = LeanSha256.hash b := by
  rw [sha256Hash_eq_spec]
```
