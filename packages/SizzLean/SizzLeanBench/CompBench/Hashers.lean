import LeanHazmatSha256
import SizzLean.Cache.Box
import SizzLean.Hasher.Sha256
import SizzLeanBench.CompBench.Fixture
import SizzLeanBench.Timer

/-!
# `SizzLeanBench.CompBench.Hashers`: what one Merkle step costs

The comparative benchmark reports a first root of a few hundred
milliseconds. Two things can produce that number: the hashing, or
everything around the hashing. They call for opposite fixes, so
the report should not leave a reader guessing which one it is.

This module prices the hashing on its own. It times the two FFI
SHA-256 entry points over the input shape merkleization actually
feeds them, two 32-byte children, and reports nanoseconds per
hash for each:

* **`Hasher.combine`**, one call per interior tree node. This is
  the primitive `merkleRootWithCache` and the spec walk both use.
  It reaches OpenSSL's `EVP` interface, which dispatches to SHA-NI
  or AVX-512 inside libcrypto but hashes one input at a time.
* **`sha256BatchCombine`**, many sibling pairs in one call. On
  x86_64 Linux this reaches Intel ISA-L's multi-buffer engine,
  which hashes 4, 8, or 16 inputs in parallel SIMD lanes.

The module then counts the calls one root of the shared fixture
makes, so the two figures multiply out to an answer rather than to
an estimate. Nothing in SizzLean calls the batched primitive
today, so the count also prices what routing the tree walk through
it could win.

## Why a chain and not a loop over one input

Each iteration hashes the previous iteration's output. The
dependency stops the compiler hoisting the call out of the loop,
and it stops the CPU overlapping iterations in a way the tree walk
could not. A Merkle level is parallel, so this understates what a
batched engine can do and states the sequential primitive exactly.
-/

set_option autoImplicit false

namespace SizzLeanBench.CompBench.Hashers

open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open SizzLeanBench.Timer

/-- A 32-byte buffer with every byte set to `b`. -/
private def chunk (b : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate 32 b)

/-- Time `n` sequential `Hasher.combine` calls, each hashing the
previous result against a fixed sibling. Returns the total
nanoseconds and a digest byte, which keeps the chain reachable. -/
private def timeCombine (n : Nat) : IO (Nat × Nat) := do
  let sibling := chunk 0x5a
  let mut acc := chunk 0x01
  let t0 ← IO.monoNanosNow
  for _ in [:n] do
    acc := Hasher.combine (H := Sha256) acc sibling
  let total := acc[0]!.toNat
  let t1 ← IO.monoNanosNow
  return (t1 - t0, total)

/-- Time `n` hashes through `sha256BatchCombine`, in batches of
`width`. Each batch depends on the one before, so the batches stay
sequential even though the lanes inside one batch do not. -/
private def timeBatch (n width : Nat) : IO (Nat × Nat) := do
  let batches := n / width
  let mut lefts : Array ByteArray := Array.replicate width (chunk 0x01)
  let rights : Array ByteArray := Array.replicate width (chunk 0x5a)
  let t0 ← IO.monoNanosNow
  for _ in [:batches] do
    lefts := LeanHazmat.Sha256.sha256BatchCombine lefts rights
  let total := lefts[0]![0]!.toNat
  let t1 ← IO.monoNanosNow
  return (t1 - t0, total)

/-- Print one line: the label, the hashes timed, and the cost per
hash in nanoseconds. -/
private def report (label : String) (hashes : Nat) (elapsed : Nat) : IO Unit :=
  IO.println s!"{label}\t{hashes}\t{elapsed / hashes} ns/hash\t\
    {(hashes * 1000000000) / elapsed} hash/s"

/-! ## Counting one root's hashes

A `Hasher` method is pure, so a counting instance has no honest
place to keep a tally. This one keeps it in a module-level
`IO.Ref` reached through `unsafeBaseIO`, which is exactly the
unsoundness the seam exists to keep out of the library. It is
confined to this bench module and to the `hashers` subcommand;
nothing in `SizzLean` imports it, and no proof mentions it. -/

/-- The tally. `initFn` runs once, when the module loads. -/
private builtin_initialize hashCounter : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

/-- Phantom tag for the counting instance. -/
private inductive Counting : Type

/-- The two counting methods. Each bumps its half of the tally and
then delegates to the FFI instance.

They reach the instance as `@[implemented_by]` bodies behind an
`opaque` declaration. An `opaque` has no definition the compiler can
see through, so it cannot fold two calls with equal arguments into
one, which is what would undercount a tree whose siblings coincide. -/
private unsafe def countedHash (b : ByteArray) : ByteArray :=
  unsafeBaseIO do
    hashCounter.modify fun (h, c) => (h + 1, c)
    return Hasher.hash (H := Sha256) b

private unsafe def countedCombine (l r : ByteArray) : ByteArray :=
  unsafeBaseIO do
    hashCounter.modify fun (h, c) => (h, c + 1)
    return Hasher.combine (H := Sha256) l r

@[implemented_by countedHash]
private opaque countedHashImpl (b : ByteArray) : ByteArray

@[implemented_by countedCombine]
private opaque countedCombineImpl (l r : ByteArray) : ByteArray

private instance : Hasher Counting where
  hash    := countedHashImpl
  combine := countedCombineImpl

/-- Root the shared fixture through the counting hasher and report
what one uncached walk asks of each method. The uncached flavour is
the one to count: the cached flavour's first walk hashes the same
tree, and its later walks are what the cache exists to avoid. -/
private def countOneRoot : IO (Nat × Nat) := do
  hashCounter.set (0, 0)
  let box : SSZ.Box Counting Fulu.BeaconState :=
    SSZ.UncachedBox Counting Fixture.mkBeaconState
  let (root, _) := box.hashTreeRoot
  if root[0]!.toNat == 999 then IO.eprintln "unreachable"
  hashCounter.get

/-- Price both entry points, then count what one root asks of them.
`hashes` is the count each timing row runs; 100000 puts every row
above a millisecond and keeps the subcommand under a second. -/
def runAll (hashes : Nat) : IO Unit := do
  IO.println "primitive\thashes\tper hash\tthroughput"
  let mut sink := 0
  let (combineNs, d) ← timeCombine hashes
  sink := sink + d
  report "Hasher.combine (OpenSSL EVP, one at a time)" hashes combineNs
  let mut bestBatchNs := combineNs
  for width in [4, 8, 16, 64, 256] do
    let (batchNs, d) ← timeBatch hashes width
    sink := sink + d
    if batchNs < bestBatchNs then bestBatchNs := batchNs
    report s!"sha256BatchCombine (ISA-L, {width} per call)" hashes batchNs
  if sink == 0 then IO.eprintln "warning: the hasher sink is zero"

  let (hashCalls, combineCalls) ← countOneRoot
  let calls := hashCalls + combineCalls
  IO.println ""
  IO.println "one uncached root of the shared fixture"
  IO.println s!"  Hasher.hash calls\t{hashCalls}"
  IO.println s!"  Hasher.combine calls\t{combineCalls}"
  -- The two projections below are the point of the subcommand: they
  -- turn a per-hash figure into a share of the root the report times.
  let spentMs := (calls * (combineNs / hashes)) / 1000000
  let batchedMs := (calls * (bestBatchNs / hashes)) / 1000000
  IO.println s!"  time in the hasher, at {combineNs / hashes} ns/hash\t{spentMs} ms"
  IO.println s!"  the same calls batched, at {bestBatchNs / hashes} ns/hash\t{batchedMs} ms"

end SizzLeanBench.CompBench.Hashers
