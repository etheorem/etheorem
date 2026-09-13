import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLean.Hasher.Sha256
import SizzLeanBench.CompBench.Fixture
import SizzLeanBench.Timer

/-!
# `SizzLeanBench.CompBench.Scenarios`: the two comparative scenarios

Both scenarios run the same four phases over the shared
`BeaconState` fixture, and both report the four phases separately:

| Phase | What it times |
|---|---|
| `deser` | wire bytes to a plain Lean value |
| `wrap`  | that value to a `Box` |
| `root1` | the first merkleization, from cold |
| `update` | the writes |
| `root2` | the second merkleization, after the writes |

`deser` and `wrap` are separated because only SizzLean has a
`wrap` step. The other two libraries root the decoded value
directly, so their harnesses report a zero there and their `deser`
column compares against ours like with like. The separation also
answers a question the totals alone would hide: an implementation
that hashed during decode would show it here, as a `deser` or a
`wrap` that costs what a root costs.

The two scenarios differ only in the write count.

* `update1` writes one field, `slot`.
* `update1000` writes 1000 fields, spread over four shapes:
  250 validator records, 250 packed balances, 250 `blockRoots`
  entries, and 250 `randaoMixes` entries.

Spreading the thousand writes matters. A thousand writes into one
list share most of their Merkle path, so a cache would pay for one
subtree and reuse it. Four shapes at four depths make the second
root walk four separate paths, which is what a real slot does.

## Why every repetition decodes again

A cached box holds its Merkle tree between roots, so its second
`root1` would be free. Each repetition therefore starts from the
wire bytes and builds a fresh box. `deser` and `wrap` cover that,
and together they are the honest cost of getting a rootable value
out of a buffer.

## The two configurations

Both call the same `Box` methods; only the constructor differs.

* **Fast**: `SSZ.FastBox`, the production path. A write rehashes
  the path from the changed field up to the root.
* **Pure**: `SSZ.PureBox`, the uncached path. Every root re-runs
  the spec over the whole value.

Both pin the FFI SHA-256 (`Sha256`), so the pair isolates the
cache and nothing else. The pure-Lean hasher is a separate
question that `packages/SizzLean/docs/OPTIMISATION.md` covers.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SizzLeanBench.CompBench.Scenarios

open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open SizzLeanBench.CompBench.Fixture
open SizzLeanBench.Timer

/-- Writes per shape in the `update1000` scenario. Four shapes, so
the scenario writes `4 * writesPerShape = 1000` fields. -/
def writesPerShape : Nat := 250

/-- The timings one repetition of one scenario produces, in
nanoseconds. -/
structure Sample where
  deserNs  : Nat
  wrapNs   : Nat
  root1Ns  : Nat
  updateNs : Nat
  root2Ns  : Nat
  deriving Repr

/-- A root rendered as a lowercase `0x` hex string, the form all
three harnesses print so the driver can compare them. -/
def rootHex (r : ByteArray) : String :=
  "0x" ++ String.join (r.toList.map fun b =>
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let digit (n : Nat) : String :=
      if n < 10 then toString n else String.singleton (Char.ofNat (87 + n))
    digit hi ++ digit lo)

/-! ## The write phases

Each takes a box and returns the box the writes produced. The
`update1000` version writes the four shapes in a fixed order:
validators, balances, `blockRoots`, `randaoMixes`. The Rust and
the Python harnesses write the same fields in the same order, so
the two roots agree across all three. -/

/-- The single write: bump `slot` by one. -/
def writeOne {H : Type} [Hasher H] (box : SSZ.Box H Fulu.BeaconState) :
    SSZ.Box H Fulu.BeaconState :=
  sszUpdate box with slot := box.view.slot + 1

/-- The thousand writes. The balances list takes one whole-list
replacement rather than 250 separate ones: `balances` is a packed
list of basic elements, which the update macro's index syntax does
not cover, so the 250 element writes are applied to the array and
the result is stored in one clause.

Both reads of the box's contents happen once, before the loops
that use them. A cached box's `view` reassembles the value from
its cells, so reading it inside a loop would make the loop
quadratic and the row would measure that instead of the writes.
Each field is written once here, so hoisting the read changes no
result. -/
def writeThousand {H : Type} [Hasher H] (box : SSZ.Box H Fulu.BeaconState) :
    SSZ.Box H Fulu.BeaconState := Id.run do
  let validators := box.view.validators
  let mut balances := box.view.balances
  let mut b := box
  -- 250 validator records: bump each one's effective balance.
  for i in [:writesPerShape] do
    let old := validators.get! i
    b := sszUpdate b with
      validators[i]! := { old with effectiveBalance := old.effectiveBalance + 1000000 }
  -- 250 packed balances, applied to the array and stored once.
  for i in [:writesPerShape] do
    balances := balances.set! i (balances.get! i + 12345)
  b := sszUpdate b with balances := balances
  -- 250 `blockRoots` entries.
  for i in [:writesPerShape] do
    b := sszUpdate b with blockRoots[i]! := mkRoot (i + 90000)
  -- 250 `randaoMixes` entries.
  for i in [:writesPerShape] do
    b := sszUpdate b with randaoMixes[i]! := mkRoot (i + 95000)
  return b

/-! ## The driver

One repetition decodes the buffer, roots, writes, and roots
again, timing each phase. The decode failure case aborts the run:
a benchmark over a value that did not decode measures nothing.

Every phase ends by folding its result to one `Nat` and passing
that through `force`, between the two clock reads. Two things
make the fold necessary. A term the code only *names* stays
unevaluated, so the phase would report the time it took to name
it. And Lean's compiler is free to move a pure computation to
wherever its result is first needed, which without a barrier is
some later phase. `force` compares the digest against zero, which
is an `IO` action the compiler cannot move the digest past. -/

/-- Sum a buffer's bytes. -/
@[inline] def digest (b : ByteArray) : Nat :=
  b.foldl (init := 0) fun acc x => acc + x.toNat

/-- The phase barrier: force `d`, then sink it. The comparison is
what forces; the sink is what keeps the result reachable, so dead-
code elimination cannot drop the work behind it. -/
@[inline] def force (sink : IO.Ref Nat) (d : Nat) : IO Unit := do
  if d == 0 then IO.eprintln "warning: a timed phase produced a zero digest"
  sink.modify (· + d)

/-- Run one repetition and return its five timings plus the two
roots. `mkBox` picks the configuration; `write` picks the
scenario. -/
def runOnce {H : Type} [Hasher H]
    (mkBox : Fulu.BeaconState → SSZ.Box H Fulu.BeaconState)
    (write : SSZ.Box H Fulu.BeaconState → SSZ.Box H Fulu.BeaconState)
    (bytes : ByteArray) (sink : IO.Ref Nat) : IO (Sample × String × String) := do
  -- Deserialize: wire bytes to a plain value. The digest reads the
  -- sizes the decode had to fill, which forces the whole value.
  let t0 ← IO.monoNanosNow
  let value ←
    match (SSZ.deserialize bytes : Except Spec.SSZError Fulu.BeaconState) with
    | .error e => throw (IO.userError s!"fixture did not decode: {repr e}")
    | .ok v => pure v
  force sink (value.validators.size + value.randaoMixes.size + value.slot.toNat)
  let t1 ← IO.monoNanosNow
  -- Wrap: the value to a `Box`. The cached flavour allocates its
  -- cell table here; it walks the tree on the first root, not now.
  let box := mkBox value
  force sink (box.view.validators.size + box.view.slot.toNat)
  let t2 ← IO.monoNanosNow
  -- First root, from cold. The cached flavour builds its Merkle
  -- tree here, on the first walk.
  let (root1, box₁) := box.hashTreeRoot
  force sink (digest root1)
  let t3 ← IO.monoNanosNow
  -- The writes.
  let box₂ := write box₁
  force sink (box₂.view.slot.toNat + 1)
  let t4 ← IO.monoNanosNow
  -- Second root, after the writes.
  let (root2, _) := box₂.hashTreeRoot
  force sink (digest root2)
  let t5 ← IO.monoNanosNow
  return ({ deserNs := t1 - t0, wrapNs := t2 - t1, root1Ns := t3 - t2
          , updateNs := t4 - t3, root2Ns := t5 - t4 }
         , rootHex root1, rootHex root2)

end SizzLeanBench.CompBench.Scenarios
