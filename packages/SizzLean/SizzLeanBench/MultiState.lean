import SizzLean.Hasher.Sha256
import SizzLean.Cache.Box
import SizzLean.Cache.MerkleTree.HashCons
import SizzLeanBench.Fixtures
import SizzLeanBench.Timer

/-!
# `SizzLeanBench.MultiState`: resident heap with and without hash-consing

The Stage 17c bench. The scenarios bench (`ssz_bench`) measures
time on one resident state and shows consing as pure overhead
there. This bench measures the case consing exists for: `N`
consecutive states kept resident at once, each a fresh tree that
shares most of its subtrees with its neighbours. It reports how
many distinct tree cells the `N` trees reach, with consing off and
with consing on.

## Workload

State `i` is a `ValidatorSet256` whose validator `i mod 256` is
replaced by a salted one. Every state is built fresh through
`SSZ.FastBox`, as a state that arrived over the wire or came off
disk would be. The states are not derived from each other by
`sszUpdate`, which already shares structure by persistence; the
question here is whether two independently built trees end up
sharing.

## The metric

Heap is counted, not sampled. `uniqueCells` walks the `N` trees
with a visited set keyed by object address and counts each cell
once, so a subtree that two trees share counts once. The count
does not depend on allocator behaviour, which the Lean runtime's
small-object allocator makes hard to read from RSS: freed pages
stay mapped, so a second configuration run in the same process
would report almost no growth whatever it allocated.

`est_bytes` turns the count into bytes with the Lean object
layout: a pair cell is a 3-field constructor (32 bytes) plus its
`some root` box (16 bytes) plus the 32-byte root array (56 bytes
with its header), 104 bytes in all; a leaf is a 1-field
constructor (16 bytes) plus its array (56 bytes), 72 bytes. The
estimate ignores per-box overhead (`view`, the thunk, the pending
map), which is the same in both configurations.

## Reading the TSV

One row per `(config, N)`:

```
label  states  pairs  leaves  est_bytes  cache_hits  cache_misses  build_ns
```

`pairs` and `leaves` for `consing off` grow linearly in `N`. For
`consing on` they should grow by one changed validator subtree
plus one spine per state after the first. The doc target
(`OPTIMISATION.md`, Stage 17c) is proportionally less heap than
`N` fresh states once `N` reaches 50.

`build_ns` is the wall time to build and root all `N` states, so
the per-state cost of the cache lookups is visible next to the
heap it buys.
-/

set_option autoImplicit false

namespace SizzLeanBench.MultiState

open SizzLean
open SizzLean.Cache
open SizzLean.Cache.MerkleTree
open SizzLean.Hasher
open SizzLeanBench.Fixtures

/-- The base set every state is one validator away from. -/
private def baseSet : ValidatorSet256 := mkValidatorSet256 1

/-- State `i`: the base set with validator `i mod 256` replaced. -/
private def stateAt (i : Nat) : ValidatorSet256 :=
  { validators := baseSet.validators.set! (i % 256) (mkValidator (0x80 + UInt8.ofNat i)) }

/-- Distinct `(pairs, leaves)` reachable from the given roots.
Object addresses key the visited set; a cell reached twice counts
once. The walk is explicit-stack so a deep list subtree cannot
overflow the OS stack. -/
unsafe def uniqueCellsUnsafe (roots : Array Node) : Nat × Nat := Id.run do
  let mut seen : Std.HashSet USize := {}
  let mut pairs := 0
  let mut leaves := 0
  let mut stack : Array Node := roots
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    let addr := ptrAddrUnsafe n
    if seen.contains addr then continue
    seen := seen.insert addr
    match n with
    | .leaf _ => leaves := leaves + 1
    | .pair l r _ =>
        pairs := pairs + 1
        stack := stack.push l
        stack := stack.push r
  return (pairs, leaves)

/-- Safe face of `uniqueCellsUnsafe`. The kernel-visible body is a
placeholder; only the compiled bench calls this. -/
@[implemented_by uniqueCellsUnsafe]
def uniqueCells (_roots : Array Node) : Nat × Nat := (0, 0)

/-- Estimated resident bytes for the counted cells. See the module
docstring for the per-cell figures. -/
def estimateBytes (pairs leaves : Nat) : Nat :=
  pairs * 104 + leaves * 72

/-- The committed tree of a cached box. The uncached flavour has
no tree and reports nothing; this bench only builds cached boxes. -/
private def treeOf {T : Type} [SSZRepr T] : SSZ.Box Sha256 T → Option Node
  | .cached t   => some t.treeBase.get
  | .uncached _ => none

def printHeader : IO Unit :=
  IO.println "label\tstates\tpairs\tleaves\test_bytes\tcache_hits\tcache_misses\tbuild_ns"

/-- Build `n` states with the given consing flag, keep all of them
resident, and print one row. Returns the roots so the caller can
check the two configurations agree. -/
def runConfig (consing : Bool) (n : Nat) : IO (Array ByteArray) := do
  HashCons.clear
  let t0 ← IO.monoNanosNow
  let mut boxes : Array (SSZ.Box Sha256 ValidatorSet256) := #[]
  let mut roots : Array ByteArray := #[]
  for i in [0:n] do
    let box := SSZ.FastBox (stateAt i) (consing := consing)
    let (root, box) := box.hashTreeRoot
    boxes := boxes.push box
    roots := roots.push root
  let t1 ← IO.monoNanosNow
  let trees := boxes.filterMap treeOf
  let (pairs, leaves) := uniqueCells trees
  let (hits, misses) ← HashCons.stats
  let label := if consing then "MultiState · consing on " else "MultiState · consing off"
  IO.println s!"{label}\t{n}\t{pairs}\t{leaves}\t{estimateBytes pairs leaves}\t{hits}\t{misses}\t{t1 - t0}"
  return roots

/-- Run both configurations at each state count and check the
roots agree. Exits non-zero on a root mismatch, since a wrong root
would make the heap figure meaningless. -/
def runAll : IO Unit := do
  -- A mainnet-sized cache: the default 4096 is smaller than one
  -- `ValidatorSet256` tree and would wipe every few states.
  HashCons.setCapacity (1 <<< 20)
  printHeader
  for n in [1, 10, 50, 100] do
    let off ← runConfig false n
    let on  ← runConfig true n
    if off != on then
      IO.eprintln s!"MultiState: root mismatch between consing off and on at N = {n}"
      IO.Process.exit 1
  HashCons.setCapacity HashCons.defaultCapacity

end SizzLeanBench.MultiState
