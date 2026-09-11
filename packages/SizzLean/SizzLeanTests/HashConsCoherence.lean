import SizzLean.Hasher.Sha256
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLean.Cache.MerkleTree.HashCons
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.HashConsCoherence`: hash-consing gates

The hash-cons cache (`SizzLean/Cache/MerkleTree/HashCons.lean`) is a
memory optimisation. Its safety contract has two halves:

1. **Root coherence.** A box built with `consing := true` roots to
   the same digest as the spec oracle, before and after
   `sszUpdate`. Sharing a cell must never change a root.
2. **The shape rule.** A cache hit is accepted only for a
   shape-equal cell. SSZ gives a container and the vector of its
   field roots the same root, so without the rule a tree holding a
   nested container could be swapped for one holding that
   container's root as a single leaf. A later write into the nested
   container would then stop at the leaf and be dropped.

Both halves run through the user-facing `SSZ.FastBox` surface, so
the gates exercise the integration and not only the primitive.

## Evaluation

The checks are pure `Bool` functions closed by `native_decide`,
like the sibling `TreeBackedCoherence` gates. The consing entry
points are `@[implemented_by]` wrappers over a global `IO.Ref`, so
the compiled evaluation `native_decide` runs is exactly what a
program sees. Lean evaluates `let` bindings in order, and each
step below feeds a value into the next, so the sequence the shape
rule depends on is fixed by data flow and not only by source order.
-/

set_option autoImplicit false

namespace SizzLeanTests.HashConsCoherence

open SizzLean
open SizzLean.Cache
open SizzLean.Cache.MerkleTree (HashCons.statsSnapshot)
open SizzLean.Hasher
open SizzLeanTests.ExampleContainers

/-- The `BeaconBlockHeader` analogue of `NestedExample`: the same
two fields, with the nested container replaced by its root. Both
containers have the same `hashTreeRoot` when `messageRoot` is the
root of `message`. -/
structure SummaryExample where
  messageRoot : ExRoot
  signature   : Vector UInt8 96
deriving Inhabited, DecidableEq, SSZRepr

private def inner : InnerExample :=
  { slot   := 7
    marker := 11
    rootA  := Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 i.val)
    rootB  := Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 (i.val + 32))
    rootC  := Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 (i.val + 64)) }

private def sig : Vector UInt8 96 :=
  Vector.ofFn (fun (i : Fin 96) => Nat.toUInt8 (i.val * 3))

private def nested : NestedExample :=
  { message := inner, signature := sig }

private def batch : BatchExample :=
  let mkRoot (k : Nat) : ExRoot :=
    Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 ((i.val + k) % 256))
  { rootsA := Vector.ofFn (fun (i : Fin 8) => mkRoot (i.val * 7))
    rootsB := Vector.ofFn (fun (i : Fin 8) => mkRoot (i.val * 13 + 100)) }

/-- Turn a 32-byte digest into the `ExRoot` vector form. -/
private def toExRoot (b : ByteArray) : ExRoot :=
  Vector.ofFn (fun (i : Fin 32) => b.get! i.val)

/-- The summary whose root equals `nested`'s root. -/
private def summary : SummaryExample :=
  { messageRoot := toExRoot (SSZ.hashTreeRoot Sha256 inner), signature := sig }

/-! ## Gate 1: root coherence with consing on -/

example :
    (SSZ.FastBox nested (consing := true)).hashTreeRoot.1
      = SSZ.hashTreeRoot Sha256 nested := by native_decide

example :
    (SSZ.FastBox batch (consing := true)).hashTreeRoot.1
      = SSZ.hashTreeRoot Sha256 batch := by native_decide

/-- Two consing boxes over the same value, then an update on the
second. The second box's tree is a cache hit on the first's, and
the update must still land. The hit counter has to move between
the two root reads, which is the positive evidence that the boxes
went through the cache at all.

Each flag depends on the previous step's output, so the steps run
in this order, and no flag folds to a constant: the compiler would
otherwise merge `a` and `b` into one box and `b` would never build
a tree of its own. -/
private def sharedThenUpdated : Bool :=
  let a := SSZ.FastBox nested (consing := true)
  let (rootA, _) := a.hashTreeRoot
  let (_, hitsBefore, _) := HashCons.statsSnapshot rootA.size
  let b := SSZ.FastBox nested (consing := hitsBefore + rootA.size > 0)
  let (rootB, b) := b.hashTreeRoot
  let (_, hitsAfter, _) := HashCons.statsSnapshot (rootB.size + 1)
  let b := sszUpdate b with message.slot := 99
  let expected := SSZ.hashTreeRoot Sha256 { nested with message.slot := 99 }
  rootA == rootB && hitsAfter > hitsBefore && b.hashTreeRoot.1 == expected

example : sharedThenUpdated = true := by native_decide

/-! ## Gate 2: the shape rule

The summary goes into the cache first. The block built next has
the same top root, so its top cell is a same-root lookup against
the summary's cell. The shape rule must reject that hit: the block
then keeps its own tree and the write into `message` lands. -/

private def summaryEqualsNested : Bool :=
  SSZ.hashTreeRoot Sha256 summary == SSZ.hashTreeRoot Sha256 nested

example : summaryEqualsNested = true := by native_decide

private def shapeRuleHolds : Bool :=
  let s := SSZ.FastBox summary (consing := true)
  let (rootS, _) := s.hashTreeRoot
  -- The block's flag depends on `rootS`, so the summary's tree is
  -- in the cache before the block's tree is built.
  let block := SSZ.FastBox nested (consing := rootS.size == 32)
  let (rootBlock, block) := block.hashTreeRoot
  let block := sszUpdate block with message.marker := 4242
  let expected := SSZ.hashTreeRoot Sha256 { nested with message.marker := 4242 }
  rootS == rootBlock && block.hashTreeRoot.1 == expected

example : shapeRuleHolds = true := by native_decide

/-- The reverse order: the block is cached first, then the summary
is built. The summary's write into `messageRoot` must land on a
leaf, so a hit that handed it the block's subtree would break the
root. -/
private def shapeRuleHoldsReversed : Bool :=
  let block := SSZ.FastBox nested (consing := true)
  let (rootBlock, _) := block.hashTreeRoot
  let s := SSZ.FastBox summary (consing := rootBlock.size == 32)
  let (rootS, s) := s.hashTreeRoot
  let newRoot : ExRoot := Vector.replicate 32 0x5a
  let s := sszUpdate s with messageRoot := newRoot
  let expected := SSZ.hashTreeRoot Sha256 { summary with messageRoot := newRoot }
  rootS == rootBlock && s.hashTreeRoot.1 == expected

example : shapeRuleHoldsReversed = true := by native_decide

/-! ## Gate 3: the primitive on its own

`Node.mkPair` is the `BaseIO` form kept for callers that hold a
root in hand. The pure `consPair` and `consTree` wrappers are what
the gates above exercise; this one checks the primitive keeps the
root and passes `none` cells through. -/

open SizzLean.Cache.MerkleTree in
private def primitiveRoots : Bool :=
  let l : Node := .leaf (ByteArray.mk (Array.replicate 32 0xaa))
  let r : Node := .leaf (ByteArray.mk (Array.replicate 32 0xbb))
  let root := Hasher.combine (H := Sha256)
    (ByteArray.mk (Array.replicate 32 0xaa)) (ByteArray.mk (Array.replicate 32 0xbb))
  let consed := Node.consPair l r root
  let plain : Node := .pair l r none
  consed.merkleRoot Sha256 == root && plain.merkleRoot Sha256 == root
    && (Node.consTree plain).merkleRoot Sha256 == root

example : primitiveRoots = true := by native_decide

end SizzLeanTests.HashConsCoherence
