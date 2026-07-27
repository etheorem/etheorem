import LeanImtPlus.Core

set_option autoImplicit false

/-!
# Hash-generic LeanIMT+ tree

This module implements the mutable operations of the reference data structure
as pure functions. Physical slots keep insertion order. Removal turns a slot
into the canonical `{0, 0}` tombstone, and odd Merkle nodes move up one level
without another hash.

The reference uses an AVL tree for predecessor lookup. This implementation
scans the active slots, preserving roots and proof formats while leaving room
for a later indexed storage backend.
-/

namespace LeanImtPlus

/-- Failures raised by tree mutation and proof generation. -/
inductive TreeError where
  | zeroValue
  | valueOutOfRange
  | duplicateValue
  | missingValue
  | emptyBatch
  | emptyTree
  | proofTooDeep
  deriving BEq, DecidableEq, Repr

/-- Physical LeanIMT+ leaf slots committed with hasher `H`. -/
structure Tree (H : Type) where
  slots : Array Leaf
  deriving BEq, Repr

/-- An empty tree, before creation of its sentinel. -/
def Tree.empty (H : Type) : Tree H :=
  { slots := #[] }

private def isTombstone (leaf : Leaf) : Bool :=
  leaf.value == 0 && leaf.nextValue == 0

/-- Active user leaves, excluding the sentinel and tombstones. -/
def Tree.leaves {H : Type} (tree : Tree H) : Array Leaf := Id.run do
  let mut result := #[]
  for i in [1:tree.slots.size] do
    let leaf := tree.slots[i]!
    if !isTombstone leaf then
      result := result.push leaf
  return result

/-- Number of active user values. -/
def Tree.size {H : Type} (tree : Tree H) : Nat :=
  tree.leaves.size

/-- Find the physical slot of an active value. -/
def Tree.indexOf? {H : Type} (tree : Tree H) (value : Nat) : Option Nat := Id.run do
  if value == 0 then
    return none
  let mut result := none
  for i in [1:tree.slots.size] do
    if tree.slots[i]!.value == value then
      result := some i
  return result

/-- Report whether an active leaf contains `value`. -/
def Tree.contains {H : Type} (tree : Tree H) (value : Nat) : Bool :=
  (tree.indexOf? value).isSome

private def validateValue {H : Type} [Hasher H] (value : Nat) :
    Except TreeError Unit := do
  if value == 0 then
    throw .zeroValue
  if !Hasher.validValue (H := H) value then
    throw .valueOutOfRange

/-- Find the physical slot containing the greatest active value below `value`. -/
private def predecessorIndex? {H : Type} (tree : Tree H) (value : Nat) :
    Option Nat := Id.run do
  if tree.slots.isEmpty then
    return none
  let mut bestIndex := 0
  let mut bestValue := 0
  for i in [1:tree.slots.size] do
    let leaf := tree.slots[i]!
    if leaf.value != 0 && leaf.value < value && bestValue < leaf.value then
      bestIndex := i
      bestValue := leaf.value
  return some bestIndex

private def insertCore {H : Type} (tree : Tree H) (value : Nat)
    (reuseSlot : Option Nat) : Tree H :=
  if tree.slots.isEmpty then
    { slots := #[{ value := 0, nextValue := value }, { value := value, nextValue := 0 }] }
  else if tree.size == 0 then
    let withSentinel := tree.slots.set! 0 { value := 0, nextValue := value }
    let slots := match reuseSlot with
      | some i => withSentinel.set! i { value := value, nextValue := 0 }
      | none => withSentinel.push { value := value, nextValue := 0 }
    { slots }
  else
    let lowIndex := (predecessorIndex? tree value).getD 0
    let lowLeaf := tree.slots[lowIndex]!
    let newLeaf := { value := value, nextValue := lowLeaf.nextValue }
    let withNew := match reuseSlot with
      | some i => tree.slots.set! i newLeaf
      | none => tree.slots.push newLeaf
    let rewired := withNew.set! lowIndex { lowLeaf with nextValue := value }
    { slots := rewired }

/-- Insert one nonzero value valid for the selected hasher. -/
def Tree.insert {H : Type} [Hasher H] (tree : Tree H) (value : Nat) :
    Except TreeError (Tree H) := do
  validateValue (H := H) value
  if tree.contains value then
    throw .duplicateValue
  return insertCore tree value none

/-- Insert values in order, matching repeated calls to `insert`. -/
def Tree.insertMany {H : Type} [Hasher H] (tree : Tree H) (values : Array Nat) :
    Except TreeError (Tree H) := do
  if values.isEmpty then
    throw .emptyBatch
  let mut result := tree
  for value in values do
    result ← result.insert value
  return result

/-- Remove an active value, rewiring its predecessor and leaving a tombstone. -/
def Tree.remove {H : Type} [Hasher H] (tree : Tree H) (value : Nat) :
    Except TreeError (Tree H) := do
  validateValue (H := H) value
  let some index := tree.indexOf? value
    | throw .missingValue
  let predecessor := (predecessorIndex? tree value).getD 0
  let removed := tree.slots[index]!
  let lowLeaf := tree.slots[predecessor]!
  let rewired := tree.slots.set! predecessor { lowLeaf with nextValue := removed.nextValue }
  let tombstoned := rewired.set! index { value := 0, nextValue := 0 }
  return { slots := tombstoned }

/-- Replace a value in its original physical slot after validating both inputs. -/
def Tree.update {H : Type} [Hasher H] (tree : Tree H) (oldValue newValue : Nat) :
    Except TreeError (Tree H) := do
  if oldValue == newValue then
    return tree
  validateValue (H := H) oldValue
  validateValue (H := H) newValue
  let some oldIndex := tree.indexOf? oldValue
    | throw .missingValue
  if tree.contains newValue then
    throw .duplicateValue
  let removed ← tree.remove oldValue
  return insertCore removed newValue (some oldIndex)

/-- Number of parent levels needed for the current physical slots. -/
def Tree.depth {H : Type} (tree : Tree H) : Nat :=
  if tree.slots.size <= 1 then 0 else Nat.log2 (tree.slots.size - 1) + 1

private def nextLevel {H : Type} [Hasher H]
    (nodes : Array (Digest H)) : Array (Digest H) := Id.run do
  let mut parents := #[]
  for i in [0:(nodes.size + 1) / 2] do
    let leftIndex := 2 * i
    let rightIndex := leftIndex + 1
    let left := nodes[leftIndex]!
    let parent := if rightIndex < nodes.size then
      internalHash left nodes[rightIndex]!
    else
      left
    parents := parents.push parent
  return parents

private def levels {H : Type} [Hasher H] (tree : Tree H) :
    Array (Array (Digest H)) := Id.run do
  let mut current := tree.slots.map leafHash
  let mut result := #[current]
  for _ in [0:tree.depth] do
    current := nextLevel current
    result := result.push current
  return result

/-- Compute the current root. Empty trees have no sentinel and no root. -/
def Tree.root {H : Type} [Hasher H] (tree : Tree H) :
    Except TreeError (Digest H) := do
  if tree.slots.isEmpty then
    throw .emptyTree
  return (levels tree)[tree.depth]![0]!

/-- Generate a compressed unified membership or non-membership proof. -/
def Tree.generateProof {H : Type} [Hasher H] (tree : Tree H) (value : Nat) :
    Except TreeError (Proof H) := do
  validateValue (H := H) value
  if tree.slots.isEmpty then
    throw .emptyTree
  let (proofType, physicalIndex) := match tree.indexOf? value with
    | some index => (ProofType.membership, index)
    | none => (ProofType.nonMembership, (predecessorIndex? tree value).getD 0)
  let root ← tree.root
  let treeLevels := levels tree
  let mut nodeIndex := physicalIndex
  let mut leafIndex := 0
  let mut siblings := #[]
  for level in [0:tree.depth] do
    let nodes := treeLevels[level]!
    let isRight := (nodeIndex &&& 1) == 1
    let siblingIndex := if isRight then nodeIndex - 1 else nodeIndex + 1
    if siblingIndex < nodes.size then
      if isRight then
        leafIndex := leafIndex + 2 ^ siblings.size
      siblings := siblings.push nodes[siblingIndex]!
    nodeIndex := nodeIndex / 2
  if siblings.size >= 252 then
    throw .proofTooDeep
  return {
    proofType
    root
    value
    leaf := tree.slots[physicalIndex]!
    leafIndex
    depth := siblings.size
    siblings
  }

end LeanImtPlus
