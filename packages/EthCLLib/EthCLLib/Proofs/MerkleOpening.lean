import EthCLLib.Spec.Arith
import EthCLLib.Spec.MerklePath
import SizzLean.Cache.MerkleTree.Build
import SizzLean.Proofs.Perfect
import SizzLean.Proofs.Util

/-!
# `EthCLLib.Proofs.MerkleOpening`: openable paths and honest Merkle openings

The path vocabulary the completeness proof quantifies over, and the openers that
produce a witness for it.

`IsOpenable` is the central predicate: a root-to-leaf path witness at one index,
which is all a completeness proof ever walks. See its declaration docstring for
the per-level obligations. `leafAt` and `siblingPath` extract the honest opening,
and `honestLeaf` / `honestBranch` are their root-typed sugar. `isOpenable_of_isPerfect`
injects every `IsPerfect` tree from SizzLean into the predicate.

All of it routes by `EthCLLib.Spec.routeRight`, the same bit the shipped check
folds on. That convention belongs to `is_valid_merkle_branch`, a consensus-spec
function. The whole opening half therefore sits framework-side, and SizzLean
keeps only shape and width (`SizzLean.Proofs.Perfect`).

Both openers fall through silently on a shape mismatch. A caller therefore relies
on holding an `IsOpenable` witness, and not on the openers rejecting bad input.

`rootOf_eq_merkleRoot` licenses reading `siblingPath`'s cache reads as the honest
`Node.merkleRoot`, unconditionally. `merkleRoot_pair` is the single bridge that
collapses the cached and uncached readings of `Node.merkleRoot`.

The completeness proof (`Proofs/MerkleBranch.lean`) and the computational
witnesses (`Tests/MerkleWitness.lean`) both open a tree through this module. The
tested expressions and the proved ones therefore stay the same.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open SizzLean SizzLean.Hasher SizzLean.Cache.MerkleTree EthCLLib.Spec
open SizzLean.Proofs

/-! ### The path predicate -/

/-- A root-to-leaf *path* witness for `Node` at `index`: the spine the honest
opening walks. Where `IsPerfect` constrains the whole tree, `IsOpenable`
constrains only the followed child at each level. For the off-path sibling it
records the two facts completeness consumes, a 32-byte root and cache validity
at this level. `hc` says nothing about caches *inside* the sibling subtrees. An
`IsOpenable` tree may therefore carry poisoned ones, and completeness then proves
acceptance against that tree's own `merkleRoot`. Every `IsPerfect` tree is
`IsOpenable` at every index (`isOpenable_of_isPerfect`).

The base case stops at *any* node whose root is 32 bytes, not only a `.leaf`.
A path can therefore end on a subtree. That is what SSZ means by the leaf at a
generalized index, since `hash_tree_root` of a composite field is a subtree root.
`Node.rootOf (.leaf b) = b` definitionally, so a leaf-terminating path is the
special case, and it changes no deposit-shaped corollary. -/
inductive IsOpenable (H : Type) [Hasher H] : Node → Nat → Nat → Prop where
  | stop (m : Node) (hsz : (Node.rootOf H m).size = 32) (index : Nat) :
      IsOpenable H m 0 index
  | left {l r : Node} {d index : Nat} {c : Option ByteArray}
      (hbit : routeRight index d = false)
      (hl : IsOpenable H l d index)
      (hr32 : (Node.merkleRoot H r).size = 32)
      (hc : ∀ root, c = some root →
        root = Hasher.combine (H := H) (Node.merkleRoot H l) (Node.merkleRoot H r)) :
      IsOpenable H (.pair l r c) (d + 1) index
  | right {l r : Node} {d index : Nat} {c : Option ByteArray}
      (hbit : routeRight index d = true)
      (hr : IsOpenable H r d index)
      (hl32 : (Node.merkleRoot H l).size = 32)
      (hc : ∀ root, c = some root →
        root = Hasher.combine (H := H) (Node.merkleRoot H l) (Node.merkleRoot H r)) :
      IsOpenable H (.pair l r c) (d + 1) index

/-! ### The openers -/

/-- The 32-byte chunk at the end of `index`'s bits, read from the root of `n`,
most-significant bit (level `depth-1`) first. It is the root of whatever node
the path stops on.

The function is total. Its remaining arm, a `.leaf` asked to open at positive
depth, is unreachable under `IsOpenable` and falls through to
`SizzLean.Spec.zero32`, the canonical all-zero chunk.

That fallthrough is silent, so a caller without an `IsOpenable` witness in hand
gets a plausible-looking zero chunk out of a shape mismatch. Holding the witness
is what rules that out. The openers themselves report nothing. -/
def leafAt (H : Type) [Hasher H] : Node → (depth : Nat) → (index : Nat) → ByteArray
  | m,             0,     _     => Node.rootOf H m
  | .pair l r _,   d + 1, index =>
      if routeRight index d then leafAt H r d index else leafAt H l d index
  | _,             _,     _     => SizzLean.Spec.zero32

/-- `leafAt` at depth 0 is the stop node's root, whatever the node's shape.

The depth-0 arm above matches any `Node`, but the equation compiler splits on the
*node* first. The arm therefore does not fire while the node is an opaque
variable, and a `cases` has to show that no other arm applies. Stating that once
here keeps every base case downstream a plain rewrite. The same holds for
`siblingPath_zero` below. -/
theorem leafAt_zero (H : Type) [Hasher H] (m : Node) (index : Nat) :
    leafAt H m 0 index = Node.rootOf H m := by
  cases m <;> rfl

/-- The sibling hashes along the root path to the leaf at `index`, ordered
bottom-to-top. Index `0` is the leaf-level sibling, and index `depth-1` is the
sibling just under the root.

The recursion enters the chosen subtree first, then pushes this level's sibling,
the *other* subtree's root, at the end. The top sibling therefore lands at the
highest array index, which matches `isValidMerkleBranch`'s bit-`i`-at-level-`i`
fold.

Sibling roots come from `Node.rootOf`, the cache-reading observer, which
allocates nothing. It agrees with `Node.merkleRoot` on every `Node`
(`rootOf_eq_merkleRoot`), so reading a sibling's cache as its `merkleRoot` needs
no hypothesis. -/
def siblingPath (H : Type) [Hasher H] :
    Node → (depth : Nat) → (index : Nat) → Array ByteArray
  | .pair l r _,   d + 1, index =>
      if routeRight index d
      then (siblingPath H r d index).push (Node.rootOf H l)
      else (siblingPath H l d index).push (Node.rootOf H r)
  | _,             _,     _     => #[]

/-- A depth-0 opening has no siblings, whatever the node's shape. Needs the same
`cases` as `leafAt_zero`, for the same reason. -/
theorem siblingPath_zero (H : Type) [Hasher H] (m : Node) (index : Nat) :
    siblingPath H m 0 index = #[] := by
  cases m <;> rfl

/-- The node reached from the root of `n` by following `index`'s bits, most
significant first. Composition opens the *node* the first path reached, so it
needs this rather than `leafAt`.

The shape-mismatch arm returns `.leaf SizzLean.Spec.zero32`, so its root agrees
with `leafAt`'s own fallthrough without a side condition. -/
def nodeAt : Node → (depth : Nat) → (index : Nat) → Node
  | m,             0,     _     => m
  | .pair l r _,   d + 1, index =>
      if routeRight index d then nodeAt r d index else nodeAt l d index
  | _,             _,     _     => .leaf SizzLean.Spec.zero32

/-- `nodeAt` at depth 0 is the node itself. Needs the same `cases` as
`leafAt_zero`, for the same reason. -/
theorem nodeAt_zero (m : Node) (index : Nat) : nodeAt m 0 index = m := by
  cases m <;> rfl

/-- **The two openers agree.** `leafAt` is `nodeAt` followed by `Node.rootOf`.

Both recursions route on the same bit. Their shape-mismatch arms agree too:
`leafAt` returns `zero32`, and `nodeAt` returns `.leaf zero32`.

The completeness theorems state their leaf with `leafAt`. This lemma carries that
leaf into `Node.rootOf`, which `rootOf_ofShape_eq_hashTreeRoot` turns into a
`hash_tree_root`. -/
theorem leafAt_eq_rootOf_nodeAt (H : Type) [Hasher H] :
    ∀ (n : Node) (depth index : Nat),
      leafAt H n depth index = Node.rootOf H (nodeAt n depth index)
  | m,           0,     index => by
      rw [leafAt_zero, nodeAt_zero]
  | .pair l r c, d + 1, index => by
      show (if routeRight index d then leafAt H r d index else leafAt H l d index)
        = Node.rootOf H (if routeRight index d then nodeAt r d index else nodeAt l d index)
      cases routeRight index d
      · simpa using leafAt_eq_rootOf_nodeAt H l d index
      · simpa using leafAt_eq_rootOf_nodeAt H r d index
  | .leaf b,     d + 1, index => by
      show SizzLean.Spec.zero32 = Node.rootOf H (.leaf SizzLean.Spec.zero32)
      rw [Node.rootOf_leaf]

/-! ### Index arithmetic for path composition

Composing a depth-`d₁` path at `i₁` with a depth-`d₂` path at `i₂` addresses the
combined index `i₁ * 2 ^ d₂ + i₂`. Below `d₂` that index reads `i₂`'s bits, at
and above it reads `i₁`'s. Both lemmas cross into `Nat.testBit` first, through
`routeRight_eq_testBit`. -/

/-- Below the inner depth, the combined index reads the inner index's bits. -/
theorem routeRight_combine_low (i₁ i₂ d₂ k : Nat) (hk : k < d₂) :
    routeRight (i₁ * 2 ^ d₂ + i₂) k = routeRight i₂ k := by
  -- Bits below `d₂` depend only on the value mod `2 ^ d₂`, which the outer
  -- term, a multiple of `2 ^ d₂`, drops out of.
  rw [routeRight_eq_testBit, routeRight_eq_testBit]
  have hmod : ∀ x : Nat, Nat.testBit x k = Nat.testBit (x % 2 ^ d₂) k := by
    intro x
    rw [Nat.testBit_mod_two_pow]
    simp [hk]
  rw [hmod (i₁ * 2 ^ d₂ + i₂), hmod i₂, Nat.add_comm (i₁ * 2 ^ d₂) i₂,
      Nat.add_mul_mod_self_right]

/-- At and above the inner depth, the combined index reads the outer index's
bits, shifted down by `d₂`. `i₂ < 2 ^ d₂` is what makes the inner index vanish
under the division. -/
theorem routeRight_combine_high (i₁ i₂ d₂ k : Nat) (hi₂ : i₂ < 2 ^ d₂) :
    routeRight (i₁ * 2 ^ d₂ + i₂) (d₂ + k) = routeRight i₁ k := by
  rw [routeRight_eq_testBit, routeRight_eq_testBit,
      Nat.mul_comm i₁ (2 ^ d₂), Nat.testBit_two_pow_mul_add i₁ hi₂,
      if_neg (by omega : ¬ d₂ + k < d₂), Nat.add_sub_cancel_left]

/-! ### Sizes along an openable path -/

/-- `siblingPath` has exactly `depth` entries along an openable path. Each
constructor case knows its own bit, so the routing `if` reduces without a
mirrored `split`. -/
theorem siblingPath_size (H : Type) [Hasher H] :
    ∀ {n : Node} {depth index : Nat}, IsOpenable H n depth index →
      (siblingPath H n depth index).size = depth := by
  intro n depth index ho
  induction ho with
  | stop m hsz index => simp [siblingPath_zero]
  | left hbit _ _ _ ihl =>
      unfold siblingPath
      simp [hbit, Array.size_push, ihl]
  | right hbit _ _ _ ihr =>
      unfold siblingPath
      simp [hbit, Array.size_push, ihr]

/-- Each entry of `siblingPath` along an openable path is 32 bytes. Entries below
the top come from the sub-path IH. The top entry is the recorded sibling root,
whose width and honest cache the predicate carries. No `CombineWidth32` here,
because `IsOpenable` records the widths itself. -/
theorem siblingPath_entries_size (H : Type) [Hasher H] :
    ∀ {n : Node} {depth index : Nat}, IsOpenable H n depth index →
      ∀ i, i < depth → ((siblingPath H n depth index)[i]!).size = 32 := by
  intro n depth index ho
  induction ho with
  | stop m hsz index => intro i hi; omega
  | @left l r d index c hbit hl hr32 hc ihl =>
      intro i hi
      unfold siblingPath
      simp only [hbit, Bool.false_eq_true, if_false]
      have hsz : (siblingPath H l d index).size = d := siblingPath_size H hl
      rcases Nat.lt_or_ge i d with hid | hid
      · rw [getElem!_push_lt _ _ _ (by rw [hsz]; exact hid)]
        exact ihl i hid
      · have hi' : i = d := by omega
        have htop := getElem!_push_size (siblingPath H l d index) (Node.rootOf H r)
        rw [hsz] at htop
        rw [hi', htop, rootOf_eq_merkleRoot H r]
        exact hr32
  | @right l r d index c hbit hr hl32 hc ihr =>
      intro i hi
      unfold siblingPath
      simp only [hbit, if_true]
      have hsz : (siblingPath H r d index).size = d := siblingPath_size H hr
      rcases Nat.lt_or_ge i d with hid | hid
      · rw [getElem!_push_lt _ _ _ (by rw [hsz]; exact hid)]
        exact ihr i hid
      · have hi' : i = d := by omega
        have htop := getElem!_push_size (siblingPath H r d index) (Node.rootOf H l)
        rw [hsz] at htop
        rw [hi', htop, rootOf_eq_merkleRoot H l]
        exact hl32

/-- The chunk `leafAt` reaches along an openable path is 32 bytes: it is the stop
node's root, whose width the `IsOpenable.stop` witness carries directly. -/
theorem leafAt_size (H : Type) [Hasher H] :
    ∀ {n : Node} {depth index : Nat}, IsOpenable H n depth index →
      (leafAt H n depth index).size = 32 := by
  intro n depth index ho
  induction ho with
  | stop m hsz index => rw [leafAt_zero]; exact hsz
  | left hbit _ _ _ ihl => unfold leafAt; simp [hbit, ihl]
  | right hbit _ _ _ ihr => unfold leafAt; simp [hbit, ihr]

/-! ### Perfect trees are openable -/

/-- Every perfect tree is openable at every index. The followed child comes from
the same-depth subtree witness. The off-path sibling root is 32 bytes by
`merkleRoot_size`, which is why the statement needs `CombineWidth32`. Cache
validity at this level is `IsPerfect`'s own `hc`.

The name does not extend SizzLean's `IsPerfect` namespace, since the conclusion
is an EthCLLib predicate. A `SizzLean.Cache.MerkleTree.IsPerfect.isOpenable`
would put a framework-typed declaration inside the SSZ library's namespace, which
is the coupling this split removes. -/
theorem isOpenable_of_isPerfect {H : Type} [Hasher H] [CombineWidth32 H] :
    ∀ {n : Node} {d : Nat}, IsPerfect H n d → ∀ (index : Nat),
      IsOpenable H n d index := by
  intro n d hp
  induction hp with
  | leaf b hsz =>
      intro index
      exact .stop (.leaf b) (by rw [Node.rootOf_leaf]; exact hsz) index
  | @pair l r d c hl hr hc ihl ihr =>
      intro index
      cases hbit : routeRight index d
      · exact .left hbit (ihl index) (merkleRoot_size H hr) hc
      · exact .right hbit (ihr index) (merkleRoot_size H hl) hc

/-! ### Path composition -/

/-- An openable path depends on the index only through its low `depth` bits.
Composition needs it, since the outer witness holds at `i₁` and has to be re-read
at the combined index. -/
theorem IsOpenable.index_congr {H : Type} [Hasher H] :
    ∀ {n : Node} {d i : Nat}, IsOpenable H n d i → ∀ (j : Nat),
      (∀ k, k < d → routeRight i k = routeRight j k) →
      IsOpenable H n d j := by
  intro n d i ho
  induction ho with
  | stop m hsz _ => intro j _; exact .stop m hsz j
  | @left l r d i c hbit hl hr32 hc ih =>
      intro j hbits
      refine .left (by rw [← hbits d (Nat.lt_succ_self d)]; exact hbit)
        (ih j (fun k hk => hbits k (Nat.lt_succ_of_lt hk))) hr32 hc
  | @right l r d i c hbit hr hl32 hc ih =>
      intro j hbits
      refine .right (by rw [← hbits d (Nat.lt_succ_self d)]; exact hbit)
        (ih j (fun k hk => hbits k (Nat.lt_succ_of_lt hk))) hl32 hc

/-- **Path composition.** Take an openable path of depth `d₁`, then an openable
path of depth `d₂` out of the node it reached. Together they are an openable
path of depth `d₁ + d₂` at the concatenated index, with the outer path holding
the high bits.

A generalized index descending through a container field into that field's own
tree is exactly this. -/
theorem IsOpenable.trans {H : Type} [Hasher H] :
    ∀ {n : Node} {d₁ i₁ : Nat}, IsOpenable H n d₁ i₁ →
      ∀ {d₂ i₂ : Nat}, IsOpenable H (nodeAt n d₁ i₁) d₂ i₂ → i₂ < 2 ^ d₂ →
        IsOpenable H n (d₁ + d₂) (i₁ * 2 ^ d₂ + i₂) := by
  intro n d₁ i₁ h₁
  induction h₁ with
  | stop m hsz i₁ =>
      intro d₂ i₂ h₂ hi₂
      -- `nodeAt m 0 i₁ = m`, and `0 + d₂ = d₂`, so the inner witness is the
      -- whole thing once its index is re-read at the combined value.
      rw [nodeAt_zero] at h₂
      simp only [Nat.zero_add]
      exact h₂.index_congr _ (fun k hk => (routeRight_combine_low i₁ i₂ d₂ k hk).symm)
  | @left l r d i₁ c hbit hl hr32 hc ih =>
      intro d₂ i₂ h₂ hi₂
      have h₂' : IsOpenable H (nodeAt l d i₁) d₂ i₂ := by simpa [nodeAt, hbit] using h₂
      -- The constructor builds depth `(d + d₂) + 1`, the goal reads `d + 1 + d₂`.
      -- Equal but not defeq while `d₂` is a variable, so say so explicitly.
      rw [show d + 1 + d₂ = (d + d₂) + 1 by omega]
      refine .left ?_ (ih h₂' hi₂) hr32 hc
      -- Bit `d + d₂` of the combined index is bit `d` of `i₁`, which `hbit` fixes.
      rw [Nat.add_comm d d₂, routeRight_combine_high i₁ i₂ d₂ d hi₂]
      exact hbit
  | @right l r d i₁ c hbit hr hl32 hc ih =>
      intro d₂ i₂ h₂ hi₂
      have h₂' : IsOpenable H (nodeAt r d i₁) d₂ i₂ := by simpa [nodeAt, hbit] using h₂
      rw [show d + 1 + d₂ = (d + d₂) + 1 by omega]
      refine .right ?_ (ih h₂' hi₂) hl32 hc
      rw [Nat.add_comm d d₂, routeRight_combine_high i₁ i₂ d₂ d hi₂]
      exact hbit

/-! **Pin: composition concatenates the index, outer bits high.** Leaves sit in
index order, so opening at `k` reaches leaf `k`. Composing at `i₁ = 1`, `i₂ = 1`
addresses `1 * 2 ^ 2 + 1 = 5`. The last conjunct holds leaf 3, where a
swapped-operand reading would have sent it. -/
#guard
  let mk : UInt8 → ByteArray := fun v => ByteArray.mk (Array.replicate 32 v)
  let t : Node :=
    .pair
      (.pair (.pair (.leaf (mk 0)) (.leaf (mk 1)) none)
             (.pair (.leaf (mk 2)) (.leaf (mk 3)) none) none)
      (.pair (.pair (.leaf (mk 4)) (.leaf (mk 5)) none)
             (.pair (.leaf (mk 6)) (.leaf (mk 7)) none) none)
      none
  (leafAt Sha256Spec t 3 5).toList == (mk 5).toList
    && (leafAt Sha256Spec (nodeAt t 1 1) 2 1).toList == (mk 5).toList
    && (leafAt Sha256Spec t 3 3).toList == (mk 3).toList

/-! ### Trees the builders produce -/

/-- Both halves of a `2 ^ (d + 1)`-bounded list are `2 ^ d`-bounded, which
`ofSubtrees_isOpenable`'s half-splitting induction opens on. -/
private theorem take_drop_length_le {α : Type} (xs : List α) (d : Nat)
    (hlen : xs.length ≤ 2 ^ (d + 1)) :
    (xs.take (2 ^ d)).length ≤ 2 ^ d ∧ (xs.drop (2 ^ d)).length ≤ 2 ^ d := by
  have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
  refine ⟨?_, ?_⟩
  · rw [List.length_take]; omega
  · rw [List.length_drop]; omega

/-- **`ofSubtrees` is openable at every position.** Take the balanced tree over
at most `2 ^ depth` sub-trees, padded right with `zeroLeaf`. It admits a
root-to-leaf path at any `k`, and stops on the sub-tree there.

`k` is a bare `Nat`. Past capacity it routes on its low `depth` bits and lands
at `k % 2 ^ depth`, as the spec's `is_valid_merkle_branch` also does.

The induction threads the capacity bound. `take_drop_length_le` splits it across
the two halves, and each half hands its share to the induction hypothesis. Only
the depth-0 base case ignores it.

The bound is there because `ofSubtrees` truncates an over-capacity list without
saying so.
The spec instead refuses ("if `limit < len(chunks)`: do not merkleize, input
exceeds limit", `ssz/simple-serialize.md:381-382`).

This is the container and composite-list shape. `Node.ofShape` builds a
`container fs` as `ofSubtrees` over the field sub-trees at depth
`chunkDepth fs.length` (`Build.lean:188`). It builds a composite `vector` the
same way (`:172`). It builds a composite `list` at `chunkDepth cap`, where the
bound arrives as `len ≤ cap ≤ 2 ^ chunkDepth cap` (`:184`). -/
theorem ofSubtrees_isOpenable (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero : ∀ d, IsPerfect H (zeroLeaf H d) d) :
    ∀ (depth : Nat) (subs : List Node),
      subs.length ≤ 2 ^ depth →
      (∀ s ∈ subs, (Node.rootOf H s).size = 32) →
      ∀ k, IsOpenable H (Node.ofSubtrees H subs depth) depth k := by
  intro depth
  induction depth with
  | zero =>
      -- At depth 0 the bound admits at most one sub-tree, and either arm stops
      -- immediately.
      intro subs _hlen hsz k
      cases subs with
      | nil =>
          refine .stop _ ?_ k
          rw [rootOf_eq_merkleRoot]
          exact merkleRoot_size H (hzero 0)
      | cons s tl => exact .stop s (hsz s (by simp)) k
  | succ d ih =>
      intro subs hlen hsz k
      obtain ⟨hLlen, hRlen⟩ := take_drop_length_le subs d hlen
      have hL : ∀ s ∈ subs.take (2 ^ d), (Node.rootOf H s).size = 32 :=
        fun s hs => hsz s (List.take_subset _ _ hs)
      have hR : ∀ s ∈ subs.drop (2 ^ d), (Node.rootOf H s).size = 32 :=
        fun s hs => hsz s (List.drop_subset _ _ hs)
      unfold Node.ofSubtrees
      simp only [List.splitAt_eq]
      -- The right half is either more sub-trees or, once they run out, a
      -- `zeroLeaf` pad. Both are openable and both have a 32-byte root. The
      -- cache obligation is the same either way, inlined per arm.
      cases hbit : routeRight k d
      · refine .left hbit (ih _ hLlen hL k) ?_ ?_
        · by_cases hre : (subs.drop (2 ^ d)).isEmpty = true
          · rw [if_pos hre]; exact merkleRoot_size H (hzero d)
          · rw [if_neg hre]; exact merkleRoot_ofSubtrees_size H hzero d _ hR
        · exact cached_root_honest H _ _
      · refine .right hbit ?_ (merkleRoot_ofSubtrees_size H hzero d _ hL) ?_
        · by_cases hre : (subs.drop (2 ^ d)).isEmpty = true
          · rw [if_pos hre]; exact isOpenable_of_isPerfect (hzero d) k
          · rw [if_neg hre]; exact ih _ hRlen hR k
        · exact cached_root_honest H _ _

/-! ### The root-typed sugar -/

/-- The honest leaf opening at `index`: the root of the node the path stops on,
root-typed.

No width hypothesis: `bytesToRoot` zero-pads a short buffer rather than failing,
so this silently widens a malformed tree (see the `#guard` below). The theorems
are safe because `IsOpenable.stop` carries
`hsz : (Node.rootOf H m).size = 32`. -/
def honestLeaf (H : Type) [Hasher H] (n : Node) (depth index : Nat) : Vector UInt8 32 :=
  bytesToRoot (leafAt H n depth index)

/-- The honest branch opening at `index`: the sibling path, root-typed entrywise.
Same absent width hypothesis as `honestLeaf`, applied per entry. -/
def honestBranch (H : Type) [Hasher H] (n : Node) (depth index : Nat) :
    Array (Vector UInt8 32) :=
  (siblingPath H n depth index).map bytesToRoot

/-! **Pin: the sugar zero-pads a wrong-width leaf.** A 3-byte leaf opened at
depth 0 comes back widened to 32. `honestBranch` returns an empty array, whose
size matches depth 0. -/
#guard
  let b : ByteArray := ByteArray.mk #[1, 2, 3]
  (honestLeaf Sha256Spec (.leaf b) 0 0).toList == [1, 2, 3] ++ List.replicate 29 0
    && (honestBranch Sha256Spec (.leaf b) 0 0).size == 0

/-- `bytesToRoot` then `vecToBytes` is the identity on exactly-32-byte buffers.
`bytesToRoot b` reads the 32 bytes of `b` into a vector, and `vecToBytes`
unwraps it. The composite is `b` iff `b` has exactly its 32 bytes. For
`b.size ≠ 32` it truncates or zero-pads, which is why the hypothesis is there. -/
theorem vecToBytes_bytesToRoot (b : ByteArray) (hsz : b.size = 32) :
    vecToBytes (bytesToRoot b) = b := by
  apply ByteArray.ext
  show (Vector.ofFn (fun i : Fin 32 => b.get! i.val)).toArray = b.data
  rw [Vector.toArray_ofFn]
  apply Array.ext
  · rw [Array.size_ofFn]; exact (ByteArray.size_data.trans hsz).symm
  · intro i h1 h2
    rw [Array.getElem_ofFn, SizzLean.Proofs.get!_eq_getElem b i h2,
        ByteArray.getElem_eq_getElem_data]

end EthCLLib.Proofs
