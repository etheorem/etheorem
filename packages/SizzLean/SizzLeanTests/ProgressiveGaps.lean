import SizzLean.Hasher.Sha256
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLean.Repr.Deriving

/-!
# `SizzLeanTests.ProgressiveGaps`: progressive containers with mask holes

`@[sizzlean_progressive_gaps p₁ p₂ …]` names the `active_fields`
positions that no field occupies (EIP-7495). A fork writes it when it
removes fields from a progressive container and keeps the later fields
at their old positions: the Heze `BeaconState` drops the eth1 fields
with `active_fields(width=46, gaps=(8, 9, 10, 28))` (EIP-8015).

The gates below run one small container through every layer the
attribute reaches:

1. the derived shape carries the `false` bit;
2. the wire bytes skip the hole;
3. the spec root matches an independent oracle;
4. the cached box roots to the spec root, before and after an
   `sszUpdate`, so the progressive cache path rebuilds over the hole.

The oracle is the pyspec's own SSZ library (`eth-ssz-specs` 0.1.0,
the dependency `consensus-specs` v1.7.0-beta.4 pins). The value
`Gapped(side=0x0102, color=7)` with `active_fields(width=3, gaps=(1,))`
serializes to `02 01 07` and roots to the digest in `gappedRootHex`.
The root is a `Sha256` (FFI) digest, so the checks close by
`native_decide` (CLAUDE.md, *Proofs involving SSZ hashes*, case 2).
Gate 2 carries no hash and closes by `native_decide` for a parallel
reduction reason: the mutual `serialize` block compiles to
`WellFounded.fix`, which the kernel cannot reduce.
-/

set_option autoImplicit false

namespace SizzLeanTests.ProgressiveGaps

open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

/-- The EIP-7495 `Square(active_fields=[1, 0, 1])` shape: two fields
around one hole. -/
@[sizzlean_progressive, sizzlean_progressive_gaps 1]
structure Gapped where
  side  : UInt16
  color : UInt8
  deriving Inhabited, SSZRepr

/-- Gate 1: the hole is a `false` bit between the two `true` bits, and
the field list holds only the two active shapes. Definitional, so
`rfl` rejects a handler that ignores the gaps. -/
example : SSZRepr.shape (T := Gapped) =
    .progressiveContainer [true, false, true] [.uintN 16, .uintN 8] := rfl

private def value : Gapped := { side := 0x0102, color := 7 }

/-- Gate 2: only the active fields are on the wire, so the hole costs no
bytes. It closes by `native_decide` because the mutual `serialize`
block compiles to `WellFounded.fix`, which the kernel cannot reduce
(CLAUDE.md, *Proofs involving SSZ hashes*, the Default rule's
hash-free exception). -/
example : SSZ.serialize value = ⟨#[0x02, 0x01, 0x07]⟩ := by native_decide

/-- Lowercase hex of a byte string, for the comparison with the oracle. -/
private def toHex (b : ByteArray) : String :=
  b.foldl (init := "") fun acc x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    acc ++ (if s.length == 1 then "0" ++ s else s)

/-- The oracle root of `value` (see the module docstring). -/
private def gappedRootHex : String :=
  "c8031bede33dc963e466f8a56079181fb415177732fae6bbd3bd55cce8530ec1"

/-- Gate 3: the spec root places a zero chunk at the hole and mixes in
the `[1, 0, 1]` mask. -/
example : toHex (SSZ.hashTreeRoot Sha256 value) = gappedRootHex := by native_decide

/-- Gate 4: the cached box agrees with the spec root, and an update to
the field after the hole keeps it in agreement. -/
private def cachedAgrees : Bool :=
  let b := SSZ.FastBox value
  let (root0, b) := b.hashTreeRoot
  let b := sszUpdate b with color := 9
  root0 == SSZ.hashTreeRoot Sha256 value
    && b.hashTreeRoot.1 == SSZ.hashTreeRoot Sha256 { value with color := 9 }

example : cachedAgrees = true := by native_decide

/-! ### Rejected layouts

The handler checks the layout at derive time, so a malformed one is a
build error at its declaration and never a wrong root. -/

/--
error: deriving SSZRepr: 'SizzLeanTests.ProgressiveGaps.TrailingGap': the last position 2 is a gap, so the mask would end in a 0
-/
#guard_msgs in
@[sizzlean_progressive, sizzlean_progressive_gaps 2]
structure TrailingGap where
  a : UInt8
  b : UInt8
  deriving SSZRepr

/--
error: deriving SSZRepr: 'SizzLeanTests.ProgressiveGaps.UnorderedGaps': gaps must ascend strictly, got #[2, 1]
-/
#guard_msgs in
@[sizzlean_progressive, sizzlean_progressive_gaps 2 1]
structure UnorderedGaps where
  a : UInt8
  b : UInt8
  deriving SSZRepr

/--
error: deriving SSZRepr: 'SizzLeanTests.ProgressiveGaps.ClassicWithGaps' has @[sizzlean_progressive_gaps] but not @[sizzlean_progressive]
-/
#guard_msgs in
@[sizzlean_progressive_gaps 1]
structure ClassicWithGaps where
  a : UInt8
  b : UInt8
  deriving SSZRepr

end SizzLeanTests.ProgressiveGaps
