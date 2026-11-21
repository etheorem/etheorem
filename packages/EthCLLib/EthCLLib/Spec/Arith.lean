import SizzLean

/-!
# `EthCLLib.Spec.Arith`: the arithmetic, byte, and collection layer

Domain-agnostic numeric and serialization utilities the spec calls
(`FRAMEWORK_ARCHITECTURE.md` §10). Spec arithmetic is not here. A spec integer
computes through the checked surface (`SPEC_ARITHMETIC.md` §4): `CLUint64` and
`CLUint8` in `Spec/CLUint.lean`, `CLInt` in `Spec/CLInt.lean`, and the
proved-total routes in `Spec/CLTotal.lean`. The helpers here work on structural
`Nat` values, on bytes as data, and on raw machine words inside proved-total
framework routes (`SPEC_ARITHMETIC.md` §7, rule 5). The raw `UInt64` helpers
`umax`, `umin`, and `saturatingSub` have no fork-body caller. Their checked
forms are the `Max` / `Min` instances and `CLUint64.saturatingSub`.

`uintToBytes` is **type-directed**: the byte width follows from the value's type
through `UIntToBytes`, removing the 4-versus-8-byte serialization bug class by
never letting the author pick the width by hand.

The collection helpers (`sszDrop`, `vget`, `bitGet` / `bitSet`) are total. A bit write
past the end changes nothing, and an out-of-range read returns the default. Use them
only at a position the caller already knows is in range, such as a fixed byte offset.
A read where the pyspec can raise `IndexError` goes through the size-aware
`sszGetIdx` / `getAt` (`Spec/State.lean`, `SPEC_ARITHMETIC.md` §4.6).
`sszOfArray` takes a proof that the array fits. A list whose length is known only at
run time goes through `sszOfArrayM` (`Spec.Header`), which raises as the spec's
`List[T, N](...)` does. A boxed-state field reads and writes through SizzLean's
`sszGet` / `sszUpdate` index forms: `f[i]` rejects on a miss, and the total `f[i]!`
is for an index already known to be in range.
-/

set_option autoImplicit false

open SizzLean.Repr

namespace EthCLLib.Spec

/-! ## Re-exported SSZ collection types

The variable-length SSZ collection types a spec body names in container fields and
signatures live in `SizzLean.Repr`. Re-export them here so `open EthCLLib.Spec`
alone brings the author surface into scope (`SPEC_AUTHORING_MODEL.md` §3.2), with
no second `open SizzLean.Repr`. The fixed-length `Vector` is core Lean; the boxed
`State` representation (`SizzLean.Cache`) stays behind `sszGet` / `sszUpdate` and is
deliberately not re-exported. -/
export SizzLean.Repr (SSZList Bitvector Bitlist ProgressiveList ProgressiveBitlist)

/-! ## `UInt64` arithmetic -/

/-- `max` on raw `UInt64`. No fork body calls it: the checked `max` is the
`Max CLUint64` instance (`Spec/CLUint.lean`). -/
@[inline] def umax (a b : UInt64) : UInt64 := if a < b then b else a
/-- `min` on raw `UInt64`. No fork body calls it: the checked `min` is the
`Min CLUint64` instance. -/
@[inline] def umin (a b : UInt64) : UInt64 := if a < b then a else b
/-- `saturating_sub(a, b)` (`phase0/beacon-chain.md:1038-1042`): `a - b`, floored at zero.
The spec writes the floor as `a - a`, which keeps the result's type; on `UInt64` that is
`0`. Total: the subtraction runs only when `a > b`, so it cannot wrap. This is the raw-word
form, with no fork-body caller. The spec bodies use `CLUint64.saturatingSub`
(`Spec/CLUint.lean`). -/
@[inline] def saturatingSub (a b : UInt64) : UInt64 := if a > b then a - b else 0

/-- Newton's-iteration integer square root over `Nat`, fuel-bounded so it is
total and kernel-reducible. It is the iteration behind the spec's `integer_squareroot`,
which `CLUint64.integerSquareroot` (`Spec/CLTotal.lean`) wraps. 200 steps converges
for any `Nat` below `2^64·N`. -/
def isqrtAux (n : Nat) : Nat → Nat → Nat
  | 0,        x => x
  | fuel + 1, x => let y := (x + n / x) / 2; if y < x then isqrtAux n fuel y else x

/-- `⌊√n⌋`. -/
def isqrt (n : Nat) : Nat := if n = 0 then 0 else isqrtAux n 200 n

/-- Newton's iteration never climbs above its start: each step either moves to a
smaller `y` or stops at `x`. -/
theorem isqrtAux_le (n : Nat) : ∀ (fuel x : Nat), isqrtAux n fuel x ≤ x
  | 0, x => Nat.le_refl x
  | fuel + 1, x => by
    show (if (x + n / x) / 2 < x then isqrtAux n fuel ((x + n / x) / 2) else x) ≤ x
    split
    · rename_i h
      exact Nat.le_trans (isqrtAux_le n fuel _) (Nat.le_of_lt h)
    · exact Nat.le_refl x

/-- The root is at most its argument, so a root of a `uint64` value fits a
`uint64` (the range premise of `CLUint64.integerSquareroot`). -/
theorem isqrt_le (n : Nat) : isqrt n ≤ n := by
  unfold isqrt
  split
  · omega
  · exact isqrtAux_le n 200 n

/-! ## Type-directed `uintToBytes` -/

/-- Little-endian serialization whose width is fixed by the type, the
width-from-type discipline of `FRAMEWORK_ARCHITECTURE.md` §10. -/
class UIntToBytes (α : Type) where
  /-- The little-endian byte serialization of a `uintN` value. -/
  toBytes : α → ByteArray

/-- `uint_to_bytes` for `uint64`: 8 little-endian bytes. -/
def uint64ToBytes (x : UInt64) : ByteArray :=
  ⟨Array.ofFn (n := 8) (fun i => (x >>> (UInt64.ofNat (8 * i.val))).toUInt8)⟩

/-- `uint_to_bytes` for `uint32`: 4 little-endian bytes. -/
def uint32ToBytes (x : UInt32) : ByteArray :=
  ⟨Array.ofFn (n := 4) (fun i => (x >>> (UInt32.ofNat (8 * i.val))).toUInt8)⟩

instance : UIntToBytes UInt64 := ⟨uint64ToBytes⟩
instance : UIntToBytes UInt32 := ⟨uint32ToBytes⟩
instance : UIntToBytes UInt8  := ⟨fun x => ⟨#[x]⟩⟩

/-- The type-directed serializer: `uintToBytes x` picks the width from `x`'s type. -/
@[inline] def uintToBytes {α : Type} [UIntToBytes α] (x : α) : ByteArray :=
  UIntToBytes.toBytes x

/-! ## Byte conversions -/

/-- A `ByteArray` from a fixed-length byte `Vector` (e.g. a `Root` / pubkey to the
crypto seam's wire bytes). -/
@[inline] def vecToBytes {n : Nat} (v : Vector UInt8 n) : ByteArray := ⟨v.toArray⟩

/-- A fixed-length byte `Vector` from a `ByteArray`'s first `n` bytes (out-of-range
positions read `0`); the inverse of `vecToBytes` for a well-sized buffer. -/
@[inline] def bytesToVec (n : Nat) (b : ByteArray) : Vector UInt8 n :=
  Vector.ofFn (fun i : Fin n => b.get! i.val)

/-- A 32-byte hash-tree-root `ByteArray` as a `Vector UInt8 32`. -/
@[inline] def bytesToRoot (b : ByteArray) : Vector UInt8 32 := bytesToVec 32 b

/-- First 8 bytes of `b` as a little-endian `Nat` (`bytes_to_uint64`). -/
def le8 (b : ByteArray) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (b.get! i).toNat * (256 ^ i)) 0

/-- 4 little-endian bytes of a `Nat` (`int.to_bytes(4, "little")`). -/
def u32leBytes (x : Nat) : ByteArray :=
  ⟨Array.ofFn (n := 4) (fun i => UInt8.ofNat ((x >>> (8 * i.val)) % 256))⟩

/-- Two bytes at offset `off` as a little-endian `Nat` (`bytes_to_uint64` on 2 bytes). -/
def le2 (b : ByteArray) (off : Nat) : Nat := (b.get! off).toNat + (b.get! (off + 1)).toNat * 256

/-! ## Collections (total) -/

/-- Read a `Vector` element by `Nat` index; the default past the end. -/
@[inline] def vget {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) : α :=
  v.toArray[i]!

/-- Whether the `len`-long slice of `a` at offset `aOff` equals the slice of `b` at offset
`bOff`, element by element (out-of-range positions read each vector's default, like `vget`).
Names the fixed-window byte comparison the withdrawal-credential / execution-address checks
repeat (`vecSliceEq creds 12 address 0 20`), so the slice's index arithmetic is written once. -/
@[inline] def vecSliceEq {α : Type} [BEq α] [Inhabited α] {n m : Nat}
    (a : Vector α n) (aOff : Nat) (b : Vector α m) (bOff len : Nat) : Bool :=
  (List.range len).all (fun k => vget a (aOff + k) == vget b (bOff + k))

/-- Shift a ring-window down by `shift` and refill the tail. The first `keep` slots copy `v`
read forward by `shift` (`vget`, defaulting past the end); the remaining `m - keep` slots come
from `fill` keyed by the tail offset `j - keep`. Names the "shift the window down by
`SLOTS_PER_EPOCH` and pad" step the ePBS rolling windows repeat
(`process_builder_pending_payments`, `process_ptc_window`), so the threshold and the shift
offset are written once. The output length matches the source, so it drops straight into the
`Vector`-typed field it updates. The pad shape is the caller's: a constant (`fun _ => empty`)
or an index-keyed refill (`fun k => fresh[k]!`). -/
@[inline] def shiftWindow {α : Type} [Inhabited α] {m : Nat}
    (v : Vector α m) (shift keep : Nat) (fill : Nat → α) : Vector α m :=
  Vector.ofFn (fun j : Fin m =>
    if j.val < keep then vget v (j.val + shift) else fill (j.val - keep))

/-- A `UInt64` taken mod `n` lands in `[0, n)` once read back as a `Nat`, given `n`
positive and in range. The bound behind `vmodGet`, the proof-carrying read into a
length-`n` vector at a `(x % UInt64.ofNat n).toNat` index. The raw `%` is the
proved-total route `SPEC_ARITHMETIC.md` §6 allows: a modulo by a positive preset length
needs no range test. The two premises hold for any sane preset (a vector length is
positive and far below `2^64`); a symbolic preset supplies them from its positivity
invariant. -/
theorem uint64ModOfNatToNatLt (x : UInt64) (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 64) :
    (x % UInt64.ofNat n).toNat < n := by
  have h : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt hb
  rw [UInt64.toNat_mod, h]
  exact Nat.mod_lt _ hn

/-- A `Nat` usable as a `uint64` modulus into a vector: positive and `< 2 ^ 64`. The
preset's vector-length constants are registered as instances (in `EthCLSpecs`), so a
modulo read names only the divisor and lets the proofs resolve. -/
class ValidModulus (d : Nat) where
  /-- The modulus is positive (`x % 0 = x` carries no bound). -/
  pos : 0 < d
  /-- The modulus fits a `uint64`. -/
  lt : d < 2 ^ 64

/-- Read `v` at the `uint64` index `x` reduced mod the period `d`, the "ring-buffer" read
(the RANDAO mixes, the block roots, the proposer-lookahead / PTC windows). The caller
passes the raw word of a checked index (`epoch.val`, `slot.val`); the raw `%` runs only
here, behind the `ValidModulus` proof (`SPEC_ARITHMETIC.md` §6). `d` divides into the
vector (`d ≤ n`, discharged by `omega` from the lengths), and the in-bounds proof comes
from `uint64ModOfNatToNatLt` plus the `[ValidModulus d]` instance, so the call names only
the vector, the index, and the period. A proof-carrying read, so no `Inhabited` default. -/
@[inline] def vmodGet {α : Type} {n : Nat} (v : Vector α n) (x : UInt64) (d : Nat)
    [vd : ValidModulus d] (hle : d ≤ n := by omega) : α :=
  v[(x % UInt64.ofNat d).toNat]'(by have := uint64ModOfNatToNatLt x d vd.pos vd.lt; omega)

/-- A list that can drop a prefix and stay the same collection type.
`SSZList` keeps its cap (the tail is no longer); `ProgressiveList` has no cap. -/
class SszDrop (ρ : Type) where
  drop : ρ → Nat → ρ

/-- Drop the first `k` elements. On an `SSZList` the cap is unchanged. -/
@[inline] def sszDrop {ρ : Type} [SszDrop ρ] (xs : ρ) (k : Nat) : ρ :=
  SszDrop.drop xs k

instance {α : Type} {cap : Nat} : SszDrop (SSZList α cap) where
  drop xs k :=
    ⟨xs.val.extract k xs.val.size, by have := xs.property; simp only [Array.size_extract]; omega⟩

instance {α : Type} : SszDrop (ProgressiveList α) where
  drop xs k := xs.drop k

/-- An `SSZList` from an array that fits, the spec's `List[T, N](a)`. The caller passes
the proof that `a.size ≤ cap` at the call site, `by decide` or `by simp` on the fixed
sizes, so the obligation is visible where it is paid and this form has no failure branch.
An array whose size depends on the input goes through `sszOfArrayM`, which raises on too
many elements as pyspec does. A `ProgressiveList` has no cap, so its one-field wrapper
takes the array whole: `⟨a⟩`. -/
def sszOfArray {α : Type} {cap : Nat} (a : Array α)
    (h : a.size ≤ cap) : SSZList α cap :=
  ⟨a, h⟩

/-- Intersection by membership: the elements of `xs` that also appear in `ys`, kept in `xs`'s
order. A `filter`, so it does not deduplicate `xs` itself; a value repeated in `xs` and present
in `ys` survives once per occurrence. Names the intersect-the-two-index-sets step
`on_attester_slashing` runs (`attestation1`'s indices filtered by membership in `attestation2`'s),
where the surviving order then feeds the equivocating-index merge. -/
@[inline] def arrayInter {α : Type} [BEq α] (xs ys : Array α) : Array α :=
  xs.filter (ys.contains ·)

/-- Dedup-append union: `xs` followed by the elements of `ys` not already present, appended in
`ys`'s order with each candidate tested against the running result. So `xs` is copied as is (its
own duplicates, if any, preserved) and `ys` contributes each new value once. Names the
insertion-order-preserving merge `on_attester_slashing` folds new equivocators onto
`store.equivocating_indices`. The resulting order matters: it feeds the fork-choice
weight computation, so the fold keeps the first-seen position rather than re-sorting. -/
@[inline] def arrayUnion {α : Type} [BEq α] (xs ys : Array α) : Array α :=
  ys.foldl (init := xs) fun acc i => if acc.contains i then acc else acc.push i

/-! ## Bit arrays and participation flags -/

/-- Set bit `i` of a `Bitvector n` to `b`. -/
def bitSet {n : Nat} (bv : Bitvector n) (i : Nat) (b : Bool) : Bitvector n :=
  let mask : BitVec n := (BitVec.ofNat n 1) <<< i
  { data := if b then bv.data ||| mask else bv.data &&& (~~~ mask) }

/-- Read bit `i` of a `Bitvector n` (LSB-first; `false` past the end). -/
def bitGet {n : Nat} (bv : Bitvector n) (i : Nat) : Bool := bv.data.getLsbD i

/-- The set bit positions of a `Bitvector n`, ascending (`0 … n-1`). Names the
`mut out / for i / if bitGet bv i then push i` walk that `get_committee_indices` and the
sync-aggregate participant select repeat. Reuses `bitGet` (the same LSB-first read, `false`
past the end, though here `i < n` always), so the bit-read convention stays in one place.
Same iteration and push order as the longhand loop. -/
def Bitvector.trueIndices {n : Nat} (bv : Bitvector n) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:n] do
    if bitGet bv i then out := out.push i
  return out

end EthCLLib.Spec
