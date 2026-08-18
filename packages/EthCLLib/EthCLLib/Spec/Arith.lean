import SizzLean

/-!
# `EthCLLib.Spec.Arith`: the arithmetic, byte, and collection layer

Domain-agnostic numeric and serialization utilities the spec calls
(`FRAMEWORK_ARCHITECTURE.md` §10). Arithmetic stays in `UInt64` matching SSZ
`uint64` semantics; `Nat` is the fallback only for an intermediate that a
faithful operation order pushes above `2^64` (the committee math's `isqrt` over a
total balance), narrowed back with an exact conversion, never a reject.

`uintToBytes` is **type-directed**: the byte width follows from the value's type
through `UIntToBytes`, removing the 4-versus-8-byte serialization bug class by
never letting the author pick the width by hand.

The collection helpers (`sszDrop` / `sszOfArray`, `vget`,
`bitGet` / `bitSet`) are total: a write past capacity clamps, an out-of-range read
returns the default, so a spec step stays total (the pure-config requirement) with
no panic. Element reads and writes on a boxed-state field go through SizzLean's
`sszGet`/`sszUpdate` index forms (`f[i]!` total, `f[i]` reject-on-miss) directly.
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
export SizzLean.Repr (SSZList Bitvector Bitlist)

/-! ## `UInt64` arithmetic -/

/-- `max` on `UInt64`. -/
@[inline] def umax (a b : UInt64) : UInt64 := if a < b then b else a
/-- `min` on `UInt64`. -/
@[inline] def umin (a b : UInt64) : UInt64 := if a < b then a else b

/-- Newton's-iteration integer square root over `Nat`, fuel-bounded so it is
total and kernel-reducible (the spec's `integer_squareroot`). 200 steps converges
for any `Nat` below `2^64·N`. -/
def isqrtAux (n : Nat) : Nat → Nat → Nat
  | 0,        x => x
  | fuel + 1, x => let y := (x + n / x) / 2; if y < x then isqrtAux n fuel y else x

/-- `⌊√n⌋`. -/
def isqrt (n : Nat) : Nat := if n = 0 then 0 else isqrtAux n 200 n

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
positive and in range. The bound for a proof-carrying read into a length-`n` vector at a
`(x % UInt64.ofNat n).toNat` index (`process_randao`'s mix slot, the slashings / payment
ring buffers): `v[(x % UInt64.ofNat n).toNat]'(uint64ModOfNatToNatLt …)`. The two premises
hold for any sane preset (a vector length is positive and far below `2^64`); a symbolic
preset supplies them from its positivity invariant. -/
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
(`process_randao`'s mix slot, the proposer-lookahead / PTC windows). `d` divides into the
vector (`d ≤ n`, discharged by `omega` from the lengths), and the in-bounds proof comes
from `uint64ModOfNatToNatLt` plus the `[ValidModulus d]` instance, so the call names only
the vector, the index, and the period. A proof-carrying read, so no `Inhabited` default. -/
@[inline] def vmodGet {α : Type} {n : Nat} (v : Vector α n) (x : UInt64) (d : Nat)
    [vd : ValidModulus d] (hle : d ≤ n := by omega) : α :=
  v[(x % UInt64.ofNat d).toNat]'(by have := uint64ModOfNatToNatLt x d vd.pos vd.lt; omega)

/-- The ring-buffer index `x % d` as a `Nat`, the write-side companion of `vmodGet`'s read
index. Names the `(x % UInt64.ofNat d).toNat` spelling a per-element reset or cache write
uses (`process_slot`'s root caching, the slashings / RANDAO / builder-payment ring buffers),
so the period is written once and a `slotsPerEpoch`-versus-`slotsPerHistoricalRoot` mixup is
harder. Index-only: it feeds the same total `field[idx]!` write, so it cannot change which
slot is hit (no bounds-carrying `vmodSet`, which a proof could discharge differently). -/
@[inline] def umodIdx (x : UInt64) (d : Nat) : Nat := (x % UInt64.ofNat d).toNat

/-- A `Nat` cursor advanced modulo a length, with the length-zero case pinned to `0`. Names
the `if n == 0 then 0 else x % n` guard the withdrawal sweeps repeat when they wrap the
builder / validator cursor past the end of a (possibly empty) collection: an empty collection
has no slot to land on, so the cursor resets to `0` instead of evaluating `x % 0` (which
Lean's `Nat` `%` defines as `x`, leaking a non-wrapped index). With a non-empty collection it
is the ordinary `x % n`. Pure `Nat` index arithmetic, so it cannot change which slot a
downstream total write hits. -/
@[inline] def modWrap (x n : Nat) : Nat := if n == 0 then 0 else x % n

/-- Drop the first `k` elements of an `SSZList` (size only shrinks). -/
def sszDrop {α : Type} {cap : Nat} (xs : SSZList α cap) (k : Nat) : SSZList α cap :=
  ⟨xs.val.extract k xs.val.size, by have := xs.property; simp only [Array.size_extract]; omega⟩

/-- Replace an `SSZList`'s contents, clamping length at capacity. -/
def sszOfArray {α : Type} {cap : Nat} (a : Array α) : SSZList α cap :=
  if h : a.size ≤ cap then ⟨a, h⟩
  else ⟨a.extract 0 cap, by simp only [Array.size_extract]; omega⟩

/-- The indices of `xs` whose element (with its position) satisfies `p`, as `uint64`s. Names
the `mut out / for i / push (UInt64.ofNat i)` accumulator that the registry walks
(`get_active_validator_indices` and its eligible-set sibling) repeat, leaving only the
one-line predicate at the call site. The predicate takes the element and its index; the spec
walks only inspect the element, the index is offered for generality. Same iteration order
(`0 … xs.size-1`) and same push order as the longhand loop, so the resulting index array is
byte-for-byte the one the loop produced. -/
def indicesWhere {α : Type} [Inhabited α] (xs : Array α) (p : α → Nat → Bool) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := #[]
  for i in [0 : xs.size] do
    if p (xs[i]!) i then out := out.push (UInt64.ofNat i)
  return out

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

/-- Test participation-flag bit `idx` of a `uint8` flag byte. -/
@[inline] def hasFlag (flags : UInt8) (idx : Nat) : Bool :=
  (flags >>> (UInt8.ofNat idx)) &&& 1 == 1

/-- Set participation-flag bit `idx` of a `uint8` flag byte. -/
@[inline] def addFlag (flags : UInt8) (idx : Nat) : UInt8 :=
  flags ||| (1 <<< (UInt8.ofNat idx))

end EthCLLib.Spec
