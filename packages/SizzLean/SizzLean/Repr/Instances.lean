import SizzLean.Repr.Class

/-!
# `SizzLean.Repr.Instances`: library-provided `SSZRepr` instances

The leaf instances the `deriving SSZRepr` handler recurses on,
plus standalone instances for the basic primitive types users
typically wrap.

## Coverage

* `SSZRepr Bool`: shape `.bool`, identity iso. `BasicSupported`-
  compatible; verified `SSZ.roundtrip` available.
* `SSZRepr UInt8` / `UInt16` / `UInt32` / `UInt64`: shapes
  `.uintN 8` / `16` / `32` / `64`, identity iso. All four are
  `BasicSupported`-compatible; verified `SSZ.roundtrip` is
  available via the matching constructors
  (`.uintN8` / `.uintN16` / `.uintN32` / `.uintN64`).
* `SSZRepr (BitVec 128)` / `(BitVec 256)`: same shape, identity
  iso. Used for the 128/256-bit fields in consensus containers.
* Composites: `Vector α n`, `SSZ.List α n` (= `SSZList`),
  `Bitvector n`, `Bitlist n`, sigma-typed unions. Same
  iso-is-identity pattern: each picks a definitional `interp`
  match so `toRepr` / `fromRepr` reduce to the identity.

## Why iso-is-identity

For each primitive `T`, the underlying `SSZType` description chosen
in the instance (`.bool`, `.uintN k`) is defined so that
`(shape.interp = T)` *definitionally*. That makes `toRepr` and
`fromRepr` both the identity function in disguise, and both iso
laws (`to_from`, `from_to`) close by `rfl` because the kernel sees
`x = x` after `interp` reduction.

*Definitional equality* (often "defeq" in Lean prose) is the
equivalence the kernel can decide by pure reduction, beta
reduction, delta-unfolding of `@[reducible]` definitions, and
iota-reduction of pattern matches. It's what `rfl` proves; it's
also what Lean's type-equality check uses when it asks "does
this expression's type match the expected one?". Because
`interp .bool` *reduces* to `Bool` (not just *equals* it
propositionally), the literal `id` typechecks at both
`Bool → interp .bool` and `interp .bool → Bool` with no
coercion.
-/

set_option autoImplicit false

namespace SizzLean.Repr

open SizzLean.Spec

/-- `SSZRepr Bool`: wire format is a single byte (`0x00` for
`false`, anything else for `true` on the read side; `0x00`/`0x01`
on the write side). The iso is identity at the kernel level
because `interp .bool ≡ Bool`. -/
instance : SSZRepr Bool where
  shape    := .bool
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-- `SSZRepr UInt8`: wire format is a single byte (LE-trivial). -/
instance : SSZRepr UInt8 where
  shape    := .uintN 8
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-- `SSZRepr UInt16`: wire format is 2 little-endian bytes. -/
instance : SSZRepr UInt16 where
  shape    := .uintN 16
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-- `SSZRepr UInt32`: wire format is 4 little-endian bytes. -/
instance : SSZRepr UInt32 where
  shape    := .uintN 32
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-- `SSZRepr UInt64`: wire format is 8 little-endian bytes. Used
extensively in consensus types (`Slot`, `Epoch`, `ValidatorIndex`,
`Gwei` all wrap `UInt64`). -/
instance : SSZRepr UInt64 where
  shape    := .uintN 64
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-! ### Wider integer instances: `BitVec 128` and `BitVec 256`

`uint128` / `uint256` are spec types but have no native Lean
counterpart, they reduce to `BitVec n` at the `interp` level. The
two instances below pin those widths so consensus types
(`ExecutionPayload.base_fee_per_gas : uint256` in particular) can
declare fields of those types directly.

The `Vector α n` instance is polymorphic and identity-iso: because
`Vector α n = Vector (SSZType.interp (SSZRepr.shape (T := α))) n` is
definitional when `α` has identity-iso `SSZRepr` (which all the
built-in instances and any `abbrev`-based newtype wrapper satisfy),
`toRepr` and `fromRepr` are both `id`. A more general
element-wise-mapping iso would be needed if non-identity inner isos
appear in scope. -/

/-- `SSZRepr (BitVec 128)`: wire format is 16 little-endian bytes
(the SSZ `uint128` shape). -/
instance : SSZRepr (BitVec 128) where
  shape    := .uintN 128
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-- `SSZRepr (BitVec 256)`: wire format is 32 little-endian bytes
(SSZ `uint256`). Required for `ExecutionPayload.base_fee_per_gas`
from Bellatrix onward. -/
instance : SSZRepr (BitVec 256) where
  shape    := .uintN 256
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-- `SSZRepr (Vector α n)`: wire format is the concatenation of `n`
element encodings. Polymorphic over `[SSZRepr α]`; the iso maps
element-wise through the inner instance's iso. -/
instance instSSZReprVector {α : Type} {n : Nat} [r : SSZRepr α] :
    SSZRepr (Vector α n) where
  shape    := .vector r.shape n
  toRepr   := fun v => v.map r.toRepr
  fromRepr := fun w => w.map r.fromRepr
  to_from  := fun v => by
    show (v.map r.toRepr).map r.fromRepr = v
    rw [Vector.map_map]
    have h : r.fromRepr ∘ r.toRepr = id := funext r.to_from
    rw [h]
    exact Vector.map_id v
  from_to  := fun w => by
    show (w.map r.fromRepr).map r.toRepr = w
    rw [Vector.map_map]
    have h : r.toRepr ∘ r.fromRepr = id := funext r.from_to
    rw [h]
    exact Vector.map_id w

/-! ### Bitvector / Bitlist / SSZ.List user-facing aliases

The Lean *runtime* type of an SSZ `Bitlist[cap]` value is
`{ bs : Array Bool // bs.size ≤ cap }` (see `Spec/Interp.lean`).
That subtype is awkward to write at user struct fields; `abbrev`
gives it a friendly name without changing the underlying type, so
the SSZRepr instance is identity. Same shape for `SSZList`.

`Bitvector` differs: `interp (.bitvector n) = BitVec n`, but
`BitVec n` is *also* the interpretation of `uintN n` for `n > 64`.
To disambiguate we wrap it in a structure, the SSZRepr `shape` is
the disambiguator that picks the bit-packed wire layout. -/

/-- SSZ `Bitlist[cap]`: variable-length bit vector capped at `cap`. -/
abbrev Bitlist (cap : Nat) : Type := { bs : Array Bool // bs.size ≤ cap }

/-- SSZ `List[α, cap]`: variable-length list of `α` capped at `cap`. -/
abbrev SSZList (α : Type) (cap : Nat) : Type := { xs : Array α // xs.size ≤ cap }

/-- Element access on an `SSZList`. Defers to `Array.get!` on the
underlying buffer. -/
abbrev SSZList.get! {α : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (i : Nat) : α :=
  xs.val[i]!

/-- Runtime length of an `SSZList`. Surfaces the underlying
`Array.size` so callers don't have to project through `.val`. Used
by the `sszUpdate` macro's bounds-check emission. -/
abbrev SSZList.size {α : Type} {cap : Nat} (xs : SSZList α cap) : Nat :=
  xs.val.size

/-- Replace the i-th element of an `SSZList`. `Array.set!` (lowered
to `setIfInBounds`) preserves size, so the cap bound on the
underlying buffer carries through. -/
abbrev SSZList.set! {α : Type} {cap : Nat}
    (xs : SSZList α cap) (i : Nat) (v : α) : SSZList α cap :=
  ⟨xs.val.set! i v, by
    have h : (xs.val.set! i v).size = xs.val.size := by
      simp [Array.set!_eq_setIfInBounds]
    rw [h]; exact xs.property⟩

/-- Append `x`, clamping at the cap: a list at capacity is returned unchanged (a valid
consensus list never overflows, so the clamp branch is unreachable on well-formed input).
The cap-respecting append on the type itself, so a downstream `sszAppend` / `appendState`
needs no separate push helper. -/
def SSZList.push {α : Type} {cap : Nat} (xs : SSZList α cap) (x : α) : SSZList α cap :=
  if h : xs.val.size < cap then ⟨xs.val.push x, by rw [Array.size_push]; omega⟩ else xs

/-- `GetElem` instance for `SSZList`, with the faithful validity predicate
`fun xs i => i < xs.size`. So the three element reads behave like `Array`'s:
`xs[i]?` is a real bounds check (`none` past the end), `xs[i]!` returns the
element type's `default` past the end, and `xs[i]'h` reads with an in-bounds
proof. The everyday reads are `xs[i]!` (total) and `xs[i]?` (option).

The `sszUpdate` / `sszGet` macros never emit a bare `xs[i]`: writes go through
`SSZList.set!`, reads through `[i]!`, and bounds through `.size`. None of those
need a proof at the index, so the faithful predicate costs the macros nothing.
`xs[i]!` is also the same syntax `Vector` supports, so the macro needs no
type-aware dispatch. -/
instance {α : Type} [Inhabited α] {cap : Nat} :
    GetElem (SSZList α cap) Nat α (fun xs i => i < xs.size) where
  getElem xs i h := xs.val[i]'h

/-! ### Element-collection surface for `SSZList` / `Bitlist`

These let a caller work an `SSZList` (or `Bitlist`) without projecting through the
subtype's `.val`. They delegate to the underlying `Array`, so they reduce away cleanly.
Element reads use the `GetElem` forms above: `xs[i]!` (total, `default` past the end)
and `xs[i]?` (option, `none` past the end). -/

/-- The elements as an `Array`. -/
abbrev SSZList.toArray {α : Type} {cap : Nat} (xs : SSZList α cap) : Array α := xs.val
/-- The elements as a `List`. -/
abbrev SSZList.toList {α : Type} {cap : Nat} (xs : SSZList α cap) : List α := xs.val.toList
/-- Left fold over the elements. -/
abbrev SSZList.foldl {α β : Type} {cap : Nat} (f : β → α → β) (init : β) (xs : SSZList α cap) : β := xs.val.foldl f init
/-- Map the elements to an `Array`. -/
abbrev SSZList.map {α β : Type} {cap : Nat} (f : α → β) (xs : SSZList α cap) : Array β := xs.val.map f
/-- Map the elements, preserving the cap. The cap bound carries across because `Array.map`
does not change the underlying size (`Array.size_map`). The bare-`Array` companion
`SSZList.map` above drops the proof; reach for `mapCap` when the result must stay an
`SSZList` at the same cap, as at a fork boundary that copies a list field into its
element-converted twin. A `def`, not an `abbrev`, because it carries a proof (like
`SSZList.push`). -/
def SSZList.mapCap {α β : Type} {cap : Nat} (f : α → β) (xs : SSZList α cap) : SSZList β cap :=
  ⟨xs.val.map f, by rw [Array.size_map]; exact xs.property⟩
/-- Whether any element satisfies `p`. -/
abbrev SSZList.any {α : Type} {cap : Nat} (xs : SSZList α cap) (p : α → Bool) : Bool := xs.val.any p
/-- Whether every element satisfies `p`. -/
abbrev SSZList.all {α : Type} {cap : Nat} (xs : SSZList α cap) (p : α → Bool) : Bool := xs.val.all p
/-- First index whose element satisfies `p`. -/
abbrev SSZList.findIdx? {α : Type} {cap : Nat} (xs : SSZList α cap) (p : α → Bool) : Option Nat := xs.val.findIdx? p
/-- Membership test. -/
abbrev SSZList.contains {α : Type} {cap : Nat} [BEq α] (xs : SSZList α cap) (a : α) : Bool := xs.val.contains a
/-- `for x in xs` iterates the elements. -/
instance {m : Type → Type} [Monad m] {α : Type} {cap : Nat} : ForIn m (SSZList α cap) α where
  forIn xs b f := ForIn.forIn xs.val b f

/-- Runtime length of a `Bitlist`. -/
abbrev Bitlist.size {cap : Nat} (bs : Bitlist cap) : Nat := bs.val.size
/-- The bits as an `Array Bool`. -/
abbrev Bitlist.toArray {cap : Nat} (bs : Bitlist cap) : Array Bool := bs.val
/-- `GetElem` for `Bitlist`, faithful (validity `fun bs i => i < bs.size`): `bs[i]?`
is `none` past the end, `bs[i]!` is `false` past the end. Matches `SSZList`'s instance. -/
instance {cap : Nat} : GetElem (Bitlist cap) Nat Bool (fun bs i => i < bs.size) where
  getElem bs i h := bs.val[i]'h

/-! ### Default / ordering / hashing for the capped collection types

`SSZList` and `Bitlist` are `Subtype`s over `Array`, so Lean derives
nothing for them on its own. The instances below give the variable-length
SSZ collections the same `Inhabited` / `Ord` / `Hashable` surface the
fixed-length types (`Vector`, `Bitvector`) already carry, so a derived
container whose fields are all SSZ types picks these up for free (a
container used as a finite-map key needs `Ord` / `Hashable`; the runner's
genesis anchor needs `Inhabited`).

The empty collection is the canonical default, so the instance belongs with
the type, not in a downstream consumer. `Ord` is lexicographic over the
underlying array and `Hashable` folds the element hashes, both deferring to
`Array`'s own instances. `SSZList`'s element-aware variants require the
matching instance on `α`; `Bitlist`'s element is `Bool`, which has both. -/

/-- `Inhabited (SSZList α cap)`: the empty list, whose size `0` is below
any cap. -/
instance instInhabitedSSZList {α : Type} {cap : Nat} : Inhabited (SSZList α cap) :=
  ⟨⟨#[], Nat.zero_le _⟩⟩

/-- `Inhabited (Bitlist cap)`: the empty bit list. -/
instance instInhabitedBitlist {cap : Nat} : Inhabited (Bitlist cap) :=
  ⟨⟨#[], Nat.zero_le _⟩⟩

/-- `Ord (SSZList α cap)`: lexicographic over the underlying array. -/
instance instOrdSSZList {α : Type} {cap : Nat} [Ord α] : Ord (SSZList α cap) where
  compare a b := compare a.val b.val

/-- `Hashable (SSZList α cap)`: folds the element hashes of the array. -/
instance instHashableSSZList {α : Type} {cap : Nat} [Hashable α] : Hashable (SSZList α cap) where
  hash a := hash a.val

/-- `Ord (Bitlist cap)`: lexicographic over the underlying bit array. -/
instance instOrdBitlist {cap : Nat} : Ord (Bitlist cap) where
  compare a b := compare a.val b.val

/-- `Hashable (Bitlist cap)`: folds the bit hashes of the array. -/
instance instHashableBitlist {cap : Nat} : Hashable (Bitlist cap) where
  hash a := hash a.val

/-- SSZ `Bitvector[n]`: fixed-length bit vector. Distinct nominal
type from `BitVec n` so the SSZRepr resolves to the bit-packed
`.bitvector n` shape (not the LE-uint `.uintN n` shape that
`BitVec 128/256` resolve to). -/
-- `Inhabited` (all-zero), `Ord` (numeric, via `BitVec`'s own `Ord`), and
-- `Hashable` ride directly off the single `BitVec n` field, so a derived
-- container with a `Bitvector` field (e.g. `BeaconState.justificationBits`)
-- inherits all three. `Vector` already carries them from its components.
structure Bitvector (n : Nat) where
  data : BitVec n
  deriving DecidableEq, Inhabited, Ord, Hashable

instance instSSZReprBitlist {cap : Nat} : SSZRepr (Bitlist cap) where
  shape    := .bitlist cap
  toRepr   := id
  fromRepr := id
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

instance instSSZReprBitvector {n : Nat} : SSZRepr (Bitvector n) where
  shape    := .bitvector n
  toRepr   := Bitvector.data
  fromRepr := Bitvector.mk
  to_from  := fun _ => rfl
  from_to  := fun ⟨_⟩ => rfl

/-- `SSZRepr (SSZList α cap)`: list of `α` elements. Element-wise
iso through the inner `SSZRepr α`, just like `Vector α n`. -/
instance instSSZReprSSZList {α : Type} {cap : Nat} [r : SSZRepr α] :
    SSZRepr (SSZList α cap) where
  shape    := .list r.shape cap
  toRepr   := fun v =>
    ⟨v.val.map r.toRepr, by rw [Array.size_map]; exact v.property⟩
  fromRepr := fun w =>
    ⟨w.val.map r.fromRepr, by rw [Array.size_map]; exact w.property⟩
  to_from  := fun v => by
    apply Subtype.ext
    show (v.val.map r.toRepr).map r.fromRepr = v.val
    rw [Array.map_map]
    have h : r.fromRepr ∘ r.toRepr = id := funext r.to_from
    rw [h, Array.map_id]
  from_to  := fun w => by
    apply Subtype.ext
    show (w.val.map r.fromRepr).map r.toRepr = w.val
    rw [Array.map_map]
    have h : r.toRepr ∘ r.fromRepr = id := funext r.from_to
    rw [h, Array.map_id]

/-- A fixed-length byte vector coerces to its underlying `ByteArray`. The conversion is
representation-only (`⟨v.toArray⟩` is exactly the bytes the vector holds), so it is a
canonical coercion rather than an explicit call: a `Root` / pubkey / signature (each a
`Vector UInt8 n`) is usable wherever an SSZ or crypto seam wants raw wire bytes, with no
conversion written at the call site. The reverse direction stays an explicit function (it
must choose a length and truncate or zero-pad), so it is deliberately not a coercion. -/
instance instCoeVectorByteArray {n : Nat} : CoeOut (Vector UInt8 n) ByteArray where
  coe v := ⟨v.toArray⟩

end SizzLean.Repr
