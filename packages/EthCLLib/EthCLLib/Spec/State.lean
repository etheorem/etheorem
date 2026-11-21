import SizzLean
import EthCLLib.Spec.Errors
import EthCLLib.Spec.CLInt
import EthCLLib.Spec.Hasher

/-!
# `EthCLLib.Spec.State`: the boxed-state access surface

`State` is the fork's `BeaconState` as an SSZ box; the per-fork abbrev (and the
`modifyState` updater) are emitted by `state_preamble` (`EthCLLib.Spec.Header`).
Reads and writes are SizzLean's generic `sszGet` / `sszUpdate` macros, available as
global syntax the moment `SizzLean` is imported, so the framework adds no per-field
lenses. This module supplies the small generic helpers the step primitives need:
`getStateRoot` / `stateRoot` / `stateRoot!`, the index-error lift
(`FRAMEWORK_ARCHITECTURE.md` §8.1), and the size-aware indexing layer
(`SPEC_ARITHMETIC.md` §4.6): the `ToIndex` class with the pure raising read
`getAt` and write `setAt`, beside the machine read `sszGetIdx` they extend.
-/

set_option autoImplicit false

open SizzLean
open SizzLean.Cache

namespace EthCLLib.Spec

universe u

/-! `Inhabited` for the SSZ collection types (`SSZList` / `Bitlist` empty, `Bitvector`
all-zero) lives in SizzLean alongside the type definitions, so a `forkcontainer`
derives `Inhabited` for the runner's genesis anchor with no framework-side instance. -/

/-- A boxed state that yields its Merkle root together with a cache-warmed successor
box (`Box.hashTreeRoot`). The single instance is for `SSZ.Box`. The class exists so
`getStateRoot` pins the state type `S` from its `MonadState S m` constraint (where the
state type is an `outParam`) as one metavariable, then recovers the box structure,
rather than leaving the box's `H` / `T` as metavariables instance search cannot solve in
the abstract `state_section`. -/
class StateRoot (S : Type) where
  /-- The root and the cache-warmed box, from `Box.hashTreeRoot`. -/
  rootAndWarm : S → ByteArray × S

@[reducible] instance instStateRootBox {H T : Type} [Hasher H] [SSZRepr T] :
    StateRoot (SSZ.Box H T) where
  rootAndWarm s := s.hashTreeRoot

/-- Take the threaded state's Merkle root inside a step, keeping the cache-warmed box.
`Box.hashTreeRoot` is `modifyGet`-shaped: it returns the root *and* a box holding the
committed intermediate-node hashes, so this writes that box back through
`MonadStateOf`, and a later root reuses the tree instead of rebuilding it. This is the
way to take a state root in a `StateTransition` / store-machine step; the pure
`stateRoot!` below is the terminal-only discard form. Whether retention actually caches
is the box flavour's call (a cached box keeps the tree, a pure box does not), so the
spec calls this unconditionally and the runner picks the flavour and manages memory. -/
@[inline] def getStateRoot {S : Type} {m : Type → Type u} [MonadState S m] [StateRoot S] :
    m ByteArray :=
  modifyGet StateRoot.rootAndWarm

/-- The Merkle root of a boxed state value in hand, **with** the cache-warmed box
`Box.hashTreeRoot` returns, for a non-monadic context that threads the box by hand: a
pure `State → State` transformer like `processSlot`, or an `Except` handler that returns
the warm box. This is the lossless pure form, so it carries no bang. `getStateRoot` is
the monadic form that threads the box automatically; `stateRoot!` is the form that drops
it. Keeping spec bodies on this surface avoids naming `Box.hashTreeRoot` directly. -/
@[inline] def stateRoot {H T : Type} [Hasher H] [SSZRepr T] (state : SSZ.Box H T) :
    ByteArray × SSZ.Box H T :=
  state.hashTreeRoot

/-- The Merkle root of a boxed state value in hand, **discarding** the cache-warmed box
`Box.hashTreeRoot` returns. The `!` marks the discard, this library's bang convention for
the convenient-but-lossy variant (as in `Array.get!` / `sszUpdate field[i]!`): it never
panics, it drops the warm tree. Correctness is unaffected, the cached and uncached roots
are equal by SizzLean's coherence invariant, only the caching speedup is lost. Use it
only at a terminal site, where the box dies right after the root is taken (the
`PySpecTests` interface impls, where the root is the return value). A step on the threaded
state uses `getStateRoot`; a non-monadic context that still needs the warm box uses the
lossless `stateRoot`. -/
@[inline] def stateRoot! {H T : Type} [Hasher H] [SSZRepr T] (state : SSZ.Box H T) :
    ByteArray :=
  (state.hashTreeRoot).1

-- Re-export `IndexError` onto the spec surface, so a pure query reading `validators[i]` can
-- be typed `Except IndexError α` under the single `open EthCLLib.Spec`.
export SizzLean.Cache (IndexError)

/-- A SizzLean index miss becomes the state machine's `outOfBounds`. -/
instance : ErrorConv IndexError StateTransitionError where
  conv := fun | .indexError i b => .outOfBounds i b
/-- … and the fork-choice machine's wrapped index reject (classified the same). -/
instance : ErrorConv IndexError StoreTransitionError where
  conv := fun | .indexError i b => .transition (.outOfBounds i b)

/-- A random-access collection `sszGetIdx` can read: the length, and `get?`.
`SSZList` and `ProgressiveList` both carry it, so a fork that switches a field
from a capped list to a progressive list keeps the same read spelling. -/
class IdxRead (ρ : Type) (α : outParam Type) where
  size : ρ → Nat
  get? : ρ → Nat → Option α

@[reducible] instance {α : Type} {cap : Nat} : IdxRead (SizzLean.Repr.SSZList α cap) α where
  size xs := xs.val.size
  get? xs i := xs.val[i]?

@[reducible] instance {α : Type} : IdxRead (SizzLean.Repr.ProgressiveList α) α where
  size xs := xs.val.size
  get? xs i := xs.val[i]?

@[reducible] instance {cap : Nat} : IdxRead (SizzLean.Repr.Bitlist cap) Bool where
  size bs := bs.val.size
  get? bs i := bs.val[i]?

@[reducible] instance : IdxRead SizzLean.Repr.ProgressiveBitlist Bool where
  size bs := bs.val.size
  get? bs i := bs.val[i]?

/-- A plain `Array` is a random-access collection: the length, and `get?`.
The fork-choice store holds plain arrays (`block_timeliness`'s
`list[boolean]`, `gloas/fork-choice.md:554,1022`), and a pure query over one
uses `getAt` below. -/
@[reducible] instance {α : Type} : IdxRead (Array α) α where
  size xs := xs.size
  get? xs i := xs[i]?

/-- A fixed-size `Vector`: the length is the type index. -/
@[reducible] instance {α : Type} {n : Nat} : IdxRead (Vector α n) α where
  size _ := n
  get? v i := if h : i < n then some v[i] else none

/-- `len(xs)` on any random-access collection: an SSZ list, a vector, a bit list, or a
plain array. The result is the pyspec's plain `int` (`SPEC_ARITHMETIC.md` §4.5), a
`CLInt`, so `x % len xs` takes the plain kind's raising `%` on an empty collection, and
`i % len xs` with a checked `i` takes the mixed route. `CLInt.len` is the same length
for a plain `Array`. -/
@[inline] def len {ρ α : Type} [IdxRead ρ α] (xs : ρ) : CLInt := ⟨IdxRead.size xs⟩

/-! ## Size-aware indices (`SPEC_ARITHMETIC.md` §4.6)

The pyspec indexes a list with any integer kind, and a plain negative `int`
counts from the end (`SPEC_ARITHMETIC.md` §3.7). `ToIndex` says how an integer
type names a position in a collection of a known size; `pos?` returns `none`
exactly where the pyspec raises `IndexError`. The class sits here, beside the
reads and writes that consume it (§5.7): the indexing surface belongs to the
spec, and `SizzLean` keeps `Nat` indices and never sees it.

Every helper on this class keeps the index fault `IndexError`-shaped: the
reject is an `IndexError`, mapped to `outOfBounds` through the `ErrorConv
IndexError E` instances, never folded into the arithmetic fault. -/

/-- How an integer type names a position in a collection of `size` elements:
`none` exactly where the pyspec raises `IndexError`. A negative plain `int`
counts from the end, as Python does.

`idx?` is the diagnostic read-back: the rejected index as the error payload's
own `Nat` field carries it, so a reject reports the index the caller wrote. It
is the written value where that value fits a `Nat` (`Nat`, `CLUint64`, and a
nonnegative `CLInt`) and the `0` placeholder where it does not (a negative
`CLInt`, whose signed value has no `Nat` representation; `IndexError`'s payload
field is a `Nat`, so the sign cannot be carried in it). The payload is diagnostic
only, and nothing branches on it. -/
class ToIndex (ι : Type) where
  /-- The position to read, or `none` where the index raises. -/
  pos? : ι → Nat → Option Nat
  /-- The rejected index, carried for the kinds whose value fits the payload's
  `Nat` field; the `0` placeholder for a negative `CLInt`. -/
  idx? : ι → Nat

/-- In range, a `Nat` index is the position itself. -/
instance : ToIndex Nat := ⟨fun i size => if i < size then some i else none, fun i => i⟩

/-- The checked value's plain integer is the position. `CLUint64` is
nonnegative, so the only raise is the positive out-of-range case. This is the
allowed executable use of the underlying-value conversion
(`SPEC_ARITHMETIC.md` §4.5): indexing goes through this interface, the value
stays the index, and no operator is resolved through it. -/
instance : ToIndex CLUint64 :=
  ⟨fun i size => if i.toPlainNat < size then some i.toPlainNat else none,
    fun i => i.toPlainNat⟩

/-- A negative plain `int` counts from the end, as Python does: `-1` names the
last element and `-size` the first. A positive out-of-range index and a
negative one below `-size` both map to `none`, the one `IndexError` shape
(`SPEC_ARITHMETIC.md` §3.7). No sign is discarded on the way: the signed value
drives the end-relative count, never an `Int.toNat` default. -/
instance : ToIndex CLInt := ⟨fun i size =>
  if 0 ≤ i.val then
    if i.val.toNat < size then some i.val.toNat else none
  else
    if i.val.natAbs ≤ size then some (size - i.val.natAbs) else none,
  fun i => if 0 ≤ i.val then i.val.toNat else 0⟩

/-- The pure raising read (`SPEC_ARITHMETIC.md` §4.6): the element at the
position `i` names, or `Except IndexError` where the pyspec raises. The fault
stays `IndexError`-shaped, so a monadic caller lifts it with `liftErr` and the
`ErrorConv IndexError E` instance maps it to `outOfBounds`; it never becomes an
arithmetic fault. A state-free helper that only reads returns this; one that
also does arithmetic returns `Except StateTransitionError`, binding both the
read (`liftErr (getAt …)`) and the operators (`SPEC_ARITHMETIC.md` §4.6). The
machine-context read on an SSZ collection stays `sszGetIdx` below. A rejected
index carries the value the caller wrote in the reject's diagnostic index
field, through `ToIndex.idx?`; a negative `CLInt` keeps the `0` placeholder,
the one case its signed value has no `Nat` payload for. The payload is
diagnostic only and nothing branches on it. -/
@[inline] def getAt {α ρ ι : Type} [IdxRead ρ α] [ToIndex ι] (xs : ρ) (i : ι) :
    Except IndexError α :=
  match ToIndex.pos? i (IdxRead.size xs) with
  | some k => match IdxRead.get? xs k with
    | some a => .ok a
    | none   => .error (IndexError.indexError k (IdxRead.size xs))
  | none   => .error (IndexError.indexError (ToIndex.idx? i) (IdxRead.size xs))

/-- A random-access collection `setAt` / the machine write can update: the
read half plus a checked element write that leaves the collection alone past
the end. The write helpers below take this class, so an array, an SSZ list, a
vector, and the bit collections share one spelling. -/
class IdxWrite (ρ : Type) (α : outParam Type) extends IdxRead ρ α where
  /-- The collection with element `k` replaced, or `none` past the end. -/
  set? : ρ → Nat → α → Option ρ

/-- A plain `Array` write: the element replaced in bounds, `none` past the
end. -/
@[reducible] instance {α : Type} : IdxWrite (Array α) α where
  set? xs k v := if h : k < xs.size then some (xs.set k v h) else none

/-- An SSZ list write: the cap bound survives, `Array.size_set` preserves the
length. -/
@[reducible] instance {α : Type} {cap : Nat} : IdxWrite (SizzLean.Repr.SSZList α cap) α where
  set? xs k v :=
    if h : k < xs.val.size then
      some ⟨xs.val.set k v h, by rw [Array.size_set]; exact xs.property⟩
    else none

/-- A progressive list write: the one-field wrapper keeps its length. -/
@[reducible] instance {α : Type} : IdxWrite (SizzLean.Repr.ProgressiveList α) α where
  set? xs k v :=
    if h : k < xs.val.size then
      some ⟨xs.val.set k v h⟩
    else none

/-- A fixed-size `Vector` write: the length is the type index, so the bound
is the type's own. -/
@[reducible] instance {α : Type} {n : Nat} : IdxWrite (Vector α n) α where
  set? v k x := if h : k < n then some (v.set k x h) else none

/-- A bit list write: the cap bound survives the single-bit replacement. -/
@[reducible] instance {cap : Nat} : IdxWrite (SizzLean.Repr.Bitlist cap) Bool where
  set? bs k v :=
    if h : k < bs.val.size then
      some ⟨bs.val.set k v h, by rw [Array.size_set]; exact bs.property⟩
    else none

/-- A progressive bit list write: the wrapper keeps its length. -/
@[reducible] instance : IdxWrite SizzLean.Repr.ProgressiveBitlist Bool where
  set? bs k v :=
    if h : k < bs.val.size then
      some ⟨bs.val.set k v h⟩
    else none

/-- The pure checked write (`SPEC_ARITHMETIC.md` §4.6, §4.5): the collection
with the element at `i` replaced, or `Except IndexError` where the write's
index is out of range. The written value's own range check is the arithmetic
fault and happens one step earlier, at the checked conversion that builds the
value (`let v ← CLUint64.ofNat? raw`, then `setAt xs i v`), so the two failure
classes stay distinct and each keeps its own classification. -/
@[inline] def setAt {α ρ ι : Type} [IdxRead ρ α] [IdxWrite ρ α] [ToIndex ι] (xs : ρ) (i : ι)
    (v : α) : Except IndexError ρ :=
  match ToIndex.pos? i (IdxRead.size xs) with
  | some k => match IdxWrite.set? xs k v with
    | some xs' => .ok xs'
    | none     => .error (IndexError.indexError k (IdxRead.size xs))
  | none   => .error (IndexError.indexError (ToIndex.idx? i) (IdxRead.size xs))

/-- Monadic element access: element `i`, or the typed reject `outOfBounds i size`
(the bug-smell for a framework-invariant index that should never be out of range on
well-formed input). The monadic-context safe read that replaces `….val[i]!`
(`SPEC_AUTHORING_MODEL.md` §7); it builds the `Except IndexError` carrying the real
index and bound and hands it to `liftErr`, whose `[ErrorConv IndexError E]` instance
maps the miss to the context's reject. Generic over the error type, so it reads in both
the state machine (`E = StateTransitionError`, a direct `outOfBounds`) and the
fork-choice machine (`E = StoreTransitionError`, the wrapped `transition (outOfBounds …)`).
A spec *validation* of an index pairs this with a preceding `assert (i < size)`: the
`assert` rejects a bad index first, as the spec's own `assert` does (an `AssertionError`,
classified `expectedRejection`), so `sszGetIdx`'s own `outOfBounds` stays unreachable, the safe
read behind the validation and a defense-in-depth signal if the assert is ever wrong.
The collection is any `IdxRead`: a capped `SSZList` or an uncapped `ProgressiveList`.
The index is any `ToIndex` kind (`SPEC_ARITHMETIC.md` §4.6): a `Nat` position, a
`CLUint64` such as a `ValidatorIndex`, or a `CLInt`. The read is `getAt` lifted into the
ambient monad, so each kind rejects exactly where the pyspec raises `IndexError`. -/
@[inline] def sszGetIdx {α ρ ι : Type} {m : Type → Type u} {E : Type} [Monad m] [IdxRead ρ α]
    [ToIndex ι] [MonadExcept E m] [ErrorConv IndexError E] (xs : ρ) (i : ι) : m α :=
  liftErr (getAt xs i)

/-- `sszGetIdx` for a bit list: bit `i`, or the typed reject `outOfBounds i size`. The
monadic safe read for an *untrusted* bit index, an attestation's `aggregation_bits` read
indexed by a block-supplied committee offset, where `[i]!`'s `false` default would mask an
over-length read. Same shape as `sszGetIdx`, on a `Bitlist` or a `ProgressiveBitlist`. -/
@[inline] def bitlistGetIdx {ρ : Type} {m : Type → Type u} {E : Type} [Monad m] [IdxRead ρ Bool]
    [MonadExcept E m] [ErrorConv IndexError E] (bs : ρ) (i : Nat) : m Bool :=
  sszGetIdx bs i

/-- `sszGetIdx` for a plain `Array`: element `i`, or the typed reject `outOfBounds i size`. The
monadic safe read for a spec `list[i]` over a non-SSZ `Array`, e.g. a fork-choice `Store` value
such as `block_timeliness`'s `list[boolean]` (`gloas/fork-choice.md:554,1022`), where `[i]!` /
`?.getD` would mask an over-length read as a silent default. Same shape as `sszGetIdx`, on the
`Array`'s own `[i]?`. -/
@[inline] def arrGetIdx {α : Type} {m : Type → Type u} {E : Type} [Monad m]
    [MonadExcept E m] [ErrorConv IndexError E] (xs : Array α) (i : Nat) : m α :=
  liftErr <| match xs[i]? with
    | some a => .ok a
    | none   => .error (IndexError.indexError i xs.size)

end EthCLLib.Spec
