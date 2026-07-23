import Std.Data.TreeMap
import Std.Data.HashMap
import SizzLean
import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Spec.FiniteMap`: the fork-choice map backing, higher-kinded

The fork-choice `Store` holds finite maps over several key types
(`Root` / `Checkpoint` / `ValidatorIndex`), and the framework abstracts the *map
backing* as a single higher-kinded family so the store's laws are provable on a
deterministic backing while the runner uses a fast one
(`FRAMEWORK_ARCHITECTURE.md` §9).

`MapKind` is the kind a `map` variable ranges over: a function from a key type
(carrying the structure a stock map needs) and a value type to a concrete map.
Its kind bakes the **union** `[Ord K] [BEq K] [Hashable K]`, so one shape backs
both `treeMap` (ordered, `Ord`, proof-friendly, deterministic key order) and
`hashMap` (`BEq` + `Hashable`, `O(1)`, the runner's). `Store` is parameterized by
`map` alone, so `Store treeMap` and `Store hashMap` are distinct types that
coexist with no ambient current map.
-/

set_option autoImplicit false

open SizzLean.Repr

namespace EthCLLib.Spec

/-- Hash a fixed-length vector by its array, so a `Vector`-keyed map (`Root =
Vector UInt8 32`, …) can use `hashMap`. -/
instance instHashableVector {α : Type} {n : Nat} [Hashable α] : Hashable (Vector α n) :=
  ⟨fun v => hash v.toArray⟩

/-- The kind of a finite-map *family*: `key type → value type → concrete map`,
given the key carries the union of structure both stock maps need. -/
abbrev MapKind := (K : Type) → [Ord K] → [BEq K] → [Hashable K] → Type → Type

/-- The operation contract a fork-choice map provides. One instance serves every
key type at once (`map Root V`, `map Checkpoint V`, …). `lookup` is partial; a
miss is the `missingKey` reject of the error model. `fold` / `keys` back the
all-keys walks (`getHead`, the filtered block tree). -/
class FcMap (map : MapKind) where
  /-- The empty map. -/
  empty    : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V
  /-- Insert (or overwrite) a key. -/
  insert   : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → K → V → map K V
  /-- Lookup; `none` on a miss (the `missingKey` reject). -/
  lookup   : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → K → Option V
  /-- Membership test. -/
  contains : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → K → Bool
  /-- Left fold over the entries. -/
  fold     : {K V β : Type} → [Ord K] → [BEq K] → [Hashable K] → (β → K → V → β) → β → map K V → β
  /-- The keys, as a list. -/
  keys     : {K V : Type} → [Ord K] → [BEq K] → [Hashable K] → map K V → List K

/-- Lookup with a default, what the store accessors want. -/
def FcMap.lookupD {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    [Inhabited V] (m : map K V) (k : K) : V := (FcMap.lookup m k).getD default

/-- The map's values (the all-values walk the fork choice needs, e.g. scanning every stored
block for a proposer equivocation). -/
def FcMap.values {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    (m : map K V) : List V := (FcMap.keys m).filterMap (FcMap.lookup m ·)

/-- The keys whose entry satisfies `p` (the "children of a block" walk: the keys whose
stored value's `parentRoot` matches). `p` sees the key and the value. -/
def FcMap.filterKeys {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    (m : map K V) (p : K → V → Bool) : List K :=
  (FcMap.keys m).filter (fun k => match FcMap.lookup m k with | some v => p k v | none => false)

/-- `Std.TreeMap` family: ordered, deterministic key order, the proof-friendly
default (uses `[Ord K]`). -/
@[reducible] def treeMap : MapKind := fun K _ _ _ V => Std.TreeMap K V

/-- `Std.HashMap` family: `O(1)`, the runner's choice (uses `[BEq K] [Hashable K]`). -/
@[reducible] def hashMap : MapKind := fun K _ _ _ V => Std.HashMap K V

instance : FcMap treeMap where
  empty := ∅
  insert m k v := m.insert k v
  lookup m k := m.get? k
  contains m k := m.contains k
  fold f init m := m.foldl f init
  keys m := m.keys

instance : FcMap hashMap where
  empty := ∅
  insert m k v := m.insert k v
  lookup m k := m.get? k
  contains m k := m.contains k
  fold f init m := m.fold f init
  keys m := m.keys

/-- Look up `k` in a fork-choice map, or throw the store machine's `missingKey errKey`
reject (the `missingKey` branch of the error model). A handler binds it with `←` in place of
the `let some v := FcMap.lookup m k | throw (.missingKey …)` destructure, which repeats the
key. The error key is explicit because a `Checkpoint`-keyed lookup reports the checkpoint's
`root`, not the checkpoint itself. -/
def FcMap.getOrThrowKey {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    {m : Type → Type} [Monad m] [MonadExceptOf StoreTransitionError m]
    (mp : map K V) (k : K) (errKey : Vector UInt8 32) : m V :=
  match FcMap.lookup mp k with
  | some v => pure v
  | none   => throw (StoreTransitionError.missingKey errKey)

/-- `getOrThrowKey` for a `Root`-keyed map: a miss reports the lookup key itself. The
`Vector UInt8 32` instances are taken as binders so this resolves wherever a `Root`-keyed
store map is read (the `Ord` instance lives with the spec's fork-choice store). -/
@[inline] def FcMap.getOrThrow {map : MapKind} [FcMap map] {V : Type}
    [Ord (Vector UInt8 32)] [BEq (Vector UInt8 32)] [Hashable (Vector UInt8 32)]
    {m : Type → Type} [Monad m] [MonadExceptOf StoreTransitionError m]
    (mp : map (Vector UInt8 32) V) (k : Vector UInt8 32) : m V :=
  FcMap.getOrThrowKey mp k k

/-- Look up `k`, or throw the spec's `assert` reject. The fused form of the pyspec pair
`assert k in d` followed by `d[k]`: the membership assert is the spec's own opening line, so
a miss is an *expected rejection* (`.assert`), where `getOrThrow`'s bare-`d[k]` miss is
`missingKey` (a bug-smell). Post-assert the key is present, so binding the value at the
assert site is observably identical to the spec's later read. `descr` renders the asserted
condition, diagnostic only. -/
def FcMap.getOrAssert {map : MapKind} [FcMap map] {K V : Type} [Ord K] [BEq K] [Hashable K]
    {m : Type → Type} [Monad m] [MonadExceptOf StoreTransitionError m]
    (mp : map K V) (k : K) (descr : String) : m V :=
  match FcMap.lookup mp k with
  | some v => pure v
  | none   => throw (StoreTransitionError.assert descr)

end EthCLLib.Spec
