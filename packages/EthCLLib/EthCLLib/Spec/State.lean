import SizzLean
import EthCLLib.Spec.Errors
import EthCLLib.Spec.Hasher

/-!
# `EthCLLib.Spec.State`: the boxed-state access surface

`State` is the fork's `BeaconState` as an SSZ box; the per-fork abbrev (and the
`modifyState` updater) are emitted by `state_preamble` (`EthCLLib.Spec.Header`).
Reads and writes are SizzLean's generic `sszGet` / `sszUpdate` macros, available as
global syntax the moment `SizzLean` is imported, so the framework adds no per-field
lenses. This module supplies the small generic helpers the step primitives need:
`getStateRoot` / `stateRoot` / `stateRoot!`, and the index-error lift
(`FRAMEWORK_ARCHITECTURE.md` §8.1).
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
`stateRoot!` below is the terminal-only escape hatch. Whether retention actually caches
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

/-- Run a state-machine action on a boxed state and project the result to the post-state
root, or the reject. The `EStateM`-side twin of `runOn` (`PySpecTests.Interface`, which does
the same for a fork-choice store): a `PySpecTests` entry point decodes a pre-state, builds
its `EStateM StateTransitionError` action, and ends with `runToRoot box0 action`, replacing
the open-coded `match action.run box0 with | .ok _ post => .ok (stateRoot! post) | .error e _
=> .error e`. The box dies right after, so `stateRoot!` (the cache-dropping form) is correct
here. -/
@[inline] def runToRoot {H T : Type} [Hasher H] [SSZRepr T]
    (box0 : SSZ.Box H T) (act : EStateM StateTransitionError (SSZ.Box H T) Unit) :
    Except StateTransitionError ByteArray :=
  match act.run box0 with
  | .ok _ post => .ok (stateRoot! post)
  | .error e _ => .error e

/-- Run a best-effort state-machine action and keep the input state on failure. The
keep-input-on-error twin of `runToRoot`: a fork-choice helper (`store_target_checkpoint_state`'s
slot advance) runs a nested `EStateM StateTransitionError` action whose failure should leave the
surrounding store unchanged, so it discards the reject and returns the pre-state `s` rather than
threading it out. Generic over the state `S` (the per-fork `State` is concrete only inside a fork
section), with the error pinned to `StateTransitionError`: that argument type is what forces a
polymorphic action passed in (e.g. `processSlots target`) to resolve its monad to
`EStateM StateTransitionError S`, replacing the open-coded `match act.run s with | .ok _ s' => s'
| .error _ _ => s` and the metavariable-pinning annotation it needed. -/
@[inline] def runBestEffort {S : Type} (act : EStateM StateTransitionError S Unit) (s : S) : S :=
  match act.run s with
  | .ok _ s'   => s'
  | .error _ _ => s

-- Re-export `IndexError` onto the spec surface, so a pure query reading `validators[i]` can
-- be typed `Except IndexError α` under the single `open EthCLLib.Spec`.
export SizzLean.Cache (IndexError)

/-- A SizzLean index miss becomes the state machine's `outOfBounds`. -/
instance : ErrorConv IndexError StateTransitionError where
  conv := fun | .indexError i b => .outOfBounds i b
/-- … and the fork-choice machine's wrapped index reject (classified the same). -/
instance : ErrorConv IndexError StoreTransitionError where
  conv := fun | .indexError i b => .transition (.outOfBounds i b)

/-- Monadic element access on an `SSZList`: element `i`, or the typed reject
`outOfBounds i size` (the bug-smell for a framework-invariant index that should never be
out of range on well-formed input). The monadic-context safe read that replaces `…
.val[i]!` (`SPEC_AUTHORING_MODEL.md` §7); it builds the `Except IndexError` carrying the
real index and bound and hands it to `liftErr`, whose `[ErrorConv IndexError E]` instance
maps the miss to the context's reject. Generic over the error type, so it reads in both the
state machine (`E = StateTransitionError`, a direct `outOfBounds`) and the fork-choice
machine (`E = StoreTransitionError`, the wrapped `transition (outOfBounds …)`). A spec
*validation* of an index pairs this with a preceding `assert (i < size)`: the `assert`
rejects a bad index first as the spec's `IndexError` (`assert`, an `expectedRejection`), so
`sszGetIdx`'s own `outOfBounds` stays unreachable, the safe read behind the validation and a
defense-in-depth signal if the assert is ever wrong. -/
@[inline] def sszGetIdx {α : Type} {m : Type → Type u} {E : Type} [Monad m] {cap : Nat}
    [MonadExcept E m] [ErrorConv IndexError E] (xs : SizzLean.Repr.SSZList α cap) (i : Nat) : m α :=
  liftErr <| match xs.val[i]? with
    | some a => .ok a
    | none   => .error (IndexError.indexError i xs.val.size)

/-- `sszGetIdx` for a `Bitlist` bit: bit `i`, or the typed reject `outOfBounds i size`. The
monadic safe read for an *untrusted* bit index, an attestation's `aggregation_bits` read
indexed by a block-supplied committee offset, where `[i]!`'s `false` default would mask an
over-length read. Same shape as `sszGetIdx`, on `Bitlist`'s faithful `[i]?`. -/
@[inline] def bitlistGetIdx {m : Type → Type u} {E : Type} [Monad m] {cap : Nat}
    [MonadExcept E m] [ErrorConv IndexError E] (bs : SizzLean.Repr.Bitlist cap) (i : Nat) : m Bool :=
  liftErr <| match bs.val[i]? with
    | some b => .ok b
    | none   => .error (IndexError.indexError i bs.val.size)

end EthCLLib.Spec
