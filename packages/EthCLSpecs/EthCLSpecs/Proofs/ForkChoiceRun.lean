import EthCLSpecs.Gloas.ForkChoice
import EthCLSpecs.Proofs.Run

/-!
# `EthCLSpecs.Proofs.ForkChoiceRun`: the fork-choice store monad these proofs would run at

`Proofs/Run.lean` names the monad for the *state* machine. This names the one for the
*store* machine, and shows a fork-choice `forkdef` discharged at it.

Nothing here is a fork-choice proof yet; `CONSENSUS_PROOF_CANDIDATES.md` queues seven.
The point is that the door is open. Until the bridge in `EthCLLib/Spec/Assert.lean`
took its nested action generically, a store handler dropped into `EStateM` whatever
monad it was itself running in, so a fork-choice proof would have carried the fast
state machine inside it no matter which store monad it pinned. The theorem below is
the evidence that it no longer does: a real fork-choice `forkdef`, at a store monad
with no `EStateM` anywhere in it.

`getSlotsSinceGenesis` is the subject because it is small and it throws. Its two
checked `uint64` ops are the reason the fork-choice read layer is monadic at all, so
proving its equation at the pure monad exercises the part that made the monad matter,
without dragging in a walk or a nested state transition.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag StoreTransitionError MapKind FcMap)
open EthCLSpecs.Fulu (Preset Config)
open EthCLSpecs.Gloas (Store getSlotsSinceGenesis getCurrentSlot)

/-- The store machine's pure monad: `StateT` over `Except`, threading the fork-choice
`Store` and rejecting with `StoreTransitionError`. The store-side counterpart of
`GloasRun`, and the store-side reading of `SPECS_ARCHITECTURE.md` §11.1.

Parameterized by the map backing rather than fixed to `treeMap`: the backing is a
separate axis of the fast/pure duality from the monad, and a theorem that does not
read a map should not pin one. -/
abbrev GloasStoreRun [Preset] [HasherTag] (map : MapKind) : Type → Type :=
  StateT (Store map) (Except StoreTransitionError)

/-- **A fork-choice `forkdef`, at the pure store monad.** `get_slots_since_genesis` on a
store whose clock has not advanced past genesis returns `0`, leaving the store alone.

The two `uint64` ops both stay in range for the trivial reason: `time - genesis_time` is
`0` when they are equal, so the checked subtraction cannot underflow and the checked
multiply has nothing to overflow. Closing by `rfl` after the hypothesis is substituted
shows the whole `do` block reduces at this monad, binds and checked ops included. -/
theorem getSlotsSinceGenesis_run_of_time_eq_genesis
    [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.time = store.genesisTime →
      (getSlotsSinceGenesis (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime
  -- `checkedSub g g` takes its `else` branch (`g > g` is false) and yields `g - g = 0`;
  -- `checkedMul 0 1000` takes its `else` branch (the `a != 0` guard) and yields `0`;
  -- `0 / SLOT_DURATION_MS` is `0` for the opaque `[Config]` divisor.
  simp [getSlotsSinceGenesis, htime, EthCLLib.Spec.checkedSub, EthCLLib.Spec.checkedMul]
  rfl

/-- The same fact one layer up, through `get_current_slot`'s `GENESIS_SLOT + _`. Two
`forkdef`s composed, so the bind between them is at this monad too, not just the leaf. -/
theorem getCurrentSlot_run_of_time_eq_genesis
    [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map] :
    ∀ store : Store map,
      store.time = store.genesisTime →
      (getCurrentSlot (StoreTransition := GloasStoreRun map) store).run store
        = .ok (0, store) := by
  intro store htime
  simp [getCurrentSlot, getSlotsSinceGenesis, htime, EthCLLib.Spec.checkedSub,
    EthCLLib.Spec.checkedMul, EthCLSpecs.Fulu.Const.genesisSlot]
  rfl

end EthCLSpecs.Proofs
