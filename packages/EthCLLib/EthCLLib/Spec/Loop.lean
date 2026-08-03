import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Spec.Loop`: the bounded-recursion control-flow primitives

For the loops whose decreasing measure resists a clean well-founded argument
(the fork-choice walks, where the bound is a runtime store size), the framework
provides `fuelLoop`: structural recursion on a `Nat` fuel, total and
kernel-reducible (`FRAMEWORK_ARCHITECTURE.md` §12). The author writes only the
step body returning `Step.done`/`Step.next`; no `Nat` counter, no exhaustion
branch. The "fuel never exhausted on a well-formed store" fact becomes a separate,
deferrable lemma rather than a gate on the definition.

Structural folds (`forM` / `foldl`) and clean-measure well-founded recursion
(`processSlots`) need none of this; `fuelLoop` is the last resort, used only where
the up-front invariant proof would block the definition before proofs are in scope.
-/

set_option autoImplicit false

universe u v

namespace EthCLLib.Spec

/-- A loop step's outcome: `done a` stops with result `a`; `next b` continues with
the new accumulator `b`. -/
inductive Step (β : Type u) (α : Type v) where
  /-- Stop, returning `α`. -/
  | done : α → Step β α
  /-- Continue with the next accumulator `β`. -/
  | next : β → Step β α
  deriving Inhabited

/-- Bounded recursion: run `step` from `init` up to `fuel` times, returning the
first `Step.done` result, or `exhausted` if the fuel runs out. Structural on
`fuel`, so total and kernel-reducible. Monadic in `m` so a fork-choice walk reads
the store through it. -/
def fuelLoop {β α : Type} {m : Type → Type u} [Monad m]
    (fuel : Nat) (init : β) (exhausted : α) (step : β → m (Step β α)) : m α := do
  match fuel with
  | 0          => return exhausted
  | fuel' + 1 =>
    match ← step init with
    | .done a => return a
    | .next b => fuelLoop fuel' b exhausted step

/-- A bounded *walk* whose result is the accumulator itself: run `step` from `a` up to `fuel`
times, stopping at the first `Step.done`, and returning the current accumulator if the fuel runs
out. `step` runs in `m`, so the per-iteration body may read the store and throw. Structural on
`fuel`, total. Distinct from `fuelLoop`, whose fuel-out returns a fixed `exhausted` value rather
than the live accumulator; supply a `fuel` bound the walk cannot exceed (a store or block count)
so that case is unreachable, and reach for `fuelIterateM!` where it is not. -/
def fuelIterateM {α : Type} {m : Type → Type u} [Monad m]
    (fuel : Nat) (a : α) (step : α → m (Step α α)) : m α := do
  match fuel with
  | 0         => return a
  | fuel' + 1 => match ← step a with
    | .done b => return b
    | .next b => fuelIterateM fuel' b step

/-- `fuelIterateM` with no slack: exhausting the fuel throws instead of returning.

`fuelIterateM` returns the live accumulator on fuel-out, which suits a walk whose bound is a
store or block count that structurally cannot be exceeded. The `on_tick` catch-up is not that
walk: its bound is `(tick_slot - current_slot) + 1`, exact only because `1000` divides
`SLOT_DURATION_MS` (true at both pinned presets, 12000 and 6000, and asserted nowhere), so a
config breaking that divisibility would return a store whose clock never reached `time` and
surface later as an unrelated `checks: time` mismatch. Throw instead, so the failure names
itself.

Fuel-out rejects as `todo`, never `assert`. The bound belongs to this model rather than to any
spec text, so exhausting it is a work-queue item, and `todo` is the class that reports one
(`xfail`). `assert` is the class a runner scores as a vector's *expected* rejection, so a
fuel-out on a `valid: false` step would pass green on a bound we know is wrong. That is the
same reason `decodeFailure` stays out of `StoreTransitionError.isExpectedRejection`. Both
current call sites are `on_tick`, whose steps carry no `valid` flag and always run
`expectedValid := true`, so no verdict rides on this today. The class keeps it that way for
the next caller. -/
def fuelIterateM! {α : Type} {m : Type → Type u} {E : Type} [Monad m] [MonadExcept E m]
    [SpecReject E] (fuel : Nat) (a : α) (what : String) (step : α → m (Step α α)) : m α := do
  match fuel with
  | 0         => throw (SpecReject.todo s!"{what}: loop fuel exhausted")
  | fuel' + 1 => match ← step a with
    | .done b => return b
    | .next b => fuelIterateM! fuel' b what step

end EthCLLib.Spec
