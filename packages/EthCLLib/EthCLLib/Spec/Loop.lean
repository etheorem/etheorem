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

/-- The pure sibling of `fuelLoop`, for a total recursive *walk* whose result is the
accumulator itself: run `step` from `a` up to `fuel` times, stopping at the first
`Step.done`, and returning the current accumulator if the fuel runs out. The fuel-out case
returns `a` (the partial accumulator), matching a hand-rolled `| 0, a => a` walk, so supply
a `fuel` bound the walk cannot exceed (a store / block count) and exhaustion is unreachable.
Structural on `fuel`, total and kernel-reducible. Suits a fork-choice DAG walk whose step
has a single continuation (`get_ancestor`, the `get_head` descent); a walk that recurses
over many children at once (`filter_block_tree`) is genuine tree recursion and keeps its
own helper. -/
def fuelIterate {α : Type} (fuel : Nat) (a : α) (step : α → Step α α) : α :=
  match fuel with
  | 0         => a
  | fuel' + 1 => match step a with
    | .done b => b
    | .next b => fuelIterate fuel' b step

end EthCLLib.Spec
