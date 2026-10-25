import EthCLLib.Spec
import EthCLLib.Proofs.Run

/-!
# `EthCLLib.Proofs.StateFree`: runs that read and write no runner state

A fork-choice query such as `getAttestationScore` reads its `store` argument and never the
runner state. So every run gives the same value, and the run keeps the state. `StateFree`
states this for one action. The rules below carry it through `pure`, `throw`, a bind, and
`fuelLoop`. `free_solve` applies them to a body.

A theorem about a query can then take a run at one runner state and conclude at another.
The `getHead` walk threads its own runner state, so its callers need that step.
`EthCLSpecs/Proofs/Heze/HeadAvoidsFull.lean` proves the same fact for `getParentPayloadStatus` alone
(`getParentPayloadStatus_run_val`).
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

section
variable {σ ε α β : Type}

/-- `x` reads and writes no runner state: one `Except` value `e` gives every run, and each
run keeps its state. -/
def StateFree (x : StateT σ (Except ε) α) : Prop :=
  ∃ e : Except ε α, ∀ s, x.run s = (fun a => (a, s)) <$> e

/-- `pure` reads no state. -/
theorem StateFree.pure (a : α) : StateFree (Pure.pure a : StateT σ (Except ε) α) :=
  ⟨.ok a, fun _ => rfl⟩

/-- `throw` reads no state. -/
theorem StateFree.throw (e : ε) :
    StateFree (MonadExceptOf.throw e : StateT σ (Except ε) α) :=
  ⟨.error e, fun _ => rfl⟩

/-- A bind reads no state when both parts read none. -/
theorem StateFree.bind {x : StateT σ (Except ε) α} {k : α → StateT σ (Except ε) β}
    (hx : StateFree x) (hk : ∀ a, StateFree (k a)) : StateFree (x >>= k) := by
  obtain ⟨e, he⟩ := hx
  cases e with
  | error err => exact ⟨.error err, fun s => by rw [run_bind, he]; rfl⟩
  | ok a =>
    obtain ⟨e', he'⟩ := hk a
    exact ⟨e', fun s => by rw [run_bind, he]; exact he' s⟩

/-- `fuelLoop` reads no state when its step reads none. -/
theorem StateFree.fuelLoop (step : β → StateT σ (Except ε) (EthCLLib.Spec.Step β α))
    (exhausted : α) (hstep : ∀ b, StateFree (step b)) :
    ∀ fuel init, StateFree (EthCLLib.Spec.fuelLoop fuel init exhausted step) := by
  intro fuel
  induction fuel with
  | zero => intro init; exact StateFree.pure exhausted
  | succ fuel ih =>
    intro init
    simp only [EthCLLib.Spec.fuelLoop]
    refine StateFree.bind (hstep init) fun st => ?_
    cases st with
    | done a => exact StateFree.pure a
    | next b => exact ih b

/-- A successful run of a state-free action keeps the state, and every other runner state
gives the same value. -/
theorem StateFree.run_eq {x : StateT σ (Except ε) α} (hx : StateFree x) {s s' : σ} {a : α}
    (h : x.run s = .ok (a, s')) : s' = s ∧ ∀ t, x.run t = .ok (a, t) := by
  obtain ⟨e, he⟩ := hx
  rw [he] at h
  cases e with
  | error err => cases h
  | ok b =>
    injection h with h
    injection h with h1 h2
    subst h1 h2
    exact ⟨rfl, fun t => he t⟩

end

/-- Prove `StateFree` of a body whose helpers are already unfolded: apply the rules, split
each `if` and `match`, and unfold the store reads. -/
syntax "free_solve" : tactic
macro_rules
  | `(tactic| free_solve) => `(tactic| repeat' (first
      | exact EthCLLib.Proofs.StateFree.pure _
      | exact EthCLLib.Proofs.StateFree.throw _
      | refine EthCLLib.Proofs.StateFree.fuelLoop _ _ (fun _ => ?_) _ _
      | refine EthCLLib.Proofs.StateFree.bind ?_ fun _ => ?_
      | split
      | unfold EthCLLib.Spec.FcMap.getOrThrow
      | unfold EthCLLib.Spec.FcMap.getOrThrowKey))

end EthCLLib.Proofs
