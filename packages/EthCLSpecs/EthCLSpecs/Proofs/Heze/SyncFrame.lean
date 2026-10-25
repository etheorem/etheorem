import EthCLSpecs.Proofs.Heze.FrameInvert

/-!
# `EthCLSpecs.Proofs.Heze.SyncFrame`: the frame of the sync aggregate

`processSyncAggregate` chooses its verification keys in three branches, and the rest of the
body is a join point that each branch calls. `frame_invert` inlines the join point into
each branch of the nested `if`, and the term grows too large. So `sync_frame` names the
join point and runs each branch up to it. The key choice does not change the state: each
branch is `pure` and `liftErr` steps. Then `frame_invert` inverts the join point once.

The join point searches the registry for the position of each committee key, an
`Array.mapM` whose steps read the state only. `committeeIndices_frame` states that, so
`frame_invert` does not unfold `Array.mapM`.

This module is separate from `FrameInvert.lean`, because `frame_invert` cannot run in the
module that declares it.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (run_bind except_bind_ok except_bind_error run_liftErr_of_ok
  run_liftErr_of_error)

/-- A successful `liftErr` bind runs its continuation on the same state. -/
theorem run_liftErr_bind_eq_ok {σ ε' ε α β : Type} [EthCLLib.Spec.ErrorConv ε' ε]
    {x : Except ε' α} {k : α → StateT σ (Except ε) β} {s : σ} {r : β × σ}
    (h : (EthCLLib.Spec.liftErr (m := StateT σ (Except ε)) (E := ε') (F := ε) x >>= k).run s
      = .ok r) :
    ∃ a, (k a).run s = .ok r := by
  cases hx : Except.mapError (EthCLLib.Spec.ErrorConv.conv (F := ε)) x with
  | error e =>
    rw [run_bind, run_liftErr_of_error x s hx, except_bind_error] at h
    cases h
  | ok a =>
    rw [run_bind, run_liftErr_of_ok x s hx, except_bind_ok] at h
    exact ⟨a, h⟩

/-- `List.mapM` keeps the state when each step keeps it. -/
theorem listMapM_run_state_eq {σ ε β γ : Type} {f : β → StateT σ (Except ε) γ}
    (hf : ∀ b s a s', (f b).run s = .ok (a, s') → s' = s) :
    ∀ (ys : List β) (s s' : σ) (l : List γ), (ys.mapM f).run s = .ok (l, s') → s' = s := by
  intro ys
  induction ys with
  | nil =>
    intro s s' l h
    rw [List.mapM_nil] at h
    exact (EthCLLib.Proofs.run_pure_eq_ok_state h).2
  | cons b ys ih =>
    intro s s' l h
    rw [List.mapM_cons] at h
    obtain ⟨_, s2, hb, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
    obtain ⟨_, s3, hbs, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
    rw [(EthCLLib.Proofs.run_pure_eq_ok_state h).2, ih s2 s3 _ hbs, hf _ _ _ _ hb]

/-- `Array.mapM` keeps the state when each step keeps it. -/
theorem mapM_run_state_eq {σ ε β γ : Type} {f : β → StateT σ (Except ε) γ}
    (hf : ∀ b s a s', (f b).run s = .ok (a, s') → s' = s) (xs : Array β) {s s' : σ}
    {a : Array γ} (h : (xs.mapM f).run s = .ok (a, s')) : s' = s := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h
  obtain ⟨l, s1, h1, h2⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
  rw [(EthCLLib.Proofs.run_pure_eq_ok_state h2).2]
  exact listMapM_run_state_eq hf _ _ _ _ h1

section
variable [EthCLSpecs.Heze.Preset] [EthCLLib.Spec.HasherTag]

/-- The committee index search of `processSyncAggregate` reads the state only. Each step
returns a registry position or raises. -/
@[frame] theorem committeeIndices_frame {t t' : EthCLSpecs.Heze.BeaconState}
    {a : Array EthCLSpecs.Heze.ValidatorIndex} {vals : Array EthCLSpecs.Heze.Validator}
    {pks : Array EthCLSpecs.Heze.BLSPubkey}
    (h : (pks.mapM (fun pk => (match vals.findIdx? (·.pubkey == pk) with
        | some pIdx => pure (UInt64.ofNat pIdx)
        | none => EthCLLib.Spec.throwArithmetic
            "process_sync_aggregate: all_pubkeys.index(pubkey)" :
          HezeRun EthCLSpecs.Heze.ValidatorIndex))).run (EthCLLib.Proofs.pureState t)
      = .ok (a, EthCLLib.Proofs.pureState t')) :
    (EthCLLib.Proofs.pureState t').view = (EthCLLib.Proofs.pureState t).view := by
  rw [mapM_run_state_eq (fun b s a s' hb => ?_) pks h]
  split at hb
  · exact (EthCLLib.Proofs.run_pure_eq_ok_state hb).2
  · unfold EthCLLib.Spec.throwArithmetic at hb
    rw [run_liftErr_of_error _ _ rfl] at hb
    cases hb

end

/-- Prove `V (pureState t') = V (pureState t)` from a run `h` of `processSyncAggregate` from
`pureState t` to `pureState t'`. The first `extract_lets` names the seven reads before the
key choice and the join point `jp` after it. In each branch, `h` becomes a run of `jp`
from `pureState t`, and `frame_invert` inverts it. -/
syntax "sync_frame " term:max ident : tactic
macro_rules
  | `(tactic| sync_frame $V $h) => `(tactic| (
      unfold EthCLSpecs.Heze.processSyncAggregate at $h:ident
      replace $h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ $h
      extract_lets _ _ _ _ _ _ _ jp at $h:ident
      -- Each branch passes its keys `y` to `jp` on the start state.
      obtain ⟨_, $h:ident⟩ : ∃ y, (jp y).run _ = _ := by
        split at $h:ident
        · rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_pure,
            EthCLLib.Proofs.except_bind_ok] at $h:ident
          exact ⟨_, $h⟩
        · split at $h:ident
          · -- The G1 arithmetic: three `liftErr` steps, then `pure` of the keys.
            obtain ⟨_, $h:ident⟩ := EthCLSpecs.Proofs.Heze.run_liftErr_bind_eq_ok $h
            obtain ⟨_, $h:ident⟩ := EthCLSpecs.Proofs.Heze.run_liftErr_bind_eq_ok $h
            obtain ⟨_, $h:ident⟩ := EthCLSpecs.Proofs.Heze.run_liftErr_bind_eq_ok $h
            rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_pure,
              EthCLLib.Proofs.except_bind_ok] at $h:ident
            exact ⟨_, $h⟩
          · rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_pure,
              EthCLLib.Proofs.except_bind_ok] at $h:ident
            exact ⟨_, $h⟩
      -- `extract_lets` named the reads too. Inline them, so that `frame_invert` sees the
      -- body as written.
      dsimp -zeta +zetaDelta only at $h:ident
      show $V _ = $V _
      frame_invert $h))

end EthCLSpecs.Proofs.Heze
