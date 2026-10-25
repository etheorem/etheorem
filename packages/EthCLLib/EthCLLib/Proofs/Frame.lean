import EthCLLib.Proofs.Run

/-!
# `EthCLLib.Proofs.Frame`: which fields a store run leaves alone

A frame fact says that a run leaves one field of the state unchanged. Fork-choice handlers
write the store with `set`, and every store they write is a record update of a store they
read with `get`. So a frame fact for one field follows from the shape of the handler body,
one bind at a time. This module gives the rules for that walk, at any `StateT`-over-`Except`
runner and any field `f`.

Three predicates carry the fact through a body:

- `KeepsAt f v x`: a successful run from a state with `f = v` ends with `f = v`.
- `Resets f v x`: a successful run from any state ends with `f = v`. A body that ends with
  a `set` of a store whose `f` is `v` resets `f`, whatever ran before the `set`.
- `Returns f v x`: a successful run returns a state value with `f = v`. A helper that
  returns a record update of its store argument returns the field of that argument.

`KeepsAt.bind_reset` joins the first two. A bind whose continuation resets `f` keeps `f`,
so the first action needs no frame fact of its own. The `getHead` walk and the nested
state transition in `onBlock` are such first actions. `KeepsAt.bind_ret` joins the first
and the third. A bind whose first action returns a state value with `f = v` passes that
fact to the continuation, which then writes the value with `set`.

The loop rules (`fuelLoop`, `fuelIterateM!`, `forIn`, `foldlM`) take a frame fact for one
step and give it for the loop. `KeepsAt.prod` joins the frame facts of two fields into a
frame fact for the pair.

`view_forIn_list`, `view_forIn_array`, and `view_forIn_range` keep a view through a pure
`Id` loop over state values, the loops that state-transition bodies run inside a write.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

section
variable {σ ε α β γ : Type}

/-- `x` keeps the value `v` of the field `f`: a successful run from a state with `f = v`
ends in a state with `f = v`. -/
def KeepsAt (f : σ → β) (v : β) (x : StateT σ (Except ε) α) : Prop :=
  ∀ (s : σ) (a : α) (s' : σ), f s = v → x.run s = .ok (a, s') → f s' = v

/-- `x` sets the field `f` to `v`: a successful run from any state ends with `f = v`. -/
def Resets (f : σ → β) (v : β) (x : StateT σ (Except ε) α) : Prop :=
  ∀ (s : σ) (a : α) (s' : σ), x.run s = .ok (a, s') → f s' = v

/-- A successful run of `pure` leaves the state unchanged. -/
theorem run_pure_state_eq (a b : α) (s s' : σ)
    (h : (Pure.pure a : StateT σ (Except ε) α).run s = .ok (b, s')) : s' = s := by
  rw [run_pure] at h
  injection h with h
  injection h with _ h
  exact h.symm

/-- A successful run of `set t` ends in the state `t`. -/
theorem run_set_state_eq (t s : σ) (a : PUnit) (s' : σ)
    (h : (MonadStateOf.set t : StateT σ (Except ε) PUnit).run s = .ok (a, s')) : s' = t := by
  injection h with h
  injection h with _ h
  exact h.symm

/-- A run that resets `f` to `v` keeps it. -/
theorem KeepsAt.of_resets {f : σ → β} {v : β} {x : StateT σ (Except ε) α}
    (h : Resets f v x) : KeepsAt f v x :=
  fun s a s' _ hrun => h s a s' hrun

/-- A run that keeps two fields keeps the pair of them. -/
theorem KeepsAt.prod {δ : Type} {f : σ → β} {g : σ → δ} {v : β} {w : δ}
    {x : StateT σ (Except ε) α} (hf : KeepsAt f v x) (hg : KeepsAt g w x) :
    KeepsAt (fun s => (f s, g s)) (v, w) x := by
  intro s a s' hs hrun
  injection hs with hs1 hs2
  show (f s', g s') = (v, w)
  rw [hf s a s' hs1 hrun, hg s a s' hs2 hrun]

/-- `pure` keeps every field. -/
theorem KeepsAt.pure {f : σ → β} {v : β} (a : α) :
    KeepsAt f v (Pure.pure a : StateT σ (Except ε) α) :=
  fun s b s' hs hrun => (run_pure_state_eq a b s s' hrun) ▸ hs

/-- A bind keeps `f` when both parts keep it. -/
theorem KeepsAt.bind {f : σ → β} {v : β} {x : StateT σ (Except ε) α}
    {k : α → StateT σ (Except ε) γ} (hx : KeepsAt f v x) (hk : ∀ a, KeepsAt f v (k a)) :
    KeepsAt f v (x >>= k) := by
  intro s c s' hs hrun
  obtain ⟨a, s1, h1, h2⟩ := run_bind_eq_ok x k s (c, s') hrun
  exact hk a s1 c s' (hx s a s1 hs h1) h2

/-- After `get`, the continuation knows that the store it read has `f = v`. -/
theorem KeepsAt.get_bind {f : σ → β} {v : β} {k : σ → StateT σ (Except ε) γ}
    (hk : ∀ st, f st = v → KeepsAt f v (k st)) :
    KeepsAt f v ((get : StateT σ (Except ε) σ) >>= k) := by
  intro s c s' hs hrun
  exact hk s hs s c s' hs hrun

/-- `set t` keeps `f = v` when `t` has `f = v`. -/
theorem KeepsAt.set {f : σ → β} {v : β} (t : σ) (ht : f t = v) :
    KeepsAt f v (MonadStateOf.set t : StateT σ (Except ε) PUnit) :=
  fun s a s' _ hrun => (run_set_state_eq t s a s' hrun) ▸ ht

/-- A `throw` never succeeds, so it keeps every field. -/
theorem KeepsAt.throw {f : σ → β} {v : β} (e : ε) :
    KeepsAt f v (MonadExceptOf.throw e : StateT σ (Except ε) α) := by
  intro s a s' _ hrun
  cases hrun

/-- Lifting an `Except` value keeps every field: it is a `pure` or a `throw`. -/
theorem KeepsAt.ofExcept {f : σ → β} {v : β} (e : Except ε α) :
    KeepsAt f v (MonadExcept.ofExcept e : StateT σ (Except ε) α) := by
  cases e with
  | error err => exact KeepsAt.throw err
  | ok a => exact KeepsAt.pure a

/-- A `throw` never succeeds, so it resets every field. -/
theorem Resets.throw {f : σ → β} {v : β} (e : ε) :
    Resets f v (MonadExceptOf.throw e : StateT σ (Except ε) α) := by
  intro s a s' hrun
  cases hrun

/-- `set t` resets `f` to the value `t` has. -/
theorem Resets.set {f : σ → β} {v : β} (t : σ) (ht : f t = v) :
    Resets f v (MonadStateOf.set t : StateT σ (Except ε) PUnit) :=
  fun s a s' hrun => (run_set_state_eq t s a s' hrun) ▸ ht

/-- A bind resets `f` when its continuation does, whatever the first action does. -/
theorem Resets.bind_any {f : σ → β} {v : β} (x : StateT σ (Except ε) α)
    {k : α → StateT σ (Except ε) γ} (hk : ∀ a, Resets f v (k a)) :
    Resets f v (x >>= k) := by
  intro s c s' hrun
  obtain ⟨a, s1, _, h2⟩ := run_bind_eq_ok x k s (c, s') hrun
  exact hk a s1 c s' h2

/-- `Resets.bind_any` with the first action implicit, for goal-directed use. -/
theorem Resets.bind {f : σ → β} {v : β} {x : StateT σ (Except ε) α}
    {k : α → StateT σ (Except ε) γ} (hk : ∀ a, Resets f v (k a)) :
    Resets f v (x >>= k) :=
  Resets.bind_any x hk

/-- A bind whose continuation sets `f` to `v` keeps `f`, whatever the first action does. -/
theorem KeepsAt.bind_reset {f : σ → β} {v : β} {x : StateT σ (Except ε) α}
    {k : α → StateT σ (Except ε) γ} (hk : ∀ a, Resets f v (k a)) :
    KeepsAt f v (x >>= k) :=
  KeepsAt.of_resets (Resets.bind_any x hk)

/-- `set t` followed by a continuation that keeps `f` resets `f` to the value `t` has. -/
theorem Resets.set_bind {f : σ → β} {v : β} (t : σ) {k : PUnit → StateT σ (Except ε) γ}
    (ht : f t = v) (hk : KeepsAt f v (k PUnit.unit)) :
    Resets f v ((MonadStateOf.set t : StateT σ (Except ε) PUnit) >>= k) := by
  intro s c s' hrun
  obtain ⟨a, s1, h1, h2⟩ := run_bind_eq_ok _ k s (c, s') hrun
  have hs1 : f s1 = v := (run_set_state_eq t s a s1 h1) ▸ ht
  exact hk s1 c s' hs1 h2

/-- `Resets.set_bind` as a `KeepsAt` fact. -/
theorem KeepsAt.set_bind {f : σ → β} {v : β} (t : σ) {k : PUnit → StateT σ (Except ε) γ}
    (ht : f t = v) (hk : KeepsAt f v (k PUnit.unit)) :
    KeepsAt f v ((MonadStateOf.set t : StateT σ (Except ε) PUnit) >>= k) :=
  KeepsAt.of_resets (Resets.set_bind t ht hk)

/-- `x` returns a state value whose field `f` is `v`. -/
def Returns (f : σ → β) (v : β) (x : StateT σ (Except ε) σ) : Prop :=
  ∀ (s a s' : σ), x.run s = .ok (a, s') → f a = v

/-- `pure a` returns `a`. -/
theorem Returns.pure {f : σ → β} {v : β} (a : σ) (ha : f a = v) :
    Returns f v (Pure.pure a : StateT σ (Except ε) σ) := by
  intro s b s' hrun
  rw [run_pure_eq_ok a b s s' hrun]
  exact ha

/-- A `throw` returns nothing. -/
theorem Returns.throw {f : σ → β} {v : β} (e : ε) :
    Returns f v (MonadExceptOf.throw e : StateT σ (Except ε) σ) := by
  intro s a s' hrun
  cases hrun

/-- A bind returns what its continuation returns. -/
theorem Returns.bind {f : σ → β} {v : β} {x : StateT σ (Except ε) α}
    {k : α → StateT σ (Except ε) σ} (hk : ∀ a, Returns f v (k a)) :
    Returns f v (x >>= k) := by
  intro s c s' hrun
  obtain ⟨a, s1, _, h2⟩ := run_bind_eq_ok x k s (c, s') hrun
  exact hk a s1 c s' h2

/-- A bind whose first action keeps `f` and returns a state value with `f = v`. The
continuation learns that the returned value has `f = v`. -/
theorem KeepsAt.bind_ret {f : σ → β} {v : β} {x : StateT σ (Except ε) σ}
    {k : σ → StateT σ (Except ε) γ} (hx : KeepsAt f v x) (hr : Returns f v x)
    (hk : ∀ a, f a = v → KeepsAt f v (k a)) : KeepsAt f v (x >>= k) := by
  intro s c s' hs hrun
  obtain ⟨a, s1, h1, h2⟩ := run_bind_eq_ok x k s (c, s') hrun
  exact hk a (hr s a s1 h1) s1 c s' (hx s a s1 hs h1) h2

/-- `fuelLoop` keeps `f` when each step keeps it. -/
theorem KeepsAt.fuelLoop {f : σ → β} {v : β} {δ : Type} (exhausted : α)
    (step : δ → StateT σ (Except ε) (EthCLLib.Spec.Step δ α))
    (hstep : ∀ b, KeepsAt f v (step b)) :
    ∀ (fuel : Nat) (init : δ),
      KeepsAt f v (EthCLLib.Spec.fuelLoop fuel init exhausted step) := by
  intro fuel
  induction fuel with
  | zero => intro init; exact KeepsAt.pure exhausted
  | succ fuel ih =>
    intro init
    simp only [EthCLLib.Spec.fuelLoop]
    refine KeepsAt.bind (hstep init) fun st => ?_
    cases st with
    | done a => exact KeepsAt.pure a
    | next b => exact ih b

/-- `fuelIterateM!` keeps `f` when each step keeps it. Fuel-out throws. -/
theorem KeepsAt.fuelIterateM! {f : σ → β} {v : β} [EthCLLib.Spec.SpecReject ε]
    (what : String) (step : α → StateT σ (Except ε) (EthCLLib.Spec.Step α α))
    (hstep : ∀ b, KeepsAt f v (step b)) :
    ∀ (fuel : Nat) (init : α),
      KeepsAt f v (EthCLLib.Spec.fuelIterateM! fuel init what step) := by
  intro fuel
  induction fuel with
  | zero =>
    intro init s a s' _ hrun
    cases hrun
  | succ fuel ih =>
    intro init
    simp only [EthCLLib.Spec.fuelIterateM!]
    refine KeepsAt.bind (hstep init) fun st => ?_
    cases st with
    | done a => exact KeepsAt.pure a
    | next b => exact ih b

/-- A `for` loop over a list keeps `f` when each body run keeps it. -/
theorem KeepsAt.forIn_list {f : σ → β} {v : β} {δ : Type}
    (body : δ → α → StateT σ (Except ε) (ForInStep α))
    (hbody : ∀ d a, KeepsAt f v (body d a)) :
    ∀ (l : List δ) (init : α), KeepsAt f v (forIn l init body) := by
  intro l
  induction l with
  | nil => intro init; exact KeepsAt.pure init
  | cons d rest ih =>
    intro init
    rw [List.forIn_cons]
    refine KeepsAt.bind (hbody d init) fun st => ?_
    cases st with
    | done a => exact KeepsAt.pure a
    | yield a => exact ih a

/-- A left fold over a list keeps `f` when each step keeps it. -/
theorem KeepsAt.foldlM_list {f : σ → β} {v : β} {δ : Type}
    (step : α → δ → StateT σ (Except ε) α) (hstep : ∀ a d, KeepsAt f v (step a d)) :
    ∀ (l : List δ) (init : α), KeepsAt f v (l.foldlM step init) := by
  intro l
  induction l with
  | nil => intro init; exact KeepsAt.pure init
  | cons d rest ih =>
    intro init
    rw [List.foldlM_cons]
    exact KeepsAt.bind (hstep init d) fun a => ih a

/-- A left fold over an array keeps `f` when each step keeps it. -/
theorem KeepsAt.foldlM_array {f : σ → β} {v : β} {δ : Type}
    (step : α → δ → StateT σ (Except ε) α) (hstep : ∀ a d, KeepsAt f v (step a d))
    (xs : Array δ) (init : α) : KeepsAt f v (xs.foldlM step init) := by
  rw [← Array.foldlM_toList]
  exact KeepsAt.foldlM_list step hstep xs.toList init

/-- A `for` loop over an array keeps `f` when each body run keeps it. -/
theorem KeepsAt.forIn_array {f : σ → β} {v : β} {δ : Type}
    (body : δ → α → StateT σ (Except ε) (ForInStep α))
    (hbody : ∀ d a, KeepsAt f v (body d a)) (xs : Array δ) (init : α) :
    KeepsAt f v (forIn xs init body) := by
  rw [← Array.forIn_toList]
  exact KeepsAt.forIn_list body hbody xs.toList init

/-- The value of a `yield` step. Rewriting with this lemma keeps the `match` of
`ForInStep.value` out of the goal, so `split` sees the branches of the loop body. -/
theorem forInStep_value_yield {α : Type} (a : α) : (ForInStep.yield a).value = a := rfl

/-- The value of a `done` step. -/
theorem forInStep_value_done {α : Type} (a : α) : (ForInStep.done a).value = a := rfl

/-- A pure `for` loop over a list keeps `f` of its accumulator when each body step does.
Epoch substeps run such loops inside `modifyState`. -/
theorem view_forIn_list {δ : Type} (f : σ → β) (body : δ → σ → Id (ForInStep σ))
    (hbody : ∀ d a, f (body d a).run.value = f a) :
    ∀ (l : List δ) (init : σ), f (forIn l init body).run = f init := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons d rest ih =>
    intro init
    rw [List.forIn_cons]
    have hd := hbody d init
    revert hd
    cases body d init with
    | done a => intro hd; exact hd
    | yield a => intro hd; rw [← hd]; exact ih a

/-- `view_forIn_list` for a loop over an array. -/
theorem view_forIn_array {δ : Type} (f : σ → β) (body : δ → σ → Id (ForInStep σ))
    (hbody : ∀ d a, f (body d a).run.value = f a) (xs : Array δ) (init : σ) :
    f (forIn xs init body).run = f init := by
  rw [← Array.forIn_toList]
  exact view_forIn_list f body hbody xs.toList init

/-- `view_forIn_list` for a loop over a range. -/
theorem view_forIn_range (f : σ → β) (body : Nat → σ → Id (ForInStep σ))
    (hbody : ∀ d a, f (body d a).run.value = f a) (r : Std.Legacy.Range) (init : σ) :
    f (forIn r init body).run = f init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact view_forIn_list f body hbody _ init

end

end EthCLLib.Proofs
