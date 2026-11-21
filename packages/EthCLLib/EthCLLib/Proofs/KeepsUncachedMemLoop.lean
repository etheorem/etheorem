import EthCLLib.Proofs.KeepsUncached

/-!
# `EthCLLib.Proofs.KeepsUncachedMemLoop`: membership loops keep the uncached box

`for h : i in xs do body` binds a proof `h : i ∈ xs` that the body can use, for
example as the bound of an array read `a[i]'…`. Lean elaborates this loop to `forIn'`,
not `forIn`. The body is then a function of the element and of the membership proof.
The loop lemmas of `EthCLLib/Proofs/KeepsUncached.lean` are about `forIn` only, so this
file adds the `forIn'` forms that a spec body with such a loop needs.

The list lemma carries an invariant `P` on the accumulator by induction on the list.
The step lemma `List.forIn'_cons` passes the rest of the loop a body whose membership
proof is `List.mem_cons_of_mem`, so the induction generalizes over the body. The range
lemma reduces `forIn'` over `[0:n]` to the list `List.range' 0 n 1` through the core
lemma `Std.Legacy.Range.forIn'_eq_forIn'_range'`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (HasherTag)
open SizzLean (SSZRepr)
open SizzLean.Cache

/-- A membership loop over a list whose accumulator satisfies `P` keeps the flavour,
and returns an accumulator that satisfies `P`, when every body step does the same for
an accumulator that satisfies `P`. The `forIn'` form of
`keepsUncachedFrom_forIn_list_inv`. -/
theorem keepsUncachedFrom_forIn'_list_inv {T ε α β : Type} [SSZRepr T] [HasherTag]
    (P : β → Prop) :
    ∀ (l : List α) (f : (a : α) → a ∈ l → β →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)),
    (∀ x hx b v r s, P b → (f x hx b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value) →
    ∀ (init : β) (v : T), P init →
      KeepsUncachedFrom v (forIn' l init f) ∧
        ∀ r s, (forIn' l init f).run (pureState v) = .ok (r, s) → P r := by
  intro l
  induction l with
  | nil =>
    intro f _ init v hinit
    refine ⟨fun a s h => ?_, fun r s h => ?_⟩
    · rw [List.forIn'_nil] at h
      injection h with h1
      injection h1 with _ h3
      subst h3
      rfl
    · rw [List.forIn'_nil] at h
      injection h with h1
      injection h1 with h2 _
      subst h2
      exact hinit
  | cons x rest ih =>
    intro f hf init v hinit
    rw [List.forIn'_cons]
    have hrest := ih (fun a' m b => f a' (List.mem_cons_of_mem x m) b)
      (fun a' m b v' r s hb h => hf a' _ b v' r s hb h)
    refine ⟨?_, ?_⟩
    · intro a s h
      rw [run_bind] at h
      cases hstep : (f x List.mem_cons_self init).run (pureState v) with
      | error e =>
        rw [hstep, except_bind_error] at h
        simp at h
      | ok p =>
        obtain ⟨st, s'⟩ := p
        rw [hstep, except_bind_ok] at h
        obtain ⟨hthread, hP⟩ := hf x _ init v st s' hinit hstep
        rw [hthread] at h
        cases st with
        | done x' => exact keepsUncached_pure x' s'.view a s h
        | yield b => exact (hrest b s'.view hP).1 a s h
    · intro r s h
      rw [run_bind] at h
      cases hstep : (f x List.mem_cons_self init).run (pureState v) with
      | error e =>
        rw [hstep, except_bind_error] at h
        simp at h
      | ok p =>
        obtain ⟨st, s'⟩ := p
        rw [hstep, except_bind_ok] at h
        obtain ⟨hthread, hP⟩ := hf x _ init v st s' hinit hstep
        rw [hthread] at h
        cases st with
        | done x' =>
          injection h with h1
          injection h1 with h2 _
          subst h2
          exact hP
        | yield b => exact (hrest b s'.view hP).2 r s h

/-- A loop body that returns its box accumulator as a pure box gives the body fact of
the invariant loop lemmas with `P := IsPure`. The two facts hold the same two
conjuncts in the opposite order. -/
theorem step_of_returnsPureVia {T ε : Type} [SSZRepr T] [HasherTag]
    {act : StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T))}
    (h : ReturnsPureVia ForInStep.value act) :
    ∀ v r s, act.run (pureState v) = .ok (r, s) → s = pureState s.view ∧ IsPure r.value :=
  fun v r s hrun => (fun p => ⟨p.2, p.1⟩) (h v r s hrun)

/-- A membership loop over a list whose accumulator satisfies `P`, bound to its
continuation `k`, keeps the flavour. The continuation's fact is stated under `P`. The
`forIn'` form of `keepsUncachedFrom_forIn_list_bind_P`. -/
theorem keepsUncachedFrom_forIn'_list_bind_P {T ε α β γ : Type} [SSZRepr T] [HasherTag]
    (l : List α)
    (f : (a : α) → a ∈ l → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (k : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ) (P : β → Prop)
    (hf : ∀ x hx b v r s, P b → (f x hx b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (hk : ∀ b w', P b → KeepsUncachedFrom w' (k b))
    (init : β) {v : T} (hinit : P init) :
    KeepsUncachedFrom v (forIn' l init f >>= k) := by
  obtain ⟨h1, h2⟩ := keepsUncachedFrom_forIn'_list_inv P l f hf init v hinit
  intro a s h
  rw [run_bind] at h
  cases hx : (forIn' l init f).run (pureState v) with
  | error e =>
    rw [hx, except_bind_error] at h
    simp at h
  | ok p =>
    obtain ⟨a', s'⟩ := p
    rw [hx, except_bind_ok] at h
    rw [h1 a' s' hx] at h
    exact hk a' s'.view (h2 a' s' hx) a s h

/-- A membership loop over `[0:n]` whose accumulator satisfies `P`, bound to its
continuation `k`, keeps the flavour. The continuation's fact is stated under `P`, so a
proof of the code after the loop can name the box in the accumulator. The `forIn'`
form of `keepsUncachedFrom_forIn_range_bind_P`, and the shape of the
`for h : i in [0:n]` loop of `processSyncAggregate`. -/
theorem keepsUncachedFrom_forIn'_range_bind_P {T ε β γ : Type} [SSZRepr T] [HasherTag]
    (n : Nat)
    (f : (i : Nat) → i ∈ [0:n] → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (k : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ) (P : β → Prop)
    (hf : ∀ x hx b v r s, P b → (f x hx b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (hk : ∀ b w', P b → KeepsUncachedFrom w' (k b))
    (init : β) {v : T} (hinit : P init) :
    KeepsUncachedFrom v (forIn' [0:n] init f >>= k) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact keepsUncachedFrom_forIn'_list_bind_P _ _ k P
    (fun x _ b v' r s hb h => hf x _ b v' r s hb h) hk init hinit

end EthCLLib.Proofs
