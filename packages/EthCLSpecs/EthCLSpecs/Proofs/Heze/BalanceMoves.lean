import EthCLSpecs.Proofs.Heze.DriftDefs

/-!
# `EthCLSpecs.Proofs.Heze.BalanceMoves`: what one balance write moves

`increase_balance` and `decrease_balance` write one balance. On a plain state, a successful
run of either returns the state with that one balance changed by at most `delta`
(`increaseBalance_run_ok`, `decreaseBalance_run_ok`). So it moves `moveN` by at most `delta`
(`moveN_increaseBalance`, `moveN_decreaseBalance`).

`forIn_move_le` bounds the move of a loop by the sum of the bounds of its steps, for any
measure with the triangle inequality.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure run_bind_eq_ok run_pure_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset BeaconState ValidatorIndex Validator Gwei)

/-- A loop moves a measure by at most the sum of the moves of its steps. Each step keeps `P`
of the accumulator and moves it by at most `β` of its element. -/
theorem forIn_move_le {σ τ ε δ : Type} (M : σ → σ → Nat)
    (htri : ∀ a b c, M a c ≤ M a b + M b c) (hrefl : ∀ a, M a a = 0) (P : σ → Prop)
    (β : δ → Nat) (body : δ → σ → StateT τ (Except ε) (ForInStep σ)) :
    ∀ l : List δ,
      (∀ d ∈ l, ∀ (acc : σ) (s s' : τ) (st : ForInStep σ), P acc →
        (body d acc).run s = .ok (st, s') → P st.value ∧ M acc st.value ≤ β d) →
      ∀ (init : σ) (s s' : τ) (r : σ), P init → (forIn l init body).run s = .ok (r, s') →
        P r ∧ M init r ≤ (l.map β).sum := by
  intro l
  induction l with
  | nil =>
    intro _ init s s' r hP h
    rw [List.forIn_nil] at h
    have := run_pure_eq_ok _ _ _ _ h
    subst this
    exact ⟨hP, by rw [hrefl]; exact Nat.zero_le _⟩
  | cons d rest ih =>
    intro hstep init s s' r hP h
    rw [List.forIn_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨hP1, hM1⟩ := hstep d List.mem_cons_self init s s1 st hP hbody
    simp only [List.map_cons, List.sum_cons]
    cases st with
    | done b =>
      have := run_pure_eq_ok _ _ _ _ hrest
      subst this
      exact ⟨hP1, Nat.le_trans hM1 (Nat.le_add_right _ _)⟩
    | yield b =>
      obtain ⟨hPr, hMr⟩ := ih (fun x hx => hstep x (List.mem_cons_of_mem _ hx)) b s1 s' r hP1 hrest
      exact ⟨hPr, Nat.le_trans (htri _ _ _) (Nat.add_le_add hM1 hMr)⟩

/-- `forIn_move_le` with an invariant `S` of the threaded state. A step starts from a threaded
state with `S`, and ends at one. -/
theorem forIn_move_le_inv {σ τ ε δ : Type} (M : σ → σ → Nat)
    (htri : ∀ a b c, M a c ≤ M a b + M b c) (hrefl : ∀ a, M a a = 0) (P : σ → Prop)
    (S : τ → Prop) (β : δ → Nat) (body : δ → σ → StateT τ (Except ε) (ForInStep σ)) :
    ∀ l : List δ,
      (∀ d ∈ l, ∀ (acc : σ) (s s' : τ) (st : ForInStep σ), P acc → S s →
        (body d acc).run s = .ok (st, s') → P st.value ∧ S s' ∧ M acc st.value ≤ β d) →
      ∀ (init : σ) (s s' : τ) (r : σ), P init → S s → (forIn l init body).run s = .ok (r, s') →
        P r ∧ S s' ∧ M init r ≤ (l.map β).sum := by
  intro l
  induction l with
  | nil =>
    intro _ init s s' r hP hS h
    rw [List.forIn_nil] at h
    have e1 := run_pure_eq_ok _ _ _ _ h
    have e2 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h
    subst e1 e2
    exact ⟨hP, hS, by rw [hrefl]; exact Nat.zero_le _⟩
  | cons d rest ih =>
    intro hstep init s s' r hP hS h
    rw [List.forIn_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨hP1, hS1, hM1⟩ := hstep d List.mem_cons_self init s s1 st hP hS hbody
    simp only [List.map_cons, List.sum_cons]
    cases st with
    | done b =>
      have e1 := run_pure_eq_ok _ _ _ _ hrest
      have e2 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hrest
      subst e1 e2
      exact ⟨hP1, hS1, Nat.le_trans hM1 (Nat.le_add_right _ _)⟩
    | yield b =>
      obtain ⟨hPr, hSr, hMr⟩ :=
        ih (fun x hx => hstep x (List.mem_cons_of_mem _ hx)) b s1 s' r hP1 hS1 hrest
      exact ⟨hPr, hSr, Nat.le_trans (htri _ _ _) (Nat.add_le_add hM1 hMr)⟩

/-- `forIn_move_le` for a loop that binds a membership proof, with one bound for every step. -/
theorem forIn'_move_le {σ τ ε δ : Type} (M : σ → σ → Nat)
    (htri : ∀ a b c, M a c ≤ M a b + M b c) (hrefl : ∀ a, M a a = 0) (P : σ → Prop)
    (β : Nat) :
    ∀ (l : List δ) (body : (d : δ) → d ∈ l → σ → StateT τ (Except ε) (ForInStep σ)),
      (∀ d hd (acc : σ) (s s' : τ) (st : ForInStep σ), P acc →
        (body d hd acc).run s = .ok (st, s') → P st.value ∧ M acc st.value ≤ β) →
      ∀ (init : σ) (s s' : τ) (r : σ), P init → (forIn' l init body).run s = .ok (r, s') →
        P r ∧ M init r ≤ β * l.length := by
  intro l
  induction l with
  | nil =>
    intro _ _ init s s' r hP h
    rw [List.forIn'_nil] at h
    have := run_pure_eq_ok _ _ _ _ h
    subst this
    exact ⟨hP, by rw [hrefl]; exact Nat.zero_le _⟩
  | cons d rest ih =>
    intro body hstep init s s' r hP h
    rw [List.forIn'_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨hP1, hM1⟩ := hstep d _ init s s1 st hP hbody
    rw [List.length_cons, Nat.mul_succ]
    cases st with
    | done b =>
      have := run_pure_eq_ok _ _ _ _ hrest
      subst this
      dsimp only [ForInStep.value] at hM1
      exact ⟨hP1, by omega⟩
    | yield b =>
      dsimp only [ForInStep.value] at hP1 hM1
      obtain ⟨hPr, hMr⟩ := ih _ (fun x hx => hstep x _) b s1 s' r hP1 hrest
      exact ⟨hPr, by have := htri init b r; omega⟩

/-- `forIn'_move_le` for a loop over a range. -/
theorem forIn'_range_move_le {σ τ ε : Type} (M : σ → σ → Nat)
    (htri : ∀ a b c, M a c ≤ M a b + M b c) (hrefl : ∀ a, M a a = 0) (P : σ → Prop)
    (β : Nat) (n : Nat)
    (body : (d : Nat) → d ∈ [0:n] → σ → StateT τ (Except ε) (ForInStep σ))
    (hstep : ∀ d hd (acc : σ) (s s' : τ) (st : ForInStep σ), P acc →
        (body d hd acc).run s = .ok (st, s') → P st.value ∧ M acc st.value ≤ β)
    (init : σ) (s s' : τ) (r : σ) (hP : P init) (h : (forIn' [0:n] init body).run s = .ok (r, s')) :
    P r ∧ M init r ≤ β * n := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at h
  have := forIn'_move_le M htri hrefl P β _ _ (fun d hd => hstep d _) init s s' r hP h
  simpa [Std.Legacy.Range.size] using this

/-- `forIn'_move_le` with an invariant `S` of the threaded state. -/
theorem forIn'_move_le_inv {σ τ ε δ : Type} (M : σ → σ → Nat)
    (htri : ∀ a b c, M a c ≤ M a b + M b c) (hrefl : ∀ a, M a a = 0) (P : σ → Prop)
    (S : τ → Prop) (β : Nat) :
    ∀ (l : List δ) (body : (d : δ) → d ∈ l → σ → StateT τ (Except ε) (ForInStep σ)),
      (∀ d hd (acc : σ) (s s' : τ) (st : ForInStep σ), P acc → S s →
        (body d hd acc).run s = .ok (st, s') → P st.value ∧ S s' ∧ M acc st.value ≤ β) →
      ∀ (init : σ) (s s' : τ) (r : σ), P init → S s →
        (forIn' l init body).run s = .ok (r, s') → P r ∧ S s' ∧ M init r ≤ β * l.length := by
  intro l
  induction l with
  | nil =>
    intro _ _ init s s' r hP hS h
    rw [List.forIn'_nil] at h
    have e1 := run_pure_eq_ok _ _ _ _ h
    have e2 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h
    subst e1 e2
    exact ⟨hP, hS, by rw [hrefl]; exact Nat.zero_le _⟩
  | cons d rest ih =>
    intro body hstep init s s' r hP hS h
    rw [List.forIn'_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨hP1, hS1, hM1⟩ := hstep d _ init s s1 st hP hS hbody
    rw [List.length_cons, Nat.mul_succ]
    cases st with
    | done b =>
      have e1 := run_pure_eq_ok _ _ _ _ hrest
      have e2 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hrest
      subst e1 e2
      dsimp only [ForInStep.value] at hM1
      exact ⟨hP1, hS1, by omega⟩
    | yield b =>
      dsimp only [ForInStep.value] at hP1 hM1
      obtain ⟨hPr, hSr, hMr⟩ := ih _ (fun x hx => hstep x _) b s1 s' r hP1 hS1 hrest
      exact ⟨hPr, hSr, by have := htri init b r; omega⟩

/-- `forIn'_move_le_inv` for a loop over a range. -/
theorem forIn'_range_move_le_inv {σ τ ε : Type} (M : σ → σ → Nat)
    (htri : ∀ a b c, M a c ≤ M a b + M b c) (hrefl : ∀ a, M a a = 0) (P : σ → Prop)
    (S : τ → Prop) (β : Nat) (n : Nat)
    (body : (d : Nat) → d ∈ [0:n] → σ → StateT τ (Except ε) (ForInStep σ))
    (hstep : ∀ d hd (acc : σ) (s s' : τ) (st : ForInStep σ), P acc → S s →
        (body d hd acc).run s = .ok (st, s') → P st.value ∧ S s' ∧ M acc st.value ≤ β)
    (init : σ) (s s' : τ) (r : σ) (hP : P init) (hS : S s)
    (h : (forIn' [0:n] init body).run s = .ok (r, s')) :
    P r ∧ S s' ∧ M init r ≤ β * n := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at h
  have := forIn'_move_le_inv M htri hrefl P S β _ _ (fun d hd => hstep d _) init s s' r hP hS h
  simpa [Std.Legacy.Range.size] using this

/-! ## Checked products and the square root

The reward amounts are `uint64` values with checked products. A successful product returns
the wrapping product, and the wrapping product is the `Nat` product
(`except_checkedMul_ok`). The run form in a state monad is `checkedMul_run_ok`
(`DriftChurn.lean`). -/

/-- The Newton loop of `isqrt` never rises above its start value. -/
theorem isqrtAux_le (n : Nat) : ∀ (fuel x : Nat), isqrtAux n fuel x ≤ x
  | 0, x => by unfold isqrtAux; exact Nat.le_refl _
  | fuel + 1, x => by
    unfold isqrtAux
    dsimp only
    split
    · rename_i hy
      exact Nat.le_trans (isqrtAux_le n fuel _) (Nat.le_of_lt hy)
    · exact Nat.le_refl _

/-- `isqrt n` is at most `n`. -/
theorem isqrt_le_self (n : Nat) : isqrt n ≤ n := by
  unfold isqrt
  split
  · exact Nat.zero_le _
  · exact isqrtAux_le n 200 n

/-- A successful `pure` in `Except` returns its value. -/
theorem except_pure_ok {ε α : Type} {x y : α} (h : (pure x : Except ε α) = .ok y) : y = x := by
  have h' : (Except.ok x : Except ε α) = .ok y := h
  injection h' with h'
  exact h'.symm

/-- A successful `checkedMul` in `Except` returns the product, and the product does not wrap. -/
theorem except_checkedMul_ok {a b r : UInt64} {d : String}
    (h : (checkedMul a b d : Except StateTransitionError UInt64) = .ok r) :
    r = a * b ∧ (a * b).toNat = a.toNat * b.toNat := by
  unfold checkedMul throwArithmetic at h
  split at h
  · cases h
  · rename_i hc
    exact ⟨except_pure_ok h, EthCLLib.Proofs.toNat_mul_of_guard _ _ hc⟩

section
variable [Preset] [HasherTag]

/-- A successful `increaseBalance` on a plain state keeps the threaded state and returns the
plain state with one balance raised by exactly `delta`. -/
theorem increaseBalance_run_ok (st w : BeaconState) (i : ValidatorIndex) (delta : Gwei)
    {x w' : BeaconState}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState st) i delta).run
      (pureState w) = .ok (pureState x, pureState w')) :
    w' = w ∧ ∃ g : Gwei, x = { st with balances := st.balances.set! i.toNat g } ∧
      absDiff g.toNat (balN st i.toNat) ≤ delta.toNat := by
  -- Name the end boxes, so that the run reduces to equations of boxes.
  generalize hr : pureState x = r at h
  generalize hs : pureState w' = s' at h
  unfold EthCLSpecs.Heze.increaseBalance sszGetIdx checkedAdd at h
  simp only [SizzLean.Proofs.view_uncachedBox] at h
  revert h
  cases hb : st.balances.val[i.toNat]? with
  | none =>
    intro h
    simp [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept] at h
    cases h
  | some b =>
    intro h
    by_cases hc : b + delta < b
    · simp [hc, EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept, throwArithmetic] at h
      cases h
    · simp [hc, EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨EthCLLib.Proofs.pureState_inj hs, b + delta, EthCLLib.Proofs.pureState_inj hr, ?_⟩
      unfold balN
      rw [hb]
      simp only [Option.getD_some]
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hc
      have := UInt64.toNat_lt delta
      have := UInt64.toNat_lt b
      unfold absDiff
      rw [UInt64.toNat_add]
      omega

/-- A successful `decreaseBalance` on a plain state keeps the threaded state and returns the
plain state with one balance lowered by at most `delta`. -/
theorem decreaseBalance_run_ok (st w : BeaconState) (i : ValidatorIndex) (delta : Gwei)
    {x w' : BeaconState}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState st) i delta).run
      (pureState w) = .ok (pureState x, pureState w')) :
    w' = w ∧ ∃ g : Gwei, x = { st with balances := st.balances.set! i.toNat g } ∧
      absDiff g.toNat (balN st i.toNat) ≤ delta.toNat := by
  generalize hr : pureState x = r at h
  generalize hs : pureState w' = s' at h
  unfold EthCLSpecs.Heze.decreaseBalance sszGetIdx at h
  simp only [SizzLean.Proofs.view_uncachedBox] at h
  revert h
  cases hb : st.balances.val[i.toNat]? with
  | none =>
    intro h
    simp [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept] at h
    cases h
  | some b =>
    intro h
    simp [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨EthCLLib.Proofs.pureState_inj hs, if delta > b then 0 else b - delta,
      EthCLLib.Proofs.pureState_inj hr, ?_⟩
    unfold balN
    rw [hb]
    simp only [Option.getD_some]
    unfold absDiff
    split
    · rename_i hc
      rw [GT.gt, UInt64.lt_iff_toNat_lt] at hc
      simp only [UInt64.toNat_zero]
      omega
    · rename_i hc
      rw [GT.gt, UInt64.lt_iff_toNat_lt] at hc
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
      omega

/-- `increaseBalance` moves `moveN` by at most `delta`. -/
theorem moveN_increaseBalance (vals : List ValidatorIndex) (hnd : vals.Nodup) (st₀ : BeaconState)
    (E : Nat) (st w : BeaconState) (i : ValidatorIndex) (delta : Gwei) {x w' : BeaconState}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState st) i delta).run
      (pureState w) = .ok (pureState x, pureState w')) :
    w' = w ∧ moveN vals st₀ E st x ≤ delta.toNat ∧ x = { st with balances := x.balances } ∧
      x.balances.val.size = st.balances.val.size := by
  obtain ⟨hs, y, rfl, hy⟩ := increaseBalance_run_ok st w i delta h
  exact ⟨hs, Nat.le_trans (moveN_balance_le vals hnd st₀ E st _ y) hy, rfl,
    SizzLean.Proofs.sszListSet!_size _ _ _⟩

/-- `decreaseBalance` moves `moveN` by at most `delta`. -/
theorem moveN_decreaseBalance (vals : List ValidatorIndex) (hnd : vals.Nodup) (st₀ : BeaconState)
    (E : Nat) (st w : BeaconState) (i : ValidatorIndex) (delta : Gwei) {x w' : BeaconState}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState st) i delta).run
      (pureState w) = .ok (pureState x, pureState w')) :
    w' = w ∧ moveN vals st₀ E st x ≤ delta.toNat ∧ x = { st with balances := x.balances } ∧
      x.balances.val.size = st.balances.val.size := by
  obtain ⟨hs, y, rfl, hy⟩ := decreaseBalance_run_ok st w i delta h
  exact ⟨hs, Nat.le_trans (moveN_balance_le vals hnd st₀ E st _ y) hy, rfl,
    SizzLean.Proofs.sszListSet!_size _ _ _⟩

end

end EthCLSpecs.Proofs.Heze
