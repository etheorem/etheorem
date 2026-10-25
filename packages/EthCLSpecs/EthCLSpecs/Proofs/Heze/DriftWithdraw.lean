import EthCLSpecs.Proofs.Heze.DriftParent

/-!
# `EthCLSpecs.Proofs.Heze.DriftWithdraw`: the move of the withdrawals of a block

`process_withdrawals` computes a list of withdrawals and applies it in order. A withdrawal of
a builder writes a builder balance. A withdrawal of a validator lowers its balance by the
amount. The move of the capped balances over a list is the sum of the moves of its steps
(`applyLoop_move`), and each step falls in one of four cases (`WCond`):

- A builder withdrawal moves no capped balance.
- A withdrawal whose amount is at most its cost `c w` moves at most `c w`.
- A withdrawal of an index that `moveN` does not count moves nothing that `moveN` reads.
- A sweep partial withdrawal takes the balance down to the cap, and leaves the capped balance
  at the cap.

The fourth case reads the withdrawals before the step (`wsum`): the amount plus the cap plus
the earlier amounts of the index stay within the balance at the start. The balance during
the run stays at least the balance at the start minus the earlier amounts (`LB`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei Withdrawal)

section
variable [Preset] [HasherTag]

/-- The amounts of the withdrawals of `P` for index `i`. -/
def wsum (P : List Withdrawal) (i : Nat) : Nat :=
  ((P.filter fun w => decide (w.validatorIndex.toNat = i)).map fun w => w.amount.toNat).sum

omit [HasherTag] in
theorem wsum_append (P Q : List Withdrawal) (i : Nat) : wsum (P ++ Q) i = wsum P i + wsum Q i := by
  unfold wsum
  rw [List.filter_append, List.map_append, List.sum_append]

omit [HasherTag] in
theorem wsum_single (w : Withdrawal) (i : Nat) :
    wsum [w] i = if w.validatorIndex.toNat = i then w.amount.toNat else 0 := by
  unfold wsum
  by_cases h : w.validatorIndex.toNat = i <;> simp [h]

/-- `moveN` counts index `i`: `vals` holds it and it is live. -/
def countedB (vals : List ValidatorIndex) (st₀ : BeaconState) (E i : Nat) : Bool :=
  vals.any fun j => decide (j.toNat = i) && liveB st₀ E i

/-- The reads of an accumulator of the withdrawals: the reads of `a` but the balances. -/
def AccW (a t : BeaconState) : Prop :=
  econView t = econView { a with balances := t.balances } ∧ t.slot = a.slot ∧
    t.balances.val.size = a.balances.val.size

/-- The balance during the run stays at least the balance at the start minus the earlier
amounts. -/
def LB (a t : BeaconState) (P : List Withdrawal) : Prop :=
  ∀ i, balN a i ≤ balN t i + wsum P i

/-- The four cases of one step, with the earlier withdrawals `P` and the cost `cw`. -/
def WCond (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat) (a : BeaconState)
    (P : List Withdrawal) (w : Withdrawal) (cw : Nat) : Prop :=
  EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true ∨ w.amount.toNat ≤ cw ∨
    countedB vals st₀ E w.validatorIndex.toNat = false ∨
    maxN a w.validatorIndex.toNat + w.amount.toNat + wsum P w.validatorIndex.toNat ≤
      balN a w.validatorIndex.toNat

omit [HasherTag] in
/-- `moveN` reads the capped balances alone. -/
theorem moveN_eq_zero_of_cap (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat)
    {t t' : BeaconState} (h : ∀ i, capN t' i = capN t i) : moveN vals st₀ E t t' = 0 := by
  unfold moveN
  induction (vals.filter fun i => liveB st₀ E i.toNat) with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.sum_cons, h, absDiff_self, ih]

omit [Preset] [HasherTag] in
/-- A sum of zeros is zero. -/
theorem sum_zero_of : ∀ l : List Nat, (∀ n ∈ l, n = 0) → l.sum = 0
  | [], _ => rfl
  | x :: l, h => by
    rw [List.sum_cons, h x List.mem_cons_self, sum_zero_of l fun n hn => h n (List.mem_cons_of_mem _ hn)]

omit [HasherTag] in
/-- A write of one balance at an index that `moveN` does not count moves nothing. -/
theorem moveN_set_uncounted (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat)
    (t : BeaconState) (j : Nat) (x : Gwei) (hc : countedB vals st₀ E j = false) :
    moveN vals st₀ E t { t with balances := t.balances.set! j x } = 0 := by
  unfold moveN
  refine sum_zero_of _ fun n hn => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
  obtain ⟨hiv, hil⟩ := List.mem_filter.mp hi
  have hij : i.toNat ≠ j := fun hij => by
    have : countedB vals st₀ E j = true := by
      unfold countedB
      rw [List.any_eq_true]
      exact ⟨i, hiv, by rw [← hij]; simp [hil]⟩
    rw [this] at hc; cases hc
  have : capN { t with balances := t.balances.set! j x } i.toNat = capN t i.toNat := by
    unfold capN balN maxN
    show min ((t.balances.val.setIfInBounds j x)[i.toNat]?.getD 0).toNat _ = _
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hij)]
  rw [this, absDiff_self]

omit [HasherTag] in
/-- The balance of index `j` after a write of `x` there, inside the list. -/
theorem balN_set_self (t : BeaconState) (j : Nat) (x : Gwei) (hj : j < t.balances.val.size) :
    balN { t with balances := t.balances.set! j x } j = x.toNat := by
  unfold balN
  show ((t.balances.val.setIfInBounds j x)[j]?.getD 0).toNat = _
  rw [Array.getElem?_setIfInBounds_self, if_pos hj]
  rfl

omit [HasherTag] in
theorem balN_set_ne (t : BeaconState) (j k : Nat) (x : Gwei) (hk : k ≠ j) :
    balN { t with balances := t.balances.set! j x } k = balN t k := by
  unfold balN
  show ((t.balances.val.setIfInBounds j x)[k]?.getD 0).toNat = _
  rw [Array.getElem?_setIfInBounds_ne (Ne.symm hk)]

/-- **The move of a list of withdrawals is at most the sum of the costs of its steps.** The
body `f` of the loop keeps the uncached box, takes the uncached box of a value to the uncached
box of a value, and writes a builder or lowers one balance by the amount. -/
theorem applyLoop_move (vals : List ValidatorIndex) (hnd : vals.Nodup) (st₀ : BeaconState) (E : Nat)
    (a : BeaconState) (f : Withdrawal → State → HezeRun (ForInStep State))
    (hk : ∀ w t, KeepsUncached (f w (pureState t)))
    (hf : ∀ w t u r u', (f w (pureState t)).run (pureState u) = .ok (r, pureState u') →
      ∃ t', r = .yield (pureState t') ∧
      ((EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true ∧ t'.balances = t.balances ∧
          t'.validators = t.validators ∧ econView t' = econView t ∧ t'.slot = t.slot) ∨
        (EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = false ∧ ∃ x : Gwei,
          t' = { t with balances := t.balances.set! w.validatorIndex.toNat x } ∧
          x.toNat = balN t w.validatorIndex.toNat - w.amount.toNat ∧
          w.validatorIndex.toNat < t.balances.val.size)))
    (c : Nat → Nat) :
    ∀ (L P : List Withdrawal) (k₀ : Nat) (t u t'' u' : BeaconState), AccW a t → LB a t P →
      (∀ k (hk : k < L.length), WCond vals st₀ E a (P ++ L.take k) L[k] (c (k₀ + k))) →
      (forIn L (pureState t) f).run (pureState u) = .ok (pureState t'', pureState u') →
      AccW a t'' ∧ LB a t'' (P ++ L) ∧
        moveN vals st₀ E a t'' ≤ moveN vals st₀ E a t +
          ((List.range L.length).map fun k => c (k₀ + k)).sum := by
  intro L
  induction L with
  | nil =>
    intro P k₀ t u t'' u' hA hL _ h
    rw [List.forIn_nil] at h
    have := EthCLLib.Proofs.pureState_inj (EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h)
    subst this
    exact ⟨hA, by simpa using hL, by simp⟩
  | cons w rest ih =>
    intro P k₀ t u t'' u' hA hL hC h
    rw [List.forIn_cons] at h
    obtain ⟨step, u1, h1, h2⟩ := run_bind_eq_ok_pure (hk w t) h
    obtain ⟨t1, rfl, hcase⟩ := hf w t u step u1 h1
    have hC0 := hC 0 (by simp)
    simp only [List.take_zero, List.append_nil, List.getElem_cons_zero, Nat.add_zero] at hC0
    -- The step: the reads stay, the lower bound moves one withdrawal on, and the move.
    have hstep : AccW a t1 ∧ LB a t1 (P ++ [w]) ∧ moveN vals st₀ E t t1 ≤ c k₀ := by
      obtain ⟨he, hsl, hsz⟩ := hA
      rcases hcase with ⟨hb, hbal, hval, hecon, hslot⟩ | ⟨hb, x, rfl, hx, hj⟩
      · refine ⟨⟨?_, by rw [hslot, hsl], by rw [hbal, hsz]⟩, fun i => ?_, ?_⟩
        · rw [hecon, he, hbal]
        · rw [wsum_append]
          have := hL i
          unfold balN at this ⊢
          rw [hbal]
          omega
        · rw [moveN_eq_zero_of_cap vals st₀ E fun i => by unfold capN balN maxN; rw [hbal, hval]]
          exact Nat.zero_le _
      · have hecon : econView { t with balances := t.balances.set! w.validatorIndex.toNat x } =
            econView { a with balances := (t.balances.set! w.validatorIndex.toNat x) } := by
          simp only [econView, Prod.mk.injEq, true_and] at he ⊢
          exact he
        refine ⟨⟨hecon, hsl, by
          show (t.balances.set! _ x).val.size = _
          exact (SizzLean.Proofs.sszListSet!_size _ _ _).trans hsz⟩, fun i => ?_, ?_⟩
        · rw [wsum_append, wsum_single]
          have := hL i
          by_cases hi : i = w.validatorIndex.toNat
          · subst hi
            rw [balN_set_self _ _ _ hj, hx, if_pos rfl]
            omega
          · rw [balN_set_ne _ _ _ _ hi, if_neg (Ne.symm hi)]
            omega
        · rcases hC0 with hb' | hle | hunc | hsw
          · rw [hb] at hb'; cases hb'
          · exact Nat.le_trans (moveN_balance_le vals hnd st₀ E t _ x)
              (by unfold absDiff; rw [hx]; omega)
          · rw [moveN_set_uncounted vals st₀ E t _ x hunc]; exact Nat.zero_le _
          · -- A sweep partial: the capped balance stays at the cap.
            have hv : t.validators = a.validators := by
              simp only [econView, Prod.mk.injEq] at he; exact he.1
            have hmx : maxN t w.validatorIndex.toNat = maxN a w.validatorIndex.toNat := by
              unfold maxN; rw [hv]
            have hlb := hL w.validatorIndex.toNat
            rw [moveN_eq_zero_of_cap vals st₀ E fun i => ?_]
            · exact Nat.zero_le _
            unfold capN
            by_cases hi : i = w.validatorIndex.toNat
            · subst hi
              rw [balN_set_self _ _ _ hj, hx]
              show min _ (maxN t _) = min _ (maxN t _)
              rw [hmx]
              omega
            · rw [balN_set_ne _ _ _ _ hi]
              rfl
    obtain ⟨hA1, hL1, hm1⟩ := hstep
    have hC' : ∀ k (hk : k < rest.length), WCond vals st₀ E a ((P ++ [w]) ++ rest.take k)
        rest[k] (c (k₀ + 1 + k)) := by
      intro k hk
      have := hC (k + 1) (by simp; omega)
      rw [show k₀ + (k + 1) = k₀ + 1 + k by omega] at this
      simpa [List.take_succ_cons, List.append_assoc] using this
    obtain ⟨hA', hL', hm'⟩ := ih (P ++ [w]) (k₀ + 1) t1 u1 t'' u' hA1 hL1 hC' h2
    refine ⟨hA', by simpa [List.append_assoc] using hL', ?_⟩
    have := moveN_triangle vals st₀ E a t t1
    have hsum : ((List.range (rest.length + 1)).map fun k => c (k₀ + k)).sum =
        c k₀ + ((List.range rest.length).map fun k => c (k₀ + 1 + k)).sum := by
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      congr 2
      refine List.map_congr_left fun k _ => ?_
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      omega
    rw [List.length_cons, hsum]
    omega

end

/-! ## Builder indices -/

/-- The builder flag is bit 40. -/
theorem builderFlag_toNat : EthCLSpecs.Heze.Const.builderIndexFlag.toNat = 2 ^ 40 := rfl

/-- A builder index converted to a validator index carries the builder flag. -/
theorem isBuilder_convert (b : UInt64) :
    EthCLSpecs.Heze.isBuilderIndex (EthCLSpecs.Heze.convertBuilderIndexToValidatorIndex b) = true := by
  unfold EthCLSpecs.Heze.isBuilderIndex EthCLSpecs.Heze.convertBuilderIndexToValidatorIndex
  simp only [bne_iff_ne, ne_eq]
  intro h
  have := congrArg (fun x : UInt64 => x.toNat.testBit 40) h
  simp only [UInt64.toNat_and, UInt64.toNat_or, Nat.testBit_and, Nat.testBit_or, builderFlag_toNat,
    Nat.testBit_two_pow_self, Bool.or_true, Bool.and_true, UInt64.toNat_zero, Nat.zero_testBit] at this
  cases this

/-- An index below `2 ^ 40` carries no builder flag. -/
theorem not_builder_of_lt (x : UInt64) (h : x.toNat < 2 ^ 40) :
    EthCLSpecs.Heze.isBuilderIndex x = false := by
  unfold EthCLSpecs.Heze.isBuilderIndex
  have : x &&& EthCLSpecs.Heze.Const.builderIndexFlag = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, builderFlag_toNat, UInt64.toNat_zero]
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : i = 40
    · subst hi; rw [Nat.testBit_lt_two_pow h]; rfl
    · simp [Ne.symm hi]
  rw [this]
  rfl

/-! ## The balance after the earlier withdrawals -/

section
variable [Preset] [HasherTag]

/-- The fold of `get_balance_after_withdrawals` sums the amounts of the index. -/
theorem wFold_run (vi : ValidatorIndex) (d : String) :
    ∀ (l : List Withdrawal) (acc : Gwei) (u u' : BeaconState) (r : Gwei),
      (l.foldlM (fun acc w => if w.validatorIndex == vi then checkedAdd acc w.amount d
        else pure acc) acc : HezeRun Gwei).run (pureState u) = .ok (r, pureState u') →
      u' = u ∧ r.toNat = acc.toNat + wsum l vi.toNat
  | [], acc, u, u', r, h => by
    rw [List.foldlM_nil] at h
    have e := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h)
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
    subst this e
    exact ⟨rfl, by simp [wsum]⟩
  | w :: l, acc, u, u', r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, s1, h1, h2⟩ := run_bind_eq_ok_pure (by frame_keeps) h
    obtain ⟨e2, hr⟩ := wFold_run vi d l acc1 s1 u' r h2
    have hw : wsum (w :: l) vi.toNat = wsum [w] vi.toNat + wsum l vi.toNat := by
      rw [show w :: l = [w] ++ l from rfl, wsum_append]
    rw [hw, wsum_single]
    split at h1
    · rename_i hv
      obtain ⟨e1, rfl, hno⟩ := checkedAdd_run_ok h1
      refine ⟨e2.trans (EthCLLib.Proofs.pureState_inj e1), ?_⟩
      rw [hr, if_pos (by rw [beq_iff_eq.mp hv]), UInt64.toNat_add, Nat.mod_eq_of_lt hno]
      omega
    · rename_i hv
      have e1 := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h1)
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h1
      subst this
      refine ⟨e2.trans e1, ?_⟩
      rw [hr, if_neg (fun he => hv (beq_iff_eq.mpr (UInt64.toNat_inj.mp he)))]
      omega

/-- **`get_balance_after_withdrawals` is the balance minus the earlier amounts of the index**,
with no wrap. -/
theorem balanceAfterWithdrawals_run (t : BeaconState) (vi : ValidatorIndex) (ws : Array Withdrawal)
    {u u' : BeaconState} {bal : Gwei}
    (h : (EthCLSpecs.Heze.balanceAfterWithdrawals (pureState t) vi ws : HezeRun Gwei).run
      (pureState u) = .ok (bal, pureState u')) :
    u' = u ∧ bal.toNat + wsum ws.toList vi.toNat = balN t vi.toNat ∧
      vi.toNat < t.balances.val.size := by
  unfold EthCLSpecs.Heze.balanceAfterWithdrawals at h
  -- The sum is an `Array.foldlM`, which runs as the `List.foldlM` of its `toList`.
  obtain ⟨wd, s1, h1, h⟩ := run_bind_eq_ok_pure (by
    rw [← Array.foldlM_toList]
    exact EthCLLib.Proofs.keepsUncached_foldlM_list _ (fun _ _ => by keeps_uncached) _ _) h
  rw [← Array.foldlM_toList] at h1
  obtain ⟨e1, hwd⟩ := wFold_run vi _ ws.toList 0 u s1 wd h1
  rw [UInt64.toNat_zero, Nat.zero_add] at hwd
  obtain ⟨b0, s2, h2, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨hb0, e2⟩ := sszGetIdx_run_ok h2
  simp only [SizzLean.Proofs.view_uncachedBox] at hb0
  unfold checkedSub throwArithmetic at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hle, h⟩
  · cases h
  have e3 := EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h)
  have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst this
  refine ⟨e3.trans ((EthCLLib.Proofs.pureState_inj e2).trans e1), ?_,
    (Array.getElem?_eq_some_iff.mp hb0).1⟩
  have hle' : wd.toNat ≤ b0.toNat := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt] at hle; omega
  have hb : balN t vi.toNat = b0.toNat := by unfold balN; rw [hb0]; rfl
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hle'), hb, ← hwd]
  omega

omit [Preset] [HasherTag] in
/-- A loop over a list keeps a predicate `P k` of the count `k` of the elements it passed: a
step from `P k` that goes on passes `l[k]` and reaches `P (k + 1)`, and a step that stops keeps
`P k`. -/
theorem forIn_list_pos_inv {σ ε α β : Type} (P : Nat → β → Prop)
    (f : α → β → StateT σ (Except ε) (ForInStep β)) :
    ∀ (l : List α) (k₀ : Nat),
      (∀ k (hk : k < l.length) b s r s', P (k₀ + k) b → (f l[k] b).run s = .ok (r, s') →
        (∀ b', r = .yield b' → P (k₀ + k + 1) b') ∧ (∀ b', r = .done b' → P (k₀ + k) b')) →
      ∀ (init : β) (s s' : σ) (r : β), P k₀ init → (forIn l init f).run s = .ok (r, s') →
        ∃ k ≤ l.length, P (k₀ + k) r := by
  intro l
  induction l with
  | nil =>
    intro k₀ _ init s s' r hi h
    rw [List.forIn_nil] at h
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
    subst this
    exact ⟨0, Nat.le_refl _, by simpa using hi⟩
  | cons x rest ih =>
    intro k₀ hf init s s' r hi h
    rw [List.forIn_cons] at h
    obtain ⟨st, s1, h1, h2⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨hy, hd⟩ := hf 0 (by simp) init s st s1 (by simpa using hi) h1
    cases st with
    | done b =>
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h2
      subst this
      exact ⟨0, Nat.zero_le _, by simpa using hd _ rfl⟩
    | yield b =>
      have hb := hy b rfl
      obtain ⟨k, hk, hP⟩ := ih (k₀ + 1) (fun k hk b s r s' hp hr => by
        have e1 : k₀ + 1 + k = k₀ + (k + 1) := by omega
        have := hf (k + 1) (by simp; omega) b s r s' (by rw [← e1]; exact hp) (by simpa using hr)
        rw [← e1] at this
        exact this) b s1 s' r (by simpa using hb) h2
      refine ⟨k + 1, by simp; omega, ?_⟩
      rw [show k₀ + (k + 1) = k₀ + 1 + k by omega]
      exact hP

/-- A withdrawal of the validator sweep, with the earlier withdrawals `P`: a validator of the
registry, withdrawable by the current epoch, or a partial withdrawal down to its cap. -/
def SweepOK (t : BeaconState) (P : List Withdrawal) (w : Withdrawal) : Prop :=
  w.validatorIndex.toNat < t.validators.val.size ∧
    ((∃ v, t.validators.val[w.validatorIndex.toNat]? = some v ∧
        v.withdrawableEpoch.toNat ≤ epochN t) ∨
      maxN t w.validatorIndex.toNat + w.amount.toNat + wsum P w.validatorIndex.toNat ≤
        balN t w.validatorIndex.toNat)

omit [Preset] [HasherTag] in
/-- A property of each entry of an array with its earlier entries survives a push of an entry
with the property. -/
theorem prefixProp_push {α : Type} (Q : List α → α → Prop) (ws : Array α) (w : α)
    (hws : ∀ k (hk : k < ws.size), Q (ws.toList.take k) ws[k]) (hw : Q ws.toList w) :
    ∀ k (hk : k < (ws.push w).size), Q ((ws.push w).toList.take k) (ws.push w)[k] := by
  intro k hk
  rw [Array.size_push] at hk
  by_cases hlt : k < ws.size
  · rw [Array.getElem_push_lt hlt, Array.toList_push, List.take_append_of_le_length (by simp; omega)]
    exact hws k hlt
  · have hk' : k = ws.size := by omega
    subst hk'
    rw [Array.getElem_push_eq, Array.toList_push, List.take_left' (by simp)]
    exact hw

variable [Config] [CryptoBackend] in
/-- **Each withdrawal of the validator sweep meets `SweepOK`.** -/
theorem getValidatorsSweep_ok (wi : UInt64) (prior : Array Withdrawal) (t : BeaconState)
    {s' : BeaconState} {r : Array Withdrawal × UInt64 × Nat} (h64 : t.validators.val.size < 2 ^ 64)
    (h : (EthCLSpecs.Heze.getValidatorsSweepWithdrawals (StateTransition := HezeRun) wi prior).run
      (pureState t) = .ok (r, pureState s')) :
    ∀ k (hk : k < r.1.size), SweepOK t (prior.toList ++ r.1.toList.take k) r.1[k] := by
  unfold EthCLSpecs.Heze.getValidatorsSweepWithdrawals at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨acc, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hr := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst hr
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
  let Q : MProd Nat (MProd Nat (MProd UInt64 (Array Withdrawal))) → Prop := fun acc =>
    ∀ k (hk : k < acc.2.2.2.size), SweepOK t (prior.toList ++ acc.2.2.2.toList.take k) acc.2.2.2[k]
  -- The invariant also names the threaded state as a plain state: the balance read needs it.
  refine (EthCLLib.Proofs.forIn_run_inv_state (fun r s => Q r ∧ ∃ u, s = pureState u) ?_
    ⟨fun k hk => absurd hk (by simp), t, rfl⟩ h1).1
  intro x _ rr s st s2 ⟨hq, u, hu⟩ hb
  subst hu
  rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
  · have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    have e := run_pure_state_eq _ _ _ _ hb
    subst this e
    exact ⟨hq, u, rfl⟩
  obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
  obtain ⟨v, s3, hv, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
  obtain ⟨hv', -⟩ := sszGetIdx_run_ok hv
  simp only [SizzLean.Proofs.view_uncachedBox] at hv'
  obtain ⟨bal, s4, hbal, hb⟩ :=
    run_bind_eq_ok_pure (keepsUncached_balanceAfterWithdrawals _ _ _) hb
  obtain ⟨-, hbalN, -⟩ := balanceAfterWithdrawals_run t _ _ hbal
  have hvi : rr.2.1 < t.validators.val.size := (Array.getElem?_eq_some_iff.mp hv').1
  have hvi64 : (UInt64.ofNat rr.2.1).toNat = rr.2.1 := EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)
  rw [hvi64, Array.toList_append] at hbalN
  -- The push of one withdrawal at the index `rr.2.1`.
  have hpush : ∀ (w : Withdrawal), w.validatorIndex = UInt64.ofNat rr.2.1 →
      ((∃ v, t.validators.val[rr.2.1]? = some v ∧ v.withdrawableEpoch.toNat ≤ epochN t) ∨
        maxN t rr.2.1 + w.amount.toNat + wsum (prior.toList ++ rr.2.2.2.toList) rr.2.1 ≤
          balN t rr.2.1) →
      Q ⟨rr.1 + 1, modWrap (rr.2.1 + 1) t.validators.val.size, rr.2.2.1 + 1, rr.2.2.2.push w⟩ := by
    intro w hwv hw
    refine prefixProp_push (fun P w => SweepOK t (prior.toList ++ P) w) _ w hq ?_
    show SweepOK t (prior.toList ++ rr.2.2.2.toList) w
    unfold SweepOK
    rw [hwv, hvi64]
    exact ⟨hvi, hw⟩
  rcases run_ite_eq_ok hb with ⟨hfull, hb⟩ | ⟨-, hb⟩
  · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
    obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    have e := run_pure_state_eq _ _ _ _ hb
    subst this e
    refine ⟨hpush _ rfl (.inl ⟨v, hv', ?_⟩), _, rfl⟩
    unfold EthCLSpecs.Heze.isFullyWithdrawable at hfull
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfull
    exact UInt64.le_iff_toNat_le.mp hfull.1.2
  rcases run_ite_eq_ok hb with ⟨hpart, hb⟩ | ⟨-, hb⟩
  · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
    obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    have e := run_pure_state_eq _ _ _ _ hb
    subst this e
    refine ⟨hpush _ rfl (.inr ?_), _, rfl⟩
    unfold EthCLSpecs.Heze.isPartiallyWithdrawable at hpart
    simp only [Bool.and_eq_true, decide_eq_true_eq, GT.gt] at hpart
    have hlt := UInt64.lt_iff_toNat_lt.mp hpart.2
    have hmx : maxN t rr.2.1 = (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat := by
      unfold maxN; rw [hv']
    show maxN t rr.2.1 + (bal - EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat + _ ≤ _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hpart.2), hmx]
    omega
  · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
    obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok_pure (by frame_keeps) hb
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    have e := run_pure_state_eq _ _ _ _ hb
    subst this e
    exact ⟨hq, _, rfl⟩

/-- The amounts of a list of withdrawals. -/
def amtSum (l : List Withdrawal) : Nat := (l.map fun w => w.amount.toNat).sum

/-- The amounts of a list of queued partial withdrawals. -/
def pamtSum (l : List EthCLSpecs.Heze.PendingPartialWithdrawal) : Nat :=
  (l.map fun w => w.amount.toNat).sum

/-- **The pending-partial phase**: its withdrawals have indices of the registry, and their
amounts add up to at most the amounts of the queue entries that it passed. Each passed entry
is withdrawable by the current epoch. -/
theorem getPendingPartial_ok (wi : UInt64) (prior : Array Withdrawal) (t : BeaconState)
    {s' : BeaconState} {r : Array Withdrawal × UInt64 × Nat}
    (h : (EthCLSpecs.Heze.getPendingPartialWithdrawals (StateTransition := HezeRun) wi prior).run
      (pureState t) = .ok (r, pureState s')) :
    amtSum r.1.toList ≤ pamtSum (t.pendingPartialWithdrawals.val.toList.take r.2.2) ∧
    (∀ e ∈ t.pendingPartialWithdrawals.val.toList.take r.2.2,
      e.withdrawableEpoch.toNat ≤ epochN t) ∧
    (∀ w ∈ r.1.toList, w.validatorIndex.toNat < t.validators.val.size) := by
  unfold EthCLSpecs.Heze.getPendingPartialWithdrawals at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨acc, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hr := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst hr
  generalize hl : t.pendingPartialWithdrawals.val.toList = l
  let P : Nat → MProd Nat (MProd UInt64 (Array Withdrawal)) → Prop := fun k acc =>
    acc.1 = k ∧ amtSum acc.2.2.toList ≤ pamtSum (l.take k) ∧
      (∀ e ∈ l.take k, e.withdrawableEpoch.toNat ≤ epochN t) ∧
      (∀ w ∈ acc.2.2.toList, w.validatorIndex.toNat < t.validators.val.size)
  have key : ∃ k ≤ l.length, P (0 + k) acc := by
    refine forIn_list_pos_inv P _ l 0 ?_ _ _ _ _ ?_ (by rw [← hl, Array.forIn_toList]; exact h1)
    rotate_left
    · refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [amtSum, pamtSum]
    intro k hk b s rr s2 ⟨hb1, hb2, hb3, hb4⟩ hrun
    simp only [Nat.zero_add] at hb1 hb2 hb3 ⊢
    rcases run_ite_eq_ok hrun with ⟨-, hrun⟩ | ⟨hc, hrun⟩
    · have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
      subst this
      refine ⟨fun b' hb' => (by cases hb'), fun b' hb' => ?_⟩
      cases hb'
      exact ⟨hb1, hb2, hb3, hb4⟩
    -- The entry `l[k]` is withdrawable by the current epoch.
    have hwe : (l[k]).withdrawableEpoch.toNat ≤ epochN t := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
        not_or, Classical.not_not] at hc
      exact UInt64.le_iff_toNat_le.mp hc.1
    have htake : l.take (k + 1) = l.take k ++ [l[k]] := List.take_succ_eq_append_getElem hk
    obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
    obtain ⟨v, s3, hv, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
    obtain ⟨hv', -⟩ := sszGetIdx_run_ok hv
    simp only [SizzLean.Proofs.view_uncachedBox] at hv'
    have hvi : (l[k]).validatorIndex.toNat < t.validators.val.size :=
      (Array.getElem?_eq_some_iff.mp hv').1
    obtain ⟨bal, s4, hbal, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
    have hamt : ∀ x : Gwei, (umin x (l[k]).amount).toNat ≤ (l[k]).amount.toNat := fun x => by
      rw [umin_toNat]; omega
    have hpk : pamtSum (l.take (k + 1)) = pamtSum (l.take k) + (l[k]).amount.toNat := by
      rw [htake]; unfold pamtSum
      rw [List.map_append, List.sum_append]
      simp
    have hek : ∀ e ∈ l.take (k + 1), e.withdrawableEpoch.toNat ≤ epochN t := by
      rw [htake]; intro e he
      rcases List.mem_append.mp he with he | he
      · exact hb3 e he
      · rw [List.mem_singleton.mp he]; exact hwe
    rcases run_ite_eq_ok hrun with ⟨-, hrun⟩ | ⟨-, hrun⟩
    · obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
      subst this
      refine ⟨fun b' hb' => ?_, fun b' hb' => by cases hb'⟩
      cases hb'
      refine ⟨by rw [hb1], ?_, hek, fun w hw => ?_⟩
      · simp only [Array.toList_push, amtSum, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil] at hb2 ⊢
        rw [hpk]
        have := hamt (bal - EthCLSpecs.Heze.Const.minActivationBalance)
        omega
      · rw [Array.toList_push] at hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hb4 w hw
        · rw [List.mem_singleton.mp hw]; exact hvi
    · obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
      have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
      subst this
      refine ⟨fun b' hb' => ?_, fun b' hb' => by cases hb'⟩
      cases hb'
      exact ⟨by rw [hb1], by show amtSum b.2.2.toList ≤ _; rw [hpk]; omega, hek, hb4⟩
  obtain ⟨k, -, hk1, hk2, hk3, hk4⟩ := key
  simp only [Nat.zero_add] at hk1 hk2 hk3
  show amtSum acc.2.2.toList ≤ _ ∧ _ ∧ _
  rw [hk1]
  exact ⟨hk2, hk3, hk4⟩

/-- A successful `decreaseBalance` on a plain state lowers one balance of the list, flooring at
zero. -/
theorem decreaseBalance_exact (st w : BeaconState) (i : ValidatorIndex) (delta : Gwei)
    {r w' : BeaconState}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState st) i delta).run
      (pureState w) = .ok (pureState r, pureState w')) :
    w' = w ∧ ∃ x : Gwei, r = { st with balances := st.balances.set! i.toNat x } ∧
      x.toNat = balN st i.toNat - delta.toNat ∧ i.toNat < st.balances.val.size := by
  -- Name the end boxes, so that the run reduces to equations of boxes.
  generalize hr : pureState r = R at h
  generalize hs : pureState w' = S at h
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
      EthCLLib.Proofs.pureState_inj hr, ?_, (Array.getElem?_eq_some_iff.mp hb).1⟩
    unfold balN
    rw [hb]
    simp only [Option.getD_some]
    split
    · rename_i hc
      rw [GT.gt, UInt64.lt_iff_toNat_lt] at hc
      simp only [UInt64.toNat_zero]
      omega
    · rename_i hc
      rw [GT.gt, UInt64.lt_iff_toNat_lt] at hc
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]

/-- The withdrawals of the builder queue are builder withdrawals. -/
theorem getBuilderWithdrawals_builder (wi : UInt64) (prior : Array Withdrawal) (t : BeaconState)
    {s' : BeaconState} {r : Array Withdrawal × UInt64 × Nat}
    (h : (EthCLSpecs.Heze.getBuilderWithdrawals (StateTransition := HezeRun) wi prior).run
      (pureState t) = .ok (r, pureState s')) :
    ∀ w ∈ r.1.toList, EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true := by
  unfold EthCLSpecs.Heze.getBuilderWithdrawals at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨acc, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hr := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst hr
  refine EthCLLib.Proofs.forIn_run_inv
    (fun acc : MProd Nat (MProd UInt64 (Array Withdrawal)) =>
      ∀ w ∈ acc.2.2.toList, EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true) _
    t.builderPendingWithdrawals.val.toList ?_ _ _ _ _ ?_
    (by rw [Array.forIn_toList]; exact h1)
  rotate_left
  · intro w hw; simp at hw
  intro x _ rr s s2 st hq hb
  rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
  · have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    subst this
    exact hq
  obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
  obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
  have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
  subst this
  intro w hw
  simp [Array.toList_push] at hw
  rcases hw with hw | rfl
  · exact hq w (Array.mem_toList_iff.mpr hw)
  · exact isBuilder_convert _

/-- The withdrawals of the builder sweep are builder withdrawals. -/
theorem getBuildersSweep_builder (wi : UInt64) (prior : Array Withdrawal) (t : BeaconState)
    {s' : BeaconState} {r : Array Withdrawal × UInt64 × Nat}
    (h : (EthCLSpecs.Heze.getBuildersSweepWithdrawals (StateTransition := HezeRun) wi prior).run
      (pureState t) = .ok (r, pureState s')) :
    ∀ w ∈ r.1.toList, EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true := by
  unfold EthCLSpecs.Heze.getBuildersSweepWithdrawals at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨acc, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hr := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst hr
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
  refine EthCLLib.Proofs.forIn_run_inv
    (fun acc : MProd Nat (MProd Nat (MProd UInt64 (Array Withdrawal))) =>
      ∀ w ∈ acc.2.2.2.toList, EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true) _ _ ?_
    _ _ _ _ (by simp) h1
  intro x _ rr s s2 st hq hb
  rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
  · have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    subst this
    exact hq
  obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
  obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
  rcases run_ite_eq_ok hb with ⟨-, hb⟩ | ⟨-, hb⟩
  · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
    obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    subst this
    intro w hw
    simp [Array.toList_push] at hw
    rcases hw with hw | rfl
    · exact hq w (Array.mem_toList_iff.mpr hw)
    · exact isBuilder_convert _
  · obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
    obtain ⟨_, _, -, hb⟩ := run_bind_eq_ok _ _ _ _ hb
    have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hb
    subst this
    exact hq

variable [Config] [CryptoBackend] in
/-- **The withdrawals of a block**: the builder queue, the pending partials, the builder sweep,
and the validator sweep, in that order, from a state that the computation keeps. -/
theorem getExpected_ok (t : BeaconState) {s' : BeaconState}
    {r : Array Withdrawal × Nat × Nat × Nat}
    (h64 : t.validators.val.size < 2 ^ 64)
    (h : (EthCLSpecs.Heze.getExpectedWithdrawals (StateTransition := HezeRun)).run
      (pureState t) = .ok (r, pureState s')) :
    s' = t ∧ ∃ Lb Lp Lbs Lv : List Withdrawal, r.1.toList = Lb ++ Lp ++ Lbs ++ Lv ∧
      (∀ w ∈ Lb ++ Lbs, EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true) ∧
      amtSum Lp ≤ pamtSum (t.pendingPartialWithdrawals.val.toList.take r.2.2.1) ∧
      (∀ e ∈ t.pendingPartialWithdrawals.val.toList.take r.2.2.1,
        e.withdrawableEpoch.toNat ≤ epochN t) ∧
      (∀ w ∈ Lp, w.validatorIndex.toNat < t.validators.val.size) ∧
      (∀ k (hk : k < Lv.length), SweepOK t ((Lb ++ Lp ++ Lbs) ++ Lv.take k) Lv[k]) := by
  unfold EthCLSpecs.Heze.getExpectedWithdrawals at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  -- Each of the four reads keeps the state.
  obtain ⟨p1, h1, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  obtain ⟨p2, h2, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  obtain ⟨p3, h3, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  obtain ⟨p4, h4, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  have e5 := (EthCLLib.Proofs.pureState_inj (run_pure_state_eq _ _ _ _ h)).symm
  have hr := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst hr e5
  have hb := getBuilderWithdrawals_builder _ _ t h1
  obtain ⟨hp1, hp2, hp3⟩ := getPendingPartial_ok _ _ t h2
  have hbs := getBuildersSweep_builder _ _ t h3
  have hv := getValidatorsSweep_ok _ _ t h64 h4
  refine ⟨rfl, p1.1.toList, p2.1.toList, p3.1.toList, p4.1.toList, ?_, ?_, hp1, hp2, hp3, ?_⟩
  · simp [Array.toList_append, List.append_assoc]
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hb w hw
    · exact hbs w hw
  · intro k hk
    have := hv k (by simpa using hk)
    simpa [Array.toList_append, List.append_assoc] using this

omit [Preset] [HasherTag] in
/-- A sum over the positions of a list of its entries is the sum of the list. -/
theorem sum_range_getD : ∀ l : List Nat,
    ((List.range l.length).map fun k => l[k]?.getD 0).sum = l.sum
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
      List.sum_cons]
    have := sum_range_getD l
    have hm : (List.map ((fun k => (x :: l)[k]?.getD 0) ∘ Nat.succ) (List.range l.length)) =
        List.map (fun k => l[k]?.getD 0) (List.range l.length) :=
      List.map_congr_left fun k _ => rfl
    rw [hm, this]
    rfl

variable [Config] [CryptoBackend] in
/-- **The move of the withdrawals of a block is at most the amounts of its pending partials.**
-/
theorem applyWithdrawals_move (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (a : BeaconState) (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hE : epochN a ≤ E)
    (h40 : a.validators.val.size < 2 ^ 40) (L : Array Withdrawal) (Lb Lp Lbs Lv : List Withdrawal)
    (hL : L.toList = Lb ++ Lp ++ Lbs ++ Lv)
    (hb : ∀ w ∈ Lb ++ Lbs, EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = true)
    (hp : ∀ w ∈ Lp, w.validatorIndex.toNat < a.validators.val.size)
    (hv : ∀ k (hk : k < Lv.length), SweepOK a ((Lb ++ Lp ++ Lbs) ++ Lv.take k) Lv[k])
    {a2 : BeaconState}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) L).run
      (pureState a) = .ok ((), pureState a2)) :
    AccW a a2 ∧ moveN vals st₀ E a a2 ≤ amtSum Lp := by
  unfold EthCLSpecs.Heze.applyWithdrawals at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨r, s1, h1, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  -- The last write sets the state to the loop result, so the loop returns `pureState a2`.
  have e := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h
  subst e
  rw [← Array.forIn_toList, hL] at h1
  -- The costs: the amount of each validator withdrawal before the sweep, and zero else.
  let X := Lb ++ Lp ++ Lbs
  let cs : List Nat := X.map (fun w => if EthCLSpecs.Heze.isBuilderIndex w.validatorIndex then 0
    else w.amount.toNat) ++ Lv.map fun _ => 0
  have hcs : cs.length = (X ++ Lv).length := by simp [cs]
  have hsum : cs.sum = amtSum Lp := by
    have hpb : ∀ w ∈ Lp, EthCLSpecs.Heze.isBuilderIndex w.validatorIndex = false := fun w hw =>
      not_builder_of_lt _ (Nat.lt_trans (hp w hw) h40)
    simp only [cs, X, List.map_append, List.sum_append]
    have h1 : (Lb.map fun w => if EthCLSpecs.Heze.isBuilderIndex w.validatorIndex then 0
        else w.amount.toNat).sum = 0 :=
      sum_zero_of _ fun n hn => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
        rw [hb w (List.mem_append_left _ hw)]; rfl
    have h3 : (Lbs.map fun w => if EthCLSpecs.Heze.isBuilderIndex w.validatorIndex then 0
        else w.amount.toNat).sum = 0 :=
      sum_zero_of _ fun n hn => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
        rw [hb w (List.mem_append_right _ hw)]; rfl
    have h2 : (Lp.map fun w => if EthCLSpecs.Heze.isBuilderIndex w.validatorIndex then 0
        else w.amount.toNat) = Lp.map fun w => w.amount.toNat :=
      List.map_congr_left fun w hw => by rw [hpb w hw]; rfl
    have h4 : (Lv.map fun _ => (0 : Nat)).sum = 0 := sum_zero_of _ fun n hn => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hn; rfl
    rw [h1, h2, h3, h4]
    simp [amtSum]
  have hAcc : AccW a a := ⟨rfl, rfl, rfl⟩
  have hLB : LB a a [] := fun i => by simp [wsum]
  have key : AccW a a2 ∧ LB a a2 ([] ++ (X ++ Lv)) ∧
      moveN vals st₀ E a a2 ≤ moveN vals st₀ E a a +
        ((List.range (X ++ Lv).length).map fun k => cs[0 + k]?.getD 0).sum := by
    refine applyLoop_move vals hnd st₀ E a _ (fun _ _ => by frame_keeps) ?_
      (fun k => cs[k]?.getD 0) (X ++ Lv) [] 0 a _ a2 _ hAcc hLB ?_ h1
    · intro w t u rr u2 hrun
      rcases run_ite_eq_ok hrun with ⟨hbf, hrun⟩ | ⟨hbf, hrun⟩
      · obtain ⟨bld, s3, hbld, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
        obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
        have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
        exact ⟨_, this, .inl ⟨hbf, rfl, rfl, rfl, rfl⟩⟩
      · obtain ⟨r1, s3, hd, hrun⟩ :=
          run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) hrun
        obtain ⟨-, x, rfl, hx, hj⟩ := decreaseBalance_exact t _ _ _ hd
        obtain ⟨_, _, -, hrun⟩ := run_bind_eq_ok _ _ _ _ hrun
        have := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrun
        exact ⟨_, this, .inr ⟨by simpa using hbf, x, rfl, hx, hj⟩⟩
    intro k hk
    simp only [List.nil_append, Nat.zero_add]
    by_cases hkX : k < X.length
    · -- Before the sweep: a builder withdrawal, or a validator withdrawal at its cost.
      rw [List.getElem_append_left hkX]
      have hcsk : cs[k]?.getD 0 = if EthCLSpecs.Heze.isBuilderIndex X[k].validatorIndex then 0
          else X[k].amount.toNat := by
        simp only [cs]
        rw [List.getElem?_append_left (by simpa using hkX), List.getElem?_map,
          List.getElem?_eq_getElem hkX]
        rfl
      rw [hcsk]
      by_cases hbk : EthCLSpecs.Heze.isBuilderIndex X[k].validatorIndex = true
      · exact .inl hbk
      · rw [if_neg hbk]; exact .inr (.inl (Nat.le_refl _))
    · -- The sweep.
      have hk' : k - X.length < Lv.length := by simp at hk; omega
      rw [List.getElem_append_right (by omega)]
      obtain ⟨hvi, hcase⟩ := hv (k - X.length) hk'
      rcases hcase with ⟨v, hv', hwe⟩ | hsw
      · -- A full withdrawal: the index is not live.
        refine .inr (.inr (.inl ?_))
        unfold countedB
        rw [List.any_eq_false]
        intro j hj hjc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hjc
        obtain ⟨hjv, hjl⟩ := hjc
        have := I.live j hj (by rw [hjv]; exact hjl) (by rw [hjv]; exact hvi)
        rw [hjv] at this
        unfold wdrOf at this
        rw [hv'] at this
        simp only at this
        omega
      · refine .inr (.inr (.inr ?_))
        rw [show (X ++ Lv).take k = X ++ Lv.take (k - X.length) by
          rw [List.take_append, List.take_of_length_le (by omega)]]
        exact hsw
  obtain ⟨hA', -, hm⟩ := key
  refine ⟨hA', ?_⟩
  rw [moveN_self, Nat.zero_add] at hm
  simp only [Nat.zero_add] at hm
  rw [← hcs, sum_range_getD, hsum] at hm
  exact hm

omit [HasherTag] in
/-- The pending-partial potential of a queue whose first `n` entries are due by `E` is their
amounts plus the potential of the rest. -/
theorem gPart_drop (E : Nat) (l : List EthCLSpecs.Heze.PendingPartialWithdrawal) (n : Nat)
    (h : ∀ e ∈ l.take n, e.withdrawableEpoch.toNat ≤ E) :
    ((l.filter fun w => decide (w.withdrawableEpoch.toNat ≤ E)).map fun w => w.amount.toNat).sum =
      pamtSum (l.take n) +
        (((l.drop n).filter fun w => decide (w.withdrawableEpoch.toNat ≤ E)).map
          fun w => w.amount.toNat).sum := by
  conv => lhs; rw [← List.take_append_drop n l]
  rw [List.filter_append, List.map_append, List.sum_append,
    List.filter_eq_self.mpr (fun e he => decide_eq_true (h e he))]
  rfl

/-- **A step that lowers balances and drops due entries of the pending-partial queue keeps the
invariant**, when the move is at most the amounts of the dropped entries. -/
theorem RunInv.withdrawStep {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (n : Nat)
    (hv : b.validators = a.validators) (hbsz : b.balances.val.size = a.balances.val.size)
    (hq1 : b.pendingConsolidations = a.pendingConsolidations)
    (hq2 : b.pendingPartialWithdrawals.val.toList = a.pendingPartialWithdrawals.val.toList.drop n)
    (hd : b.depositBalanceToConsume = a.depositBalanceToConsume)
    (hx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch)
    (hdue : ∀ e ∈ a.pendingPartialWithdrawals.val.toList.take n, e.withdrawableEpoch.toNat ≤ E)
    (hm : moveN vals st₀ E a b ≤ pamtSum (a.pendingPartialWithdrawals.val.toList.take n)) :
    RunInv vals st₀ E CX CC b (stepV V a b) W tag Γp B := by
  have e2 : ∀ i, ebN b i = ebN a i := fun i => by simp [ebN, hv]
  have e3 : phi vals E b + pamtSum (a.pendingPartialWithdrawals.val.toList.take n) =
      phi vals E a := by
    have hg := gPart_drop E a.pendingPartialWithdrawals.val.toList n hdue
    unfold phi gPart gCons gSl sizeOf slashedOf maxN wdrOf
    rw [hv, hq1, hd, hq2, hg]
    omega
  have e4 : ∀ i, actOf b i = actOf a i := fun i => by simp [actOf, hv]
  have e5 : ∀ i, exitOf b i = exitOf a i := fun i => by simp [exitOf, hv]
  have e6 : ∀ i, wdrOf b i = wdrOf a i := fun i => by simp [wdrOf, hv]
  have e7 : sizeOf b = sizeOf a := by simp [sizeOf, hv]
  have e9 : ∀ i, maxN b i = maxN a i := fun i => by simp [maxN, hv]
  have e10 := exitedCount_eq e7 e5
  have e11 : ∀ i, slashedOf b i = slashedOf a i := fun i => by simp [slashedOf, hv]
  have hV : ∀ i, V i ≤ stepV V a b i := fun i => Nat.le_add_right _ _
  refine ⟨fun i hi hl => ?_, ?_, fun i hi hl => ?_, fun i h1 h2 => by rw [e4]; exact I.actOnce i h1 h2,
    fun i h1 h2 => by rw [e5]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => ?_, by rw [hx1, hx2]; exact I.churnX.of_exit_eq e5,
    by rw [hc1, hc2]; exact I.churnC.of_exit_eq e5, ?_,
    fun i hi hl hs => by rw [e6]; exact I.live i hi hl (by rw [← e7]; exact hs),
    by rw [e7]; exact I.sizeLe, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [e6]; exact I.slashInv i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)⟩
  · have := absDiff_triangle (capN b i.toNat) (capN a i.toNat) (capN st₀ i.toNat)
    have := I.cap i hi hl
    unfold stepV
    omega
  · rw [sum_stepV]
    have := I.bud
    omega
  · rw [e2]; exact (I.track i hi hl).mono (hV _)
  · exact Nat.le_trans (I.newExit i hi h1 h2 (by rw [← e5]; exact h3))
      (Nat.add_le_add_left (abound_mono (Nat.add_le_add_left (hV _) _)) _)
  · obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    constructor
    · rw [hv, hbsz]; exact s1
    · intro i hi; rw [e2, e9]; exact s2 i (by rw [← e7]; exact hi)
    · intro i hi; rw [e2]; exact s3 i (by rw [← e7]; exact hi)
    · intro i hi hx; rw [e6]; exact s4 i (by rw [← e7]; exact hi) (by rw [← e5]; exact hx)
    · intro i hi hs; rw [e5]; exact s5 i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)

/-- The fields that `WKeep` reads, and the queue of pending partials. The cursor writes at the
end of `processWithdrawals` keep this view. -/
def wView (s : State) :=
  (sszGet s validators, sszGet s balances, sszGet s slot, sszGet s pendingConsolidations,
    sszGet s depositBalanceToConsume, sszGet s exitBalanceToConsume, sszGet s earliestExitEpoch,
    sszGet s consolidationBalanceToConsume, sszGet s earliestConsolidationEpoch,
    sszGet s pendingPartialWithdrawals)

/-- The fields of the invariant that the bookkeeping writes of `process_withdrawals` keep. -/
structure WKeep (x y : BeaconState) : Prop where
  v : y.validators = x.validators
  bal : y.balances = x.balances
  sl : y.slot = x.slot
  pc : y.pendingConsolidations = x.pendingConsolidations
  dbc : y.depositBalanceToConsume = x.depositBalanceToConsume
  x1 : y.exitBalanceToConsume = x.exitBalanceToConsume
  x2 : y.earliestExitEpoch = x.earliestExitEpoch
  c1 : y.consolidationBalanceToConsume = x.consolidationBalanceToConsume
  c2 : y.earliestConsolidationEpoch = x.earliestConsolidationEpoch

omit [HasherTag] in
theorem WKeep.trans {x y z : BeaconState} (h1 : WKeep x y) (h2 : WKeep y z) : WKeep x z :=
  ⟨h2.v.trans h1.v, h2.bal.trans h1.bal, h2.sl.trans h1.sl, h2.pc.trans h1.pc, h2.dbc.trans h1.dbc,
    h2.x1.trans h1.x1, h2.x2.trans h1.x2, h2.c1.trans h1.c1, h2.c2.trans h1.c2⟩

omit [Preset] [HasherTag] in
/-- The list of an `SSZList` after a drop of its first `n` entries. -/
theorem sszDrop_toList {α : Type} {cap : Nat} (xs : SizzLean.Repr.SSZList α cap) (n : Nat) :
    (sszDrop xs n).val.toList = xs.val.toList.drop n := by
  unfold sszDrop
  simp only [Array.toList_extract, List.extract]
  exact List.take_of_length_le (by simp)

variable [Config] [CryptoBackend] in
/-- **The withdrawals of a block keep the invariant**, at no cost: the move is at most the
amounts of the pending partials that the run drops from the queue. -/
theorem RunInv.processWithdrawals (vals : List ValidatorIndex) (hnd : vals.Nodup)
    (st₀ : BeaconState) {E CX CC : Nat} {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    {a b : BeaconState} (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hE : epochN a ≤ E)
    (h40 : a.validators.val.size < 2 ^ 40)
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run
      (pureState a) = .ok ((), pureState b)) :
    AcKeep a b ∧ ∃ V', RunInv vals st₀ E CX CC b V' W tag Γp B := by
  unfold EthCLSpecs.Heze.processWithdrawals at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [pureState_inj (run_pure_state_eq _ _ _ _ h)]
    exact ⟨AcKeep.refl _, V, I⟩
  obtain ⟨⟨⟩, s0, h0, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e0 := run_pure_state_eq _ _ _ _ h0
  subst e0
  obtain ⟨⟨L, bc, pc, sc⟩, s1, h1, h⟩ := run_bind_eq_ok_pure keepsUncached_getExpectedWithdrawals h
  obtain ⟨e1, Lb, Lp, Lbs, Lv, hL, hbB, hamt, hwe, hp, hsw⟩ := getExpected_ok a (by omega) h1
  -- Eliminate `s1`. An earlier run hypothesis mentions `a`, so `a` stays.
  have e1 := e1.symm
  subst e1
  try dsimp only at h
  obtain ⟨⟨⟩, a2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_applyWithdrawals _) h
  obtain ⟨⟨he2, hsl2, hsz2⟩, hm2⟩ :=
    applyWithdrawals_move vals hnd st₀ a I hE h40 L Lb Lp Lbs Lv hL hbB hp hsw h2
  simp only [econView, Prod.mk.injEq, true_and] at he2
  obtain ⟨hv2, hpc2, hppw2, hdbc2, hx12, hx22, hc12, hc22⟩ := he2
  -- The bookkeeping writes: they keep every read but the pending-partial queue, which drops
  -- its first `pc` entries.
  -- The last two writes, the builder cursor and the validator cursor, keep `WKeep` and the
  -- queue of pending partials.
  have rest : ∀ x7 : BeaconState, wView (pureState b) = wView (pureState x7) →
      WKeep x7 b ∧ b.pendingPartialWithdrawals = x7.pendingPartialWithdrawals := by
    intro x7 he
    simp only [wView, Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := he
    exact ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩, e10⟩
  have tail : WKeep a2 b ∧ b.pendingPartialWithdrawals = sszDrop a2.pendingPartialWithdrawals pc := by
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · -- The checked index sum keeps the state.
      obtain ⟨_, s3c, h3c, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨rfl, -, -⟩ := checkedAdd_run_ok h3c
      obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨x3, rfl, k3, q3⟩ : ∃ y, s3 = pureState y ∧ WKeep a2 y ∧
          y.pendingPartialWithdrawals = a2.pendingPartialWithdrawals :=
        ⟨_, EthCLLib.Proofs.run_modifyThe_eq_ok h3, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      obtain ⟨_, -, h⟩ :=
        run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
      obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨x5, rfl, k5, q5⟩ : ∃ y, s5 = pureState y ∧ WKeep x3 y ∧
          y.pendingPartialWithdrawals = x3.pendingPartialWithdrawals :=
        ⟨_, EthCLLib.Proofs.run_modifyThe_eq_ok h5, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨x6, rfl, k6, q6⟩ : ∃ y, s6 = pureState y ∧ WKeep x5 y ∧
          y.pendingPartialWithdrawals = x5.pendingPartialWithdrawals :=
        ⟨_, EthCLLib.Proofs.run_modifyThe_eq_ok h6, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      obtain ⟨⟨⟩, s7, h7, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨x7, rfl, k7, q7⟩ : ∃ y, s7 = pureState y ∧ WKeep x6 y ∧
          y.pendingPartialWithdrawals = sszDrop x6.pendingPartialWithdrawals pc :=
        ⟨_, EthCLLib.Proofs.run_modifyThe_eq_ok h7, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      obtain ⟨k8, q8⟩ := rest x7 (by frame_invert h)
      refine ⟨k3.trans (k5.trans (k6.trans (k7.trans k8))), ?_⟩
      rw [q8, q7, q6, q5, q3]
    · obtain ⟨⟨⟩, s0, h0, h⟩ := run_bind_eq_ok _ _ _ _ h
      have e0 := run_pure_state_eq _ _ _ _ h0
      subst e0
      obtain ⟨_, -, h⟩ :=
        run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
      obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨x5, rfl, k5, q5⟩ : ∃ y, s5 = pureState y ∧ WKeep a2 y ∧
          y.pendingPartialWithdrawals = a2.pendingPartialWithdrawals :=
        ⟨_, EthCLLib.Proofs.run_modifyThe_eq_ok h5, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨x6, rfl, k6, q6⟩ : ∃ y, s6 = pureState y ∧ WKeep x5 y ∧
          y.pendingPartialWithdrawals = x5.pendingPartialWithdrawals :=
        ⟨_, EthCLLib.Proofs.run_modifyThe_eq_ok h6, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      obtain ⟨⟨⟩, s7, h7, h⟩ := run_bind_eq_ok _ _ _ _ h
      obtain ⟨x7, rfl, k7, q7⟩ : ∃ y, s7 = pureState y ∧ WKeep x6 y ∧
          y.pendingPartialWithdrawals = sszDrop x6.pendingPartialWithdrawals pc :=
        ⟨_, EthCLLib.Proofs.run_modifyThe_eq_ok h7, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      obtain ⟨k8, q8⟩ := rest x7 (by frame_invert h)
      refine ⟨k5.trans (k6.trans (k7.trans k8)), ?_⟩
      rw [q8, q7, q6, q5]
  obtain ⟨hW, hppw⟩ := tail
  have hbv : b.validators = a.validators := hW.v.trans hv2
  have hcap : ∀ i, capN b i = capN a2 i := fun i => by unfold capN balN maxN; rw [hW.bal, hW.v]
  have hmb : moveN vals st₀ E a b ≤ pamtSum (a.pendingPartialWithdrawals.val.toList.take pc) := by
    rw [show moveN vals st₀ E a b = moveN vals st₀ E a a2 by unfold moveN; simp only [hcap]]
    exact Nat.le_trans hm2 hamt
  refine ⟨AcKeep.of_validators (hW.sl.trans hsl2) hbv, _,
    I.withdrawStep pc hbv (by rw [hW.bal]; exact hsz2) (hW.pc.trans hpc2)
      (by rw [hppw, sszDrop_toList, hppw2]) (hW.dbc.trans hdbc2) (hW.x1.trans hx12)
      (hW.x2.trans hx22) (hW.c1.trans hc12) (hW.c2.trans hc22)
      (fun e he => Nat.le_trans (hwe e he) hE) hmb⟩

end

end EthCLSpecs.Proofs.Heze
