import EthCLSpecs.Proofs.Heze.DriftInv
import EthCLSpecs.Proofs.Heze.KeyFrame
import EthCLSpecs.Proofs.Heze.Churn
import EthCLSpecs.Proofs.Heze.Time

/-!
# `EthCLSpecs.Proofs.Heze.DriftChurn`: the exit churn along a run

`compute_exit_epoch_and_update_churn` and its consolidation analogue reserve churn for a
balance (`reserveChurn`). This module restates one successful reservation on `Nat`, when its
values stay below `2 ^ 62` (`reserveChurn_toNat`). It bounds the churn that the ledger carries
after a reservation (`resTotal_sub_le`), and the move of the `earliest` epoch (`resEpoch_le`).

`compute_activation_exit_epoch` and `reserveChurn` raise on a `uint64` overflow. So the run
lemmas name the values that a successful run computed, the activation epoch `act` and the
reserved pair `(x, c)`, through `= .ok` hypotheses. They read the run through the exit lemmas of
`Churn.lean`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure run_bind_eq_ok run_pure_eq_ok run_get_bind_eq_ok
  run_assert_bind_eq_ok run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

/-! ## Sums with one changed index -/

/-- A sum over distinct indices, whose summand changes at the index `j` alone and grows there by
at most `d`, grows by at most `d`. -/
theorem sum_le_add_single (f g : ValidatorIndex → Nat) (j d : Nat) :
    ∀ l : List ValidatorIndex, l.Nodup → (∀ k ∈ l, k.toNat ≠ j → f k = g k) →
      (∀ k ∈ l, k.toNat = j → f k ≤ g k + d) → (l.map f).sum ≤ (l.map g).sum + d
  | [], _, _, _ => Nat.zero_le _
  | x :: l, hnd, h0, h1 => by
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    by_cases hxj : x.toNat = j
    · -- The other indices differ from `x`, so they keep their summand.
      have hrest : (l.map f).sum = (l.map g).sum := by
        congr 1
        refine List.map_congr_left fun y hy => h0 y (List.mem_cons_of_mem _ hy) fun hyj => hx ?_
        rw [UInt64.toNat_inj.mp (hxj.trans hyj.symm)]
        exact hy
      have := h1 x List.mem_cons_self hxj
      omega
    · rw [h0 x List.mem_cons_self hxj]
      have := sum_le_add_single f g j d l hnd' (fun k hk => h0 k (List.mem_cons_of_mem _ hk))
        (fun k hk => h1 k (List.mem_cons_of_mem _ hk))
      omega

/-! ## One reservation on `Nat` -/

/-- The epoch after one reservation of `bal` against the ledger `(ee, ebc)` at epoch `cur`,
with the churn `C` of one epoch, on `Nat`. -/
def resEpoch (lag ee ebc cur C bal : Nat) : Nat :=
  let earliest := max ee (cur + lag)
  let consume := if ee < earliest then C else ebc
  if consume < bal then earliest + ((bal - consume - 1) / C + 1) else earliest

/-- The churn that the ledger holds after the reservation, before the balance is taken. -/
def resTotal (lag ee ebc cur C bal : Nat) : Nat :=
  let earliest := max ee (cur + lag)
  let consume := if ee < earliest then C else ebc
  if consume < bal then consume + ((bal - consume - 1) / C + 1) * C else consume

section
variable [Preset]

/-- **One reservation keeps the ledger.** A reservation of `bal` adds at most `bal` to the
recorded exits, and the churn it consumes comes from the epochs it moves `earliest` by. -/
theorem ledger_step {e₀ ee₀ ebc₀ ee ebc cur C Cmax bal S S' : Nat}
    (hcur : e₀ ≤ cur) (hC : 0 < C) (hCm : C ≤ Cmax) (hmono : ee₀ ≤ ee)
    (hheld : S + ledgerHeld e₀ ee ebc ≤ ledgerCarry e₀ ee₀ ebc₀ + (ee - ledgerBase e₀ ee₀) * Cmax)
    (hS' : S' ≤ S + bal) :
    S' + ledgerHeld e₀ (resEpoch lagN ee ebc cur C bal) (resTotal lagN ee ebc cur C bal - bal) ≤
        ledgerCarry e₀ ee₀ ebc₀ + (resEpoch lagN ee ebc cur C bal - ledgerBase e₀ ee₀) * Cmax ∧
      ee ≤ resEpoch lagN ee ebc cur C bal ∧ cur + lagN ≤ resEpoch lagN ee ebc cur C bal ∧
      bal ≤ resTotal lagN ee ebc cur C bal := by
  have hlag : 1 ≤ lagN := by unfold lagN; omega
  unfold resEpoch resTotal
  dsimp only
  -- The quotient of the spread, and its two bounds.
  generalize hq : ((bal - (if ee < max ee (cur + lagN) then C else ebc) - 1) / C) = q
  have hq1 : q * C ≤ bal - (if ee < max ee (cur + lagN) then C else ebc) - 1 := by
    rw [← hq]; exact Nat.div_mul_le_self _ _
  have hq2 : bal - (if ee < max ee (cur + lagN) then C else ebc) - 1 < q * C + C := by
    rw [← hq]
    have := Nat.lt_div_mul_add (a := bal - (if ee < max ee (cur + lagN) then C else ebc) - 1) hC
    omega
  have hqC : q * C ≤ q * Cmax := Nat.mul_le_mul_left _ hCm
  have hsm : (q + 1) * C = q * C + C := Nat.succ_mul _ _
  have hsmax : (q + 1) * Cmax = q * Cmax + Cmax := Nat.succ_mul _ _
  unfold ledgerHeld ledgerBase ledgerCarry at *
  by_cases hf : ee < max ee (cur + lagN)
  · -- A stale ledger restarts at `cur + lagN` with a fresh epoch of churn.
    have hearl : max ee (cur + lagN) = cur + lagN := by omega
    rw [hearl] at hf hq1 hq2 ⊢
    simp only [hf, ↓reduceIte] at hq1 hq2 ⊢
    -- The base lies below the restart epoch, and `ee` lies below it too.
    have hb : max ee₀ (e₀ + lagN - 1) < cur + lagN := by omega
    have hD : (ee - max ee₀ (e₀ + lagN - 1)) + 1 ≤ cur + lagN - max ee₀ (e₀ + lagN - 1) := by omega
    have hDm := Nat.mul_le_mul_right Cmax hD
    rw [Nat.add_mul, Nat.one_mul] at hDm
    have hheld' : S ≤ (if e₀ + lagN ≤ ee₀ then ebc₀ else 0) +
        (ee - max ee₀ (e₀ + lagN - 1)) * Cmax := by split at hheld <;> omega
    by_cases hlt : C < bal
    · simp only [hlt, ↓reduceIte]
      have e1 : cur + lagN + (q + 1) - max ee₀ (e₀ + lagN - 1) =
          (cur + lagN - max ee₀ (e₀ + lagN - 1)) + (q + 1) := by omega
      have hsplit : ((cur + lagN - max ee₀ (e₀ + lagN - 1)) + (q + 1)) * Cmax =
          (cur + lagN - max ee₀ (e₀ + lagN - 1)) * Cmax + (q * Cmax + Cmax) := by
        rw [Nat.add_mul, hsmax]
      rw [e1, if_pos (by omega)]
      refine ⟨?_, by omega, by omega, by omega⟩
      omega
    · simp only [hlt, ↓reduceIte]
      rw [if_pos (by omega)]
      refine ⟨?_, by omega, by omega, by omega⟩
      omega
  · -- A live ledger spends its carried churn first.
    have hearl : max ee (cur + lagN) = ee := by omega
    rw [hearl] at hf hq1 hq2 ⊢
    simp only [hf, ↓reduceIte] at hq1 hq2 ⊢
    have hlive : e₀ + lagN ≤ ee := by omega
    rw [if_pos hlive] at hheld
    have hbe : max ee₀ (e₀ + lagN - 1) ≤ ee := by omega
    by_cases hlt : ebc < bal
    · simp only [hlt, ↓reduceIte]
      have e1 : ee + (q + 1) - max ee₀ (e₀ + lagN - 1) = (ee - max ee₀ (e₀ + lagN - 1)) + (q + 1) := by
        omega
      have hsplit : ((ee - max ee₀ (e₀ + lagN - 1)) + (q + 1)) * Cmax =
          (ee - max ee₀ (e₀ + lagN - 1)) * Cmax + (q * Cmax + Cmax) := by
        rw [Nat.add_mul, hsmax]
      rw [e1, if_pos (by omega)]
      refine ⟨?_, by omega, by omega, by omega⟩
      omega
    · simp only [hlt, ↓reduceIte]
      rw [if_pos hlive]
      refine ⟨?_, by omega, by omega, by omega⟩
      omega

/-- The churn that a ledger carries after a reservation is at most its carry before, or one
epoch of churn. -/
theorem resTotal_sub_le (ee ebc cur C bal : Nat) :
    resTotal lagN ee ebc cur C bal - bal ≤ max ebc C := by
  unfold resTotal
  dsimp only
  have hcons : (if ee < max ee (cur + lagN) then C else ebc) ≤ max ebc C := by split <;> omega
  generalize (if ee < max ee (cur + lagN) then C else ebc) = cons at hcons ⊢
  generalize hq : (bal - cons - 1) / C = q
  have hq1 : q * C ≤ bal - cons - 1 := by rw [← hq]; exact Nat.div_mul_le_self _ _
  have hsm : (q + 1) * C = q * C + C := Nat.succ_mul _ _
  split <;> omega

/-- The move of `earliest` by one reservation: at most `bal / C + 1` epochs past the earlier of
`earliest` and the restart epoch. -/
theorem resEpoch_le (ee ebc cur C bal : Nat) :
    resEpoch lagN ee ebc cur C bal ≤ max ee (cur + lagN) + (bal / C + 1) := by
  unfold resEpoch
  dsimp only
  generalize (if ee < max ee (cur + lagN) then C else ebc) = cons
  split
  · have : (bal - cons - 1) / C ≤ bal / C := Nat.div_le_div_right (by omega)
    omega
  · exact Nat.le_add_right _ _

end

section
variable [Preset]

omit [Preset] in
/-- A successful `reserveChurn` on `Nat`, when its values stay below `2 ^ 62`. The values come
from `reserveChurn_ok` when the balance does not fit, and from `reserveChurn_fits` when it
does. -/
theorem reserveChurn_toNat (bal consume per earliest : Gwei) {ee c : Gwei}
    (hb : bal.toNat < 2 ^ 62) (hc : consume.toNat < 2 ^ 62) (hp0 : 0 < per.toNat)
    (hp : per.toNat < 2 ^ 62) (he : earliest.toNat < 2 ^ 62)
    (hr : (EthCLSpecs.Heze.reserveChurn bal consume per earliest : Except StateTransitionError _)
      = .ok (ee, c)) :
    ee.toNat =
        (if consume.toNat < bal.toNat then
          earliest.toNat + ((bal.toNat - consume.toNat - 1) / per.toNat + 1) else earliest.toNat) ∧
      c.toNat =
        (if consume.toNat < bal.toNat then
          consume.toNat + ((bal.toNat - consume.toNat - 1) / per.toNat + 1) * per.toNat
        else consume.toNat) := by
  by_cases hlt' : consume.toNat < bal.toNat
  · simp only [if_pos hlt']
    -- The spread and its product with the churn stay small, so no checked step fires.
    have hqle : (bal.toNat - consume.toNat - 1) / per.toNat ≤ bal.toNat :=
      Nat.le_trans (Nat.div_le_self _ _) (by omega)
    have hmul : ((bal.toNat - consume.toNat - 1) / per.toNat + 1) * per.toNat < 2 ^ 63 := by
      have := Nat.div_mul_le_self (bal.toNat - consume.toNat - 1) per.toNat
      rw [Nat.succ_mul]
      omega
    obtain ⟨epoch, consumed, hok, he1, hc1⟩ := reserveChurn_ok bal consume per earliest
      (UInt64.lt_iff_toNat_lt.mpr hlt') hp0
      (by simp only [EthCLSpecs.Proofs.Fulu.churnEpochs]; omega)
      (by simp only [EthCLSpecs.Proofs.Fulu.churnEpochs]; omega)
      (by simp only [EthCLSpecs.Proofs.Fulu.churnEpochs]; omega)
    rw [hok] at hr
    injection hr with hr
    injection hr with h1 h2
    subst h1 h2
    exact ⟨he1, hc1⟩
  · simp only [if_neg hlt']
    rw [reserveChurn_fits _ _ _ _
      (UInt64.le_iff_toNat_le.mpr (Nat.le_of_not_lt hlt'))] at hr
    injection hr with hr
    injection hr with h1 h2
    subst h1 h2
    exact ⟨rfl, rfl⟩

end

/-- A successful `checkedAdd` keeps the state, returns the sum, and does not wrap. -/
theorem checkedAdd_run_ok {σ : Type} {a b : UInt64} {d : String} {s s' : σ} {r : UInt64}
    (h : (checkedAdd (m := StateT σ (Except StateTransitionError)) a b d).run s = .ok (r, s')) :
    s' = s ∧ r = a + b ∧ a.toNat + b.toNat < 2 ^ 64 := by
  unfold checkedAdd throwArithmetic at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hc, h⟩
  · cases h
  · rw [EthCLLib.Proofs.run_pure] at h
    injection h with h
    injection h with h1 h2
    refine ⟨h2.symm, h1.symm, ?_⟩
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hc
    have := UInt64.toNat_lt a
    have := UInt64.toNat_lt b
    omega

/-- A `foldlM` over a list whose steps keep the state keeps the state. -/
theorem listFoldlM_run_state_eq {σ ε α β : Type} {f : β → α → StateT σ (Except ε) β}
    (hf : ∀ b a s r s', (f b a).run s = .ok (r, s') → s' = s) :
    ∀ (l : List α) (b : β) (s s' : σ) (r : β), (l.foldlM f b).run s = .ok (r, s') → s' = s
  | [], b, s, s', r, h => by
    rw [List.foldlM_nil] at h
    exact (EthCLLib.Proofs.run_pure_eq_ok_state h).2
  | a :: l, b, s, s', r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
    rw [listFoldlM_run_state_eq hf l b' s1 s' r h, hf _ _ _ _ _ h1]

/-- A successful `checkedMul` keeps the state, returns the product, and does not wrap. -/
theorem checkedMul_run_ok {σ : Type} {a b : UInt64} {d : String} {s s' : σ} {r : UInt64}
    (h : (checkedMul (m := StateT σ (Except StateTransitionError)) a b d).run s = .ok (r, s')) :
    s' = s ∧ r = a * b ∧ (a * b).toNat = a.toNat * b.toNat := by
  unfold checkedMul throwArithmetic at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hc, h⟩
  · cases h
  · rw [EthCLLib.Proofs.run_pure] at h
    injection h with h
    injection h with h1 h2
    exact ⟨h2.symm, h1.symm, EthCLLib.Proofs.toNat_mul_of_guard _ _ hc⟩

section
variable [Preset] [HasherTag] [Config]

/-- The exit churn limit of `u`. The read sums the active balances, so it is `Except`. A fault
gives `0`, as in `totBal`. A successful reservation reads the limit without a fault
(`computeExitEpochAndUpdateChurn_run`). -/
def exitChurn (u : BeaconState) : Gwei :=
  match EthCLSpecs.Heze.getExitChurnLimit (pureState u) with
  | .ok g => g
  | .error _ => 0

/-- The consolidation churn limit of `u`, with the fault rule of `exitChurn`. -/
def consChurn (u : BeaconState) : Gwei :=
  match EthCLSpecs.Heze.getConsolidationChurnLimit (pureState u) with
  | .ok g => g
  | .error _ => 0

/-- The state after `computeExitEpochAndUpdateChurn bal`, which reserved the epoch `x` and the
consumed total `c`. -/
def afterExitChurn (a : BeaconState) (bal : Gwei) (x : EthCLSpecs.Heze.Epoch) (c : Gwei) :
    BeaconState :=
  { a with exitBalanceToConsume := c - bal, earliestExitEpoch := x }

/-- The run of `computeExitEpochAndUpdateChurn` on a plain state. A successful run computed the
activation epoch `act`, read the exit churn limit `exitChurn a`, and reserved the pair
`(x, c)`, and it wrote that pair. -/
theorem computeExitEpochAndUpdateChurn_run (bal : Gwei) (a : BeaconState) {x : EthCLSpecs.Heze.Epoch}
    {s' : BeaconState}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) bal).run
      (pureState a) = .ok (x, pureState s')) :
    ∃ act c : UInt64,
      (EthCLSpecs.Heze.computeActivationExitEpoch (EthCLSpecs.Heze.computeEpochAtSlot a.slot)
        : Except StateTransitionError UInt64) = .ok act ∧
      EthCLSpecs.Heze.getExitChurnLimit (pureState a) = .ok (exitChurn a) ∧
      (EthCLSpecs.Heze.reserveChurn bal
        (if a.earliestExitEpoch < umax a.earliestExitEpoch act
          then exitChurn a else a.exitBalanceToConsume)
        (exitChurn a)
        (umax a.earliestExitEpoch act) : Except StateTransitionError _) = .ok (x, c) ∧
      s' = afterExitChurn a bal x c := by
  cases hact : (EthCLSpecs.Heze.computeActivationExitEpoch
      (EthCLSpecs.Heze.computeEpochAtSlot a.slot) : Except StateTransitionError UInt64) with
  | error err =>
    rw [computeExitEpochAndUpdateChurn_run_activation_error a bal err hact] at h
    cases h
  | ok act =>
    cases hch : EthCLSpecs.Heze.getExitChurnLimit (pureState a) with
    | error err =>
      rw [computeExitEpochAndUpdateChurn_run_churn_error a bal act err hact hch] at h
      cases h
    | ok churn =>
      have ec : exitChurn a = churn := by
        unfold exitChurn
        rw [hch]
      rw [ec]
      cases hres : (EthCLSpecs.Heze.reserveChurn bal
          (if a.earliestExitEpoch < umax a.earliestExitEpoch act
            then churn else a.exitBalanceToConsume)
          churn
          (umax a.earliestExitEpoch act) : Except StateTransitionError _) with
      | error err =>
        rw [computeExitEpochAndUpdateChurn_run_reserve_error a bal act churn err hact hch hres] at h
        cases h
      | ok p =>
        obtain ⟨ep, c⟩ := p
        rw [computeExitEpochAndUpdateChurn_run_ok a bal act churn ep c hact hch hres] at h
        injection h with h
        injection h with h1 h2
        subst h1
        exact ⟨act, c, by first | exact hact | rfl, rfl, by first | exact hres | rfl,
          (EthCLLib.Proofs.pureState_inj h2).symm⟩

/-- The run of `initiateValidatorExit` on a plain state. A validator that already exits stays.
Otherwise the run computed the activation epoch `act`, reserved the exit churn `(x, c)` for the
effective balance, and set the exit epoch `x` and the withdrawable epoch
`x + MIN_VALIDATOR_WITHDRAWABILITY_DELAY`. -/
theorem initiateValidatorExit_run [CryptoBackend] (i : ValidatorIndex) (a b : BeaconState)
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState a) = .ok ((), pureState b)) :
    ∃ v, a.validators.val[i.toNat]? = some v ∧
      ((v.exitEpoch ≠ EthCLSpecs.Heze.Const.farFutureEpoch ∧ b = a) ∨
       (v.exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch ∧
        ∃ (act : UInt64) (x : EthCLSpecs.Heze.Epoch) (c : Gwei),
         (EthCLSpecs.Heze.computeActivationExitEpoch (EthCLSpecs.Heze.computeEpochAtSlot a.slot)
           : Except StateTransitionError UInt64) = .ok act ∧
         EthCLSpecs.Heze.getExitChurnLimit (pureState a) = .ok (exitChurn a) ∧
         (EthCLSpecs.Heze.reserveChurn v.effectiveBalance
          (if a.earliestExitEpoch < umax a.earliestExitEpoch act
            then exitChurn a else a.exitBalanceToConsume)
          (exitChurn a)
          (umax a.earliestExitEpoch act) : Except StateTransitionError _) = .ok (x, c) ∧
         x.toNat + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64 ∧
         b = { afterExitChurn a v.effectiveBalance x c with
           validators := a.validators.set! i.toNat
             { v with exitEpoch := x,
                      withdrawableEpoch := x + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay } })) := by
  unfold EthCLSpecs.Heze.initiateValidatorExit at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨v, s1, hv, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hv', rfl⟩ := sszGetIdx_run_ok hv
  simp only [SizzLean.Proofs.view_uncachedBox] at hv'
  refine ⟨v, hv', ?_⟩
  rcases run_ite_eq_ok h with ⟨hc, h⟩ | ⟨hc, h⟩
  · have := run_pure_eq_ok _ _ _ _ h
    rw [EthCLLib.Proofs.run_pure] at h
    injection h with h
    injection h with _ h
    refine .inl ⟨?_, (congrArg SizzLean.Cache.SSZ.Box.view h).symm⟩
    unfold EthCLSpecs.Heze.hasNotInitiatedExit at hc
    simpa using hc
  · have hfar : v.exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch := by
      unfold EthCLSpecs.Heze.hasNotInitiatedExit at hc
      simpa using hc
    obtain ⟨x, s2, hx, h⟩ :=
      EthCLLib.Proofs.run_bind_eq_ok_pure (keepsUncached_computeExitEpochAndUpdateChurn _) h
    obtain ⟨act, c, hact, hch, hres, hs2⟩ := computeExitEpochAndUpdateChurn_run _ _ hx
    subst hs2
    obtain ⟨we, s3, hwe, h⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨rfl, hwe', hno⟩ := checkedAdd_run_ok hwe
    have e1 := EthCLLib.Proofs.run_modifyThe_eq_ok h
    refine .inr ⟨hfar, act, x, c, hact, hch, hres, hno, ?_⟩
    have ev := congrArg SizzLean.Cache.SSZ.Box.view e1
    change b = _ at ev
    rw [ev, hwe']
    -- `modValidator` reads the old validator at `i`, which is `v`.
    have hget : a.validators[i.toNat]! = v := by
      rw [sszList_getElem!_eq, getElem!_pos a.validators.val i.toNat
        (Array.getElem?_eq_some_iff.mp hv').1]
      exact (Array.getElem?_eq_some_iff.mp hv').2
    rw [modValidator_pureState, SizzLean.Proofs.view_uncachedBox]
    have hget' : (afterExitChurn a v.effectiveBalance x c).validators[i.toNat]! = v := hget
    unfold afterExitChurn at hget' ⊢
    rw [hget']

end

end EthCLSpecs.Proofs.Heze
