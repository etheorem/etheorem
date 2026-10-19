import EthCLSpecs.Proofs.Heze.TargetStake
import EthCLSpecs.Proofs.Heze.DriftMath

/-!
# `EthCLSpecs.Proofs.Heze.EbUpdates`: what `process_effective_balance_updates` writes

The update loop writes the effective balance of each validator from its balance by the
hysteresis rule (`ebuVal`) and keeps every other field. The loop reads each balance through
`sszGetIdx`. In each step it forms the two hysteresis thresholds as checked products, and the
two sums of the band test as checked sums.
`processEffectiveBalanceUpdates_run` states a successful run as a fold of one write per index
(`ebuBody`), and `ebuFold_spec` reads the fold.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Epoch ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

/-- One step of the update loop, on a plain state: update the effective balance at `i` when
the balance leaves the hysteresis band. -/
def ebuBody (b : BeaconState) (i : Nat) : BeaconState :=
  let hys := EthCLSpecs.Heze.Const.effectiveBalanceIncrementG /
    UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisQuotient
  let downward := hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisDownwardMultiplier
  let upward := hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisUpwardMultiplier
  let v := b.validators[i]!
  let bal := b.balances[i]!
  if bal + downward < v.effectiveBalance || v.effectiveBalance + upward < bal then
    let floor := bal - bal % EthCLSpecs.Heze.Const.effectiveBalanceIncrementG
    let eb := umin floor (EthCLSpecs.Heze.getMaxEffectiveBalance v)
    -- `modValidator` writes at the `uint64` cast of `i`, and reads the old element there.
    let j := (UInt64.ofNat i).toNat
    let v' : Validator := { b.validators[j]! with effectiveBalance := eb }
    { b with validators := b.validators.set! j v' }
  else b

/-- The update of one validator with its balance. -/
def ebuVal (v : Validator) (bal : Gwei) : Validator :=
  let hys := EthCLSpecs.Heze.Const.effectiveBalanceIncrementG /
    UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisQuotient
  let downward := hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisDownwardMultiplier
  let upward := hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisUpwardMultiplier
  if bal + downward < v.effectiveBalance || v.effectiveBalance + upward < bal then
    let floor := bal - bal % EthCLSpecs.Heze.Const.effectiveBalanceIncrementG
    { v with effectiveBalance := umin floor (EthCLSpecs.Heze.getMaxEffectiveBalance v) }
  else v

omit [HasherTag] in
theorem ebuBody_eq (b : BeaconState) (i : Nat) :
    ebuBody b i = { b with validators := (ebuBody b i).validators } := by
  unfold ebuBody; dsimp only; split <;> rfl

omit [HasherTag] in
theorem ebuBody_size (b : BeaconState) (i : Nat) :
    (ebuBody b i).validators.size = b.validators.size := by
  unfold ebuBody; dsimp only; split
  · exact SizzLean.Proofs.sszListSet!_size _ _ _
  · rfl

omit [HasherTag] in
theorem ebuBody_balances (b : BeaconState) (i : Nat) :
    (ebuBody b i).balances = b.balances := by
  rw [ebuBody_eq]

omit [HasherTag] in
theorem ebuBody_get_ne (b : BeaconState) (i j : Nat) (h : (UInt64.ofNat i).toNat ≠ j) :
    (ebuBody b i).validators[j]! = b.validators[j]! := by
  unfold ebuBody; dsimp only; split
  · exact SizzLean.Proofs.sszListSet!_getElem!_ne _ _ _ _ h
  · rfl

omit [HasherTag] in
theorem ebuBody_get_self (b : BeaconState) (i : Nat) (h64 : i < 2 ^ 64)
    (hi : i < b.validators.size) :
    (ebuBody b i).validators[i]! = ebuVal b.validators[i]! b.balances[i]! := by
  have hc : (UInt64.ofNat i).toNat = i := by
    exact UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  unfold ebuBody ebuVal
  dsimp only
  simp only [hc]
  split
  · exact SizzLean.Proofs.sszListSet!_getElem!_self _ _ _ hi
  · rfl

omit [HasherTag] in
/-- The fold of the update loop: it keeps every field but the registry, it keeps the size of
the registry, and it updates each validator with its own balance. -/
theorem ebuFold_spec (st : BeaconState) (h64 : st.validators.size ≤ 2 ^ 64) :
    ∀ k, k ≤ st.validators.size →
      let r := (List.range' 0 k).foldl ebuBody st
      r = { st with validators := r.validators } ∧ r.validators.size = st.validators.size ∧
        (∀ j, j < k → r.validators[j]! = ebuVal st.validators[j]! st.balances[j]!) ∧
        (∀ j, k ≤ j → r.validators[j]! = st.validators[j]!)
  | 0, _ => ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | k + 1, hk => by
    obtain ⟨e, hs, hlo, hhi⟩ := ebuFold_spec st h64 k (Nat.le_of_succ_le hk)
    intro r
    have hr : r = ebuBody ((List.range' 0 k).foldl ebuBody st) k := by
      show (List.range' 0 (k + 1)).foldl ebuBody st = _
      rw [List.range'_concat, List.foldl_append]
      simp
    have hck : (UInt64.ofNat k).toNat = k := by
      exact UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
    refine ⟨?_, ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [hr, ebuBody_eq, e]
    · rw [hr, ebuBody_size, hs]
    · rw [hr]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [ebuBody_get_ne _ _ _ (by omega), hlo j hj]
      · rw [ebuBody_get_self _ _ (by omega) (by omega), hhi j (Nat.le_refl _), e]
    · rw [hr, ebuBody_get_ne _ _ _ (by omega), hhi j (by omega)]

omit [Preset] [HasherTag] in
/-- A loop over a list in `StateT σ (Except ε)`. Its body, from the image `p t`, yields and
moves to the image of `f t i`. A successful run of the loop runs the fold of `f`. -/
theorem forIn_run_foldl {σ τ ε : Type} (p : τ → σ) (f : τ → Nat → τ)
    (body : Nat → PUnit → StateT σ (Except ε) (ForInStep PUnit))
    (h : ∀ i t r s', (body i PUnit.unit).run (p t) = .ok (r, s') →
      r = .yield PUnit.unit ∧ s' = p (f t i)) :
    ∀ (l : List Nat) (t : τ) (s' : σ),
      (forIn l PUnit.unit body).run (p t) = .ok (PUnit.unit, s') → s' = p (l.foldl f t)
  | [], t, s', hr => by
    rw [List.forIn_nil] at hr
    exact (EthCLLib.Proofs.run_pure_eq_ok_state hr).2
  | i :: rest, t, s', hr => by
    rw [List.forIn_cons] at hr
    obtain ⟨st, s1, hb, hrest⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hr
    obtain ⟨rfl, rfl⟩ := h i t st s1 hb
    exact forIn_run_foldl p f body h rest (f t i) s' hrest

/-- A successful run of the update loop is the fold of `ebuBody`. The balance read went
through `sszGetIdx`, and the two threshold products and the two sums of the band test are
checked. So each read is in range and no product or sum overflowed. The wrapping products and
sums of `ebuBody` are then the values that the run formed. The second sum runs only when the
first test fails, as in the pyspec's `or`. -/
theorem processEffectiveBalanceUpdates_run (st w : BeaconState)
    (h : (EthCLSpecs.Heze.processEffectiveBalanceUpdates (StateTransition := HezeRun)).run
      (pureState st) = .ok ((), pureState w)) :
    w = (List.range' 0 st.validators.size).foldl ebuBody st := by
  unfold EthCLSpecs.Heze.processEffectiveBalanceUpdates at h
  extract_lets hys at h
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  extract_lets n at h
  obtain ⟨⟨⟩, s1, hloop, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
  have e1 := (EthCLLib.Proofs.run_pure_eq_ok_state h).2
  subst e1
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop
  have hf := forIn_run_foldl pureState ebuBody _ ?step _ st _ hloop
  · exact pureState_inj (by simpa [n, Std.Legacy.Range.size] using hf)
  case step =>
    intro i t r s' hb
    have hb := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ hb
    extract_lets v at hb
    -- The balance read is in range, and it keeps the state.
    obtain ⟨bal, s2, hbal, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
    obtain ⟨hbal', rfl⟩ := sszGetIdx_run_ok hbal
    -- The two hysteresis products did not overflow. Each keeps the state, and its value is the
    -- wrapping product of `ebuBody`.
    obtain ⟨down, s2d, hdown, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
    unfold checkedMul throwArithmetic at hdown
    rcases run_ite_eq_ok hdown with ⟨-, hdown⟩ | ⟨-, hdown⟩
    · cases hdown
    obtain ⟨rfl, rfl⟩ := EthCLLib.Proofs.run_pure_eq_ok_state hdown
    obtain ⟨up, s2u, hup, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
    unfold checkedMul throwArithmetic at hup
    rcases run_ite_eq_ok hup with ⟨-, hup⟩ | ⟨-, hup⟩
    · cases hup
    obtain ⟨rfl, rfl⟩ := EthCLLib.Proofs.run_pure_eq_ok_state hup
    -- The first sum of the band test did not overflow.
    obtain ⟨lo, s3, hlo, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
    have e3 := checkedAdd_run_state hlo
    subst e3
    unfold checkedAdd throwArithmetic at hlo
    rcases run_ite_eq_ok hlo with ⟨-, hlo⟩ | ⟨hno1, hlo⟩
    · cases hlo
    have elo := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hlo
    subst elo
    -- `extract_lets` lifts the new effective balance out of the join point first.
    extract_lets newEff jp at hb
    -- The test value is the `||` of `ebuBody`: the second sum runs only when the first test
    -- fails.
    have hbal'' : t.balances[i]! = bal := by
      rw [sszList_getElem!_eq, getElem!_def]
      have : t.balances.val[i]? = some bal := hbal'
      simp only [this]
    obtain ⟨upd, hupd, hb⟩ : ∃ upd : Bool,
        upd = (t.balances[i]! +
            hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisDownwardMultiplier <
              v.effectiveBalance ||
          v.effectiveBalance + hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisUpwardMultiplier <
            t.balances[i]!) ∧
        (jp upd).run (pureState t) = .ok (r, s') := by
      rw [hbal'']
      rcases run_ite_eq_ok hb with ⟨hc, hb⟩ | ⟨hc, hb⟩
      · refine ⟨true, by simp [hc], ?_⟩
        exact hb
      · obtain ⟨hi, s4, hhi, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
        have e4 := checkedAdd_run_state hhi
        subst e4
        unfold checkedAdd throwArithmetic at hhi
        rcases run_ite_eq_ok hhi with ⟨-, hhi⟩ | ⟨-, hhi⟩
        · cases hhi
        have ehi := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hhi
        subst ehi
        exact ⟨_, by simp [hc], hb⟩
    -- The join point writes the update when the test passes. `show` states `ebuBody` with the
    -- names of the run, so the test is `upd`.
    simp only [jp] at hb
    show r = _ ∧ s' = pureState (if (t.balances[i]! +
        hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisDownwardMultiplier <
          v.effectiveBalance ||
      v.effectiveBalance + hys * UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisUpwardMultiplier <
        t.balances[i]!) = true then _ else t)
    rw [← hupd]
    rcases run_ite_eq_ok hb with ⟨hc, hb⟩ | ⟨hc, hb⟩
    · obtain ⟨_, s5, h5, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
      have e5 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h5
      subst e5
      have ⟨er, es⟩ := EthCLLib.Proofs.run_pure_eq_ok_state hb
      refine ⟨er, ?_⟩
      rw [if_pos hc, es, modValidator_pureState, hbal'']
      rfl
    · obtain ⟨_, s5, h5, hb⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ hb
      have e5 := (EthCLLib.Proofs.run_pure_eq_ok_state h5).2
      subst e5
      have ⟨er, es⟩ := EthCLLib.Proofs.run_pure_eq_ok_state hb
      refine ⟨er, ?_⟩
      rw [if_neg hc, es]

end

end EthCLSpecs.Proofs.Heze
