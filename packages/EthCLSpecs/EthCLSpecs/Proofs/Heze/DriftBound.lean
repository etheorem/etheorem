import EthCLSpecs.Proofs.Heze.DriftDefs

/-!
# `EthCLSpecs.Proofs.Heze.DriftBound`: the drift from the facts at the end of a run

The stake drift of a run from `st₀` to `u` over a list `vals` is the sum of the distances of
the link stakes, plus the shortfall of the total active balance (`drift`). This module bounds
it by facts about the two states alone (`EndFacts`). The run itself enters through those facts
(`StakeDrift.lean`).

The link stake of `i` is its effective balance behind a gate: `i` is active at the current or
the previous epoch (`laB`). The total active balance counts the validators active at the
current epoch (`acB`). For two gated values `absDiff_gate_le` splits the distance in two:

- The distance of the effective balances, where the gate of `u` is open (the EB term).
- The effective balance at `st₀`, where the two gates differ (the set term).

The EB term follows `EbTrack` (`DriftMath.lean`). A gate changes only for a validator that
`st₀` already queues for activation, that `st₀` already schedules to exit by `E`, or that the
run makes exit by `E`. The first two are values of `st₀`, and the third has the bound `ne`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset BeaconState ValidatorIndex Validator Gwei currentEpochOf
  previousEpochOf isActiveValidator)

section
variable [Preset] [HasherTag]

/-- The gate of the link stake: active at the current or the previous epoch. -/
def laB (u : BeaconState) (i : Nat) : Bool :=
  match u.validators.val[i]? with
  | some v => isActiveValidator v (currentEpochOf (pureState u)) ||
      isActiveValidator v (previousEpochOf (pureState u))
  | none => false

/-- The gate of the total active balance: active at the current epoch. -/
def acB (u : BeaconState) (i : Nat) : Bool :=
  match u.validators.val[i]? with
  | some v => isActiveValidator v (currentEpochOf (pureState u))
  | none => false

theorem linkStake_eq (u : BeaconState) (i : ValidatorIndex) :
    linkStake u i = if laB u i.toNat then ebN u i.toNat else 0 := by
  unfold linkStake laB ebN
  cases u.validators.val[i.toNat]? <;> simp

omit [Preset] [HasherTag] in
/-- A sum over a filter is the sum of the gated summand. -/
theorem sum_filter_eq_sum_ite {α : Type} (p : α → Bool) (f : α → Nat) :
    ∀ l : List α, ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum
  | [] => rfl
  | x :: l => by
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases p x <;> simp [sum_filter_eq_sum_ite p f l]

/-- The total active balance of `u` is the `Nat` sum of the effective balances of the active
indices, or the floor `EFFECTIVE_BALANCE_INCREMENT`, when the sum of all effective balances
fits a `uint64`. Then the checked read succeeds, so `totBal` is the read. -/
theorem totalActive_toNat (u : BeaconState)
    (hsum : (u.validators.val.toList.map (·.effectiveBalance.toNat)).sum < 2 ^ 64)
    (h64 : u.validators.val.size < 2 ^ 64) :
    (totBal u).toNat =
      max ((List.range u.validators.val.size).map fun i =>
          if acB u i then ebN u i else 0).sum
        EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat := by
  let n := u.validators.val.size
  let P := (EthCLSpecs.Heze.getActiveValidatorIndices (pureState u)
    (currentEpochOf (pureState u))).toList
  let g : Nat → Nat := fun i => (u.validators.val[i]!).effectiveBalance.toNat
  let q : Nat → Bool := fun i =>
    isActiveValidator u.validators.val[i]! (currentEpochOf (pureState u))
  have hP : P = ((List.range n).filter q).map UInt64.ofNat :=
    getActiveValidatorIndices_toList u _
  -- The active sum, as a gated sum over the registry indices.
  have h1 : (P.map fun x => g x.toNat) = ((List.range n).filter q).map g := by
    rw [hP, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    simp only [Function.comp, EthCLLib.Proofs.toNat_ofNat_lt64 (by omega : i < 2 ^ 64)]
  have h3 : ((List.range n).map fun i => if q i then g i else 0) =
      (List.range n).map fun i => if acB u i then ebN u i else 0 := by
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    unfold acB ebN
    rw [getElem?_pos u.validators.val i hi']
    simp only [q, g, getElem!_pos u.validators.val i hi']
  have hPsum : (P.map fun x => g x.toNat).sum = ((List.range n).map fun i =>
      if acB u i then ebN u i else 0).sum := by
    rw [h1, sum_filter_eq_sum_ite, h3]
  -- The active sum is at most the registry sum, so the `uint64` fold does not wrap.
  have hle : (P.map fun x => g x.toNat).sum ≤
      (u.validators.val.toList.map (·.effectiveBalance.toNat)).sum := by
    rw [h1, sum_filter_eq_sum_ite, ← sum_range_getElem! u.validators.val]
    exact sum_map_le_sum_map _ _ (fun i => by simp only [g]; split <;> omega) _
  -- Each active index is a registry index, and the active sum fits, so the read succeeds.
  have hin : ∀ x ∈ P, x.toNat < n := by
    intro x hx
    rw [hP] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    rw [EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)]
    exact hi'
  have hfit : (P.map fun x => g x.toNat).sum < 2 ^ 64 := Nat.lt_of_le_of_lt hle hsum
  have hok := getTotalBalance_ok_of (u := u) (idx := EthCLSpecs.Heze.getActiveValidatorIndices
    (pureState u) (currentEpochOf (pureState u))) hin hfit
  rw [totBal_of_ok hok, umax_toNat]
  -- `effBal u x` is `g x.toNat`, and the active list is `P`.
  change max (UInt64.ofNat (P.map fun x => g x.toNat).sum).toNat _ = _
  rw [EthCLLib.Proofs.toNat_ofNat_lt64 hfit, hPsum]

/-- The drift of `u` from `st₀` over `vals`: the distances of the link stakes, plus the
shortfall of the total active balance. -/
def drift (vals : List ValidatorIndex) (st₀ u : BeaconState) : Nat :=
  EthCLLib.Proofs.FFG.absDiffSum (linkStake u) (linkStake st₀) vals +
    ((totBal st₀).toNat - (totBal u).toNat)

/-! ## Sums over `vals` against sums over the registry -/

omit [Preset] [HasherTag] in
/-- A sum over distinct indices of a summand that vanishes from `n` on is at most the sum
over the indices below `n`. -/
theorem sum_vals_le_range (vals : List ValidatorIndex) (hnd : vals.Nodup) (g : Nat → Nat)
    (n : Nat) (hg : ∀ i, n ≤ i → g i = 0) :
    (vals.map fun i => g i.toNat).sum ≤ ((List.range n).map g).sum := by
  rw [show (vals.map fun i => g i.toNat).sum =
      ((vals.filter fun i => decide (i.toNat < n)).map fun i => g i.toNat).sum by
    rw [sum_filter_eq_sum_ite]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    by_cases h : i.toNat < n
    · simp [h]
    · simp [h, hg i.toNat (by omega)]]
  rw [show ((vals.filter fun i => decide (i.toNat < n)).map fun i => g i.toNat) =
      ((vals.filter fun i => decide (i.toNat < n)).map UInt64.toNat).map g by
    rw [List.map_map]; rfl]
  refine sum_map_le_of_subset g _ _ ?_ fun i hi => ?_
  · exact EthCLLib.Proofs.nodup_map_of_injOn (hnd.filter _)
      fun a _ b _ hab => UInt64.toNat_inj.mp hab
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    exact List.mem_range.mpr (by simpa using (List.mem_filter.mp hx).2)

omit [Preset] [HasherTag] in
/-- A sum over the indices below `n` is at most the sum over a list that holds each of them. -/
theorem sum_range_le_vals (vals : List ValidatorIndex) (g : Nat → Nat) (n : Nat)
    (h64 : n ≤ 2 ^ 64) (hcov : ∀ i, i < n → UInt64.ofNat i ∈ vals) :
    ((List.range n).map g).sum ≤ (vals.map fun i => g i.toNat).sum := by
  rw [show ((List.range n).map g) = ((List.range n).map UInt64.ofNat).map fun i => g i.toNat by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [Function.comp, EthCLLib.Proofs.toNat_ofNat_lt64 (by omega : i < 2 ^ 64)]]
  refine sum_map_le_of_subset _ _ _ ?_ fun x hx => ?_
  · refine EthCLLib.Proofs.nodup_map_of_injOn List.nodup_range fun a ha b hb hab => ?_
    have h1 := List.mem_range.mp ha
    have h2 := List.mem_range.mp hb
    have := congrArg UInt64.toNat hab
    rwa [EthCLLib.Proofs.toNat_ofNat_lt64 (by omega), EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)]
      at this
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hcov i (List.mem_range.mp hi)

omit [Preset] [HasherTag] in
/-- A sum is at most another sum plus the distances. -/
theorem sum_le_add_absDiff {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map f).sum ≤ (l.map g).sum + (l.map fun x => absDiff (g x) (f x)).sum
  | [] => Nat.le_refl _
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_add_absDiff f g l
    have := le_add_absDiff (f x) (g x)
    rw [absDiff_comm (g x) (f x)]
    omega

/-! ## The bound -/

/-- The activation epoch of index `i`, in `Nat`, or zero past the registry. -/
def actOf (u : BeaconState) (i : Nat) : Nat :=
  match u.validators.val[i]? with
  | some v => v.activationEpoch.toNat
  | none => 0

/-- The exit epoch of index `i`, in `Nat`, or the far future past the registry. -/
def exitOf (u : BeaconState) (i : Nat) : Nat :=
  match u.validators.val[i]? with
  | some v => v.exitEpoch.toNat
  | none => 2 ^ 64 - 1

/-- The distance of the capped balance from the effective balance at the fork point. -/
def eps0 (st₀ : BeaconState) (i : Nat) : Nat := absDiff (capN st₀ i) (ebN st₀ i)

/-- The EB-term bound of a capped move `x` (`EbTrack.bound`). -/
def abound (A d x : Nat) : Nat := x + A * x / (d + 1)

/-- The current epoch, in `Nat`. -/
def epochN (u : BeaconState) : Nat := (currentEpochOf (pureState u)).toNat

/-- `st₀` queues `i` for activation after its current epoch. -/
def pendingB (st₀ : BeaconState) (i : Nat) : Bool := decide (epochN st₀ < actOf st₀ i)

/-- `st₀` schedules `i` to exit from its current epoch up to `E`. -/
def schedB (st₀ : BeaconState) (E i : Nat) : Bool :=
  decide (exitOf st₀ i ≠ 2 ^ 64 - 1 ∧ epochN st₀ ≤ exitOf st₀ i ∧ exitOf st₀ i ≤ E)

/-- The run makes `i` exit by `E`, and `st₀` had no exit for it. -/
def newExitB (st₀ u : BeaconState) (E i : Nat) : Bool :=
  decide (i < st₀.validators.val.size ∧ exitOf st₀ i = 2 ^ 64 - 1 ∧ exitOf u i ≤ E)

/-- The facts at the end state `u` of a run from `st₀` that bound the drift. `V i` bounds the
move of the capped balance of `i` since `st₀`, and `W i` is the effective balance at which the
run made `i` exit. `vb` and `ne` bound their sums. -/
structure EndFacts (vals : List ValidatorIndex) (st₀ u : BeaconState) (E A d : Nat)
    (V W : Nat → Nat) (vb ne : Nat) : Prop where
  nodup : vals.Nodup
  cover : ∀ i, i < st₀.validators.val.size → UInt64.ofNat i ∈ vals
  h64₀ : st₀.validators.val.size < 2 ^ 64
  h64u : u.validators.val.size < 2 ^ 64
  sum₀ : (st₀.validators.val.toList.map (·.effectiveBalance.toNat)).sum < 2 ^ 64
  sumu : (u.validators.val.toList.map (·.effectiveBalance.toNat)).sum < 2 ^ 64
  laLive : ∀ i ∈ vals, laB u i.toNat = true → liveB st₀ E i.toNat = true
  track : ∀ i ∈ vals, liveB st₀ E i.toNat = true →
    EbTrack d A (ebN u i.toNat) (ebN st₀ i.toNat) (eps0 st₀ i.toNat) (V i.toNat)
  gate : ∀ i ∈ vals, (laB u i.toNat ≠ laB st₀ i.toNat ∨ acB u i.toNat ≠ acB st₀ i.toNat) →
    ebN st₀ i.toNat ≠ 0 →
    pendingB st₀ i.toNat = true ∨ schedB st₀ E i.toNat = true ∨ newExitB st₀ u E i.toNat = true
  neEB : ∀ i ∈ vals, newExitB st₀ u E i.toNat = true →
    ebN st₀ i.toNat ≤ W i.toNat + abound A d (eps0 st₀ i.toNat + V i.toNat) ∧
      liveB st₀ E i.toNat = true
  neSum : ((vals.filter fun i => newExitB st₀ u E i.toNat).map fun i => W i.toNat).sum ≤ ne
  vSum : ((vals.filter fun i => liveB st₀ E i.toNat).map fun i => V i.toNat).sum ≤ vb

/-- The pending activations of `st₀`. -/
def pendSum (st₀ : BeaconState) : Nat :=
  ((List.range st₀.validators.val.size).map fun i =>
    if pendingB st₀ i then ebN st₀ i else 0).sum

/-- The scheduled exits of `st₀` up to `E`. -/
def schedSum (st₀ : BeaconState) (E : Nat) : Nat :=
  ((List.range st₀.validators.val.size).map fun i =>
    if schedB st₀ E i then ebN st₀ i else 0).sum

/-- The distances of `st₀`'s capped balances from its effective balances. -/
def epsSum (st₀ : BeaconState) : Nat :=
  ((List.range st₀.validators.val.size).map fun i => eps0 st₀ i).sum

theorem laB_of_acB {u : BeaconState} {i : Nat} (h : acB u i = true) : laB u i = true := by
  unfold acB at h
  unfold laB
  cases hv : u.validators.val[i]? with
  | none => rw [hv] at h; cases h
  | some v => rw [hv] at h; simp [h]

omit [HasherTag] in
theorem ebN_eq_zero_of_ge {u : BeaconState} {i : Nat} (h : u.validators.val.size ≤ i) :
    ebN u i = 0 := by
  unfold ebN; rw [Array.getElem?_eq_none h]

omit [HasherTag] in
theorem eps0_eq_zero_of_ge {u : BeaconState} {i : Nat} (h : u.validators.val.size ≤ i) :
    eps0 u i = 0 := by
  unfold eps0 capN maxN
  rw [ebN_eq_zero_of_ge h, Array.getElem?_eq_none h]
  simp [absDiff]

section Pointwise
variable {vals : List ValidatorIndex} {st₀ u : BeaconState} {E A d : Nat} {V W : Nat → Nat}
  {vb ne : Nat}

/-- The EB term of one index. -/
def tEb (st₀ : BeaconState) (E A d : Nat) (V : Nat → Nat) (x : Nat) : Nat :=
  if liveB st₀ E x then abound A d (eps0 st₀ x + V x) else 0

/-- The set term of one index. -/
def tSet (st₀ u : BeaconState) (E A d : Nat) (V W : Nat → Nat) (x : Nat) : Nat :=
  (if pendingB st₀ x then ebN st₀ x else 0) + (if schedB st₀ E x then ebN st₀ x else 0) +
    (if newExitB st₀ u E x then W x + abound A d (eps0 st₀ x + V x) else 0)

/-- A gated EB distance is at most the EB term, once the gate of `u` gives a live index. -/
theorem gated_eb_le (F : EndFacts vals st₀ u E A d V W vb ne) {i : ValidatorIndex} (hi : i ∈ vals)
    (p : Bool) (hp : p = true → laB u i.toNat = true) :
    (if p then absDiff (ebN u i.toNat) (ebN st₀ i.toNat) else 0) ≤ tEb st₀ E A d V i.toNat := by
  cases p
  · exact Nat.zero_le _
  · have hl := F.laLive i hi (hp rfl)
    unfold tEb
    rw [if_pos hl]
    exact (F.track i hi hl).bound

/-- A change of a gate costs at most the set term. -/
theorem gate_change_le (F : EndFacts vals st₀ u E A d V W vb ne) {i : ValidatorIndex}
    (hi : i ∈ vals) (hch : laB u i.toNat ≠ laB st₀ i.toNat ∨ acB u i.toNat ≠ acB st₀ i.toNat) :
    ebN st₀ i.toNat ≤ tSet st₀ u E A d V W i.toNat := by
  by_cases h0 : ebN st₀ i.toNat = 0
  · rw [h0]; exact Nat.zero_le _
  · unfold tSet
    rcases F.gate i hi hch h0 with h | h | h
    · rw [if_pos h]; omega
    · rw [if_pos h]; omega
    · rw [if_pos h]
      have := (F.neEB i hi h).1
      omega

/-- The link stake distance of one index. -/
theorem link_le (F : EndFacts vals st₀ u E A d V W vb ne) {i : ValidatorIndex} (hi : i ∈ vals) :
    absDiff (linkStake u i) (linkStake st₀ i) ≤
      tEb st₀ E A d V i.toNat + tSet st₀ u E A d V W i.toNat := by
  rw [linkStake_eq, linkStake_eq]
  refine Nat.le_trans (absDiff_gate_le _ _ _ _) (Nat.add_le_add ?_ ?_)
  · exact gated_eb_le F hi _ id
  · split
    · exact Nat.zero_le _
    · rename_i hne
      exact gate_change_le F hi (.inl hne)

/-- The active-gate distance of one index. -/
theorem active_le (F : EndFacts vals st₀ u E A d V W vb ne) {i : ValidatorIndex} (hi : i ∈ vals) :
    absDiff (if acB u i.toNat then ebN u i.toNat else 0)
        (if acB st₀ i.toNat then ebN st₀ i.toNat else 0) ≤
      tEb st₀ E A d V i.toNat + tSet st₀ u E A d V W i.toNat := by
  refine Nat.le_trans (absDiff_gate_le _ _ _ _) (Nat.add_le_add ?_ ?_)
  · exact gated_eb_le F hi _ laB_of_acB
  · split
    · exact Nat.zero_le _
    · rename_i hne
      exact gate_change_le F hi (.inr hne)

end Pointwise

omit [Preset] [HasherTag] in
/-- The superadditivity of `abound`. -/
theorem sum_abound_le {α : Type} (A d : Nat) (f : α → Nat) :
    ∀ l : List α, (l.map fun x => abound A d (f x)).sum ≤ abound A d (l.map f).sum := by
  intro l
  unfold abound
  rw [sum_map_add]
  have h1 := sum_map_div_le (fun x => A * f x) (d + 1) l
  rw [sum_map_mul_left] at h1
  omega

/-- **The drift from the facts at the end of a run.** -/
theorem drift_le_of_endFacts {vals : List ValidatorIndex} {st₀ u : BeaconState} {E A d : Nat}
    {V W : Nat → Nat} {vb ne : Nat} (F : EndFacts vals st₀ u E A d V W vb ne) :
    drift vals st₀ u ≤ EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat +
      4 * abound A d (epsSum st₀ + vb) + 2 * (pendSum st₀ + schedSum st₀ E + ne) := by
  let te := fun i : ValidatorIndex => tEb st₀ E A d V i.toNat
  let ts := fun i : ValidatorIndex => tSet st₀ u E A d V W i.toNat
  -- The link-stake part.
  have hlink : EthCLLib.Proofs.FFG.absDiffSum (linkStake u) (linkStake st₀) vals ≤
      (vals.map te).sum + (vals.map ts).sum := by
    unfold EthCLLib.Proofs.FFG.absDiffSum
    rw [← sum_map_add]
    exact sum_map_le_sum_map_mem _ _ _ fun i hi => link_le F hi
  -- The total part: the floor of `st₀` costs one increment, and the rest is a gated sum.
  let a₀ : Nat → Nat := fun x => if acB st₀ x then ebN st₀ x else 0
  let aᵤ : Nat → Nat := fun x => if acB u x then ebN u x else 0
  have ht₀ := totalActive_toNat st₀ F.sum₀ F.h64₀
  have htu := totalActive_toNat u F.sumu F.h64u
  have hr₀ : ((List.range st₀.validators.val.size).map a₀).sum ≤ (vals.map fun i => a₀ i.toNat).sum :=
    sum_range_le_vals vals a₀ _ (Nat.le_of_lt F.h64₀) F.cover
  have hru : (vals.map fun i => aᵤ i.toNat).sum ≤ ((List.range u.validators.val.size).map aᵤ).sum :=
    sum_vals_le_range vals F.nodup aᵤ _ fun x hx => by
      simp only [aᵤ]
      unfold acB
      rw [Array.getElem?_eq_none hx]
      rfl
  have hdiff := sum_le_add_absDiff (fun i : ValidatorIndex => a₀ i.toNat)
    (fun i : ValidatorIndex => aᵤ i.toNat) vals
  have hact : (vals.map fun i => absDiff (aᵤ i.toNat) (a₀ i.toNat)).sum ≤
      (vals.map te).sum + (vals.map ts).sum := by
    rw [← sum_map_add]
    exact sum_map_le_sum_map_mem _ _ _ fun i hi => active_le F hi
  have htot : (totBal st₀).toNat - (totBal u).toNat ≤
      EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat +
        ((vals.map te).sum + (vals.map ts).sum) := by
    rw [ht₀, htu]
    simp only [a₀, aᵤ] at hr₀ hru hdiff hact
    omega
  -- The EB terms and the set terms over `vals`.
  have hte : (vals.map te).sum ≤ abound A d (epsSum st₀ + vb) := by
    have h1 : (vals.map te).sum = ((vals.filter fun i => liveB st₀ E i.toNat).map fun i =>
        abound A d (eps0 st₀ i.toNat + V i.toNat)).sum := by
      rw [sum_filter_eq_sum_ite]
      rfl
    have h2 := sum_abound_le A d (fun i : ValidatorIndex => eps0 st₀ i.toNat + V i.toNat)
      (vals.filter fun i => liveB st₀ E i.toNat)
    rw [sum_map_add] at h2
    have h3 : ((vals.filter fun i => liveB st₀ E i.toNat).map fun i => eps0 st₀ i.toNat).sum ≤
        epsSum st₀ :=
      sum_vals_le_range _ (F.nodup.filter _) (eps0 st₀) _ fun x hx => eps0_eq_zero_of_ge hx
    have h4 := F.vSum
    have hmono : ∀ x y, x ≤ y → abound A d x ≤ abound A d y := fun x y hxy => by
      unfold abound
      exact Nat.add_le_add hxy (Nat.div_le_div_right (Nat.mul_le_mul_left _ hxy))
    rw [h1]
    exact Nat.le_trans h2 (hmono _ _ (by omega))
  have hts : (vals.map ts).sum ≤ pendSum st₀ + schedSum st₀ E + ne +
      abound A d (epsSum st₀ + vb) := by
    have hsplit : (vals.map ts).sum = (vals.map fun i => if pendingB st₀ i.toNat then
        ebN st₀ i.toNat else 0).sum + (vals.map fun i => if schedB st₀ E i.toNat then
        ebN st₀ i.toNat else 0).sum + (vals.map fun i => if newExitB st₀ u E i.toNat then
        W i.toNat + abound A d (eps0 st₀ i.toNat + V i.toNat) else 0).sum := by
      rw [← sum_map_add, ← sum_map_add]
      rfl
    have hp : (vals.map fun i => if pendingB st₀ i.toNat then ebN st₀ i.toNat else 0).sum ≤
        pendSum st₀ :=
      sum_vals_le_range vals F.nodup (fun x => if pendingB st₀ x then ebN st₀ x else 0) _
        fun x hx => by simp [ebN_eq_zero_of_ge hx]
    have hs : (vals.map fun i => if schedB st₀ E i.toNat then ebN st₀ i.toNat else 0).sum ≤
        schedSum st₀ E :=
      sum_vals_le_range vals F.nodup (fun x => if schedB st₀ E x then ebN st₀ x else 0) _
        fun x hx => by simp [ebN_eq_zero_of_ge hx]
    -- The new exits: their recorded balances, and their EB terms among the live indices.
    have hn : (vals.map fun i => if newExitB st₀ u E i.toNat then
        W i.toNat + abound A d (eps0 st₀ i.toNat + V i.toNat) else 0).sum ≤
        ne + (vals.map te).sum := by
      have e1 : (vals.map fun i => if newExitB st₀ u E i.toNat then
          W i.toNat + abound A d (eps0 st₀ i.toNat + V i.toNat) else 0).sum =
          ((vals.filter fun i => newExitB st₀ u E i.toNat).map fun i => W i.toNat).sum +
          (vals.map fun i => if newExitB st₀ u E i.toNat then
            abound A d (eps0 st₀ i.toNat + V i.toNat) else 0).sum := by
        rw [sum_filter_eq_sum_ite, ← sum_map_add]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split <;> simp
      have e2 : (vals.map fun i => if newExitB st₀ u E i.toNat then
          abound A d (eps0 st₀ i.toNat + V i.toNat) else 0).sum ≤ (vals.map te).sum := by
        refine sum_map_le_sum_map_mem _ _ _ fun i hi => ?_
        split
        · rename_i h
          simp only [te, tEb, if_pos (F.neEB i hi h).2]
          exact Nat.le_refl _
        · exact Nat.zero_le _
      have := F.neSum
      omega
    omega
  unfold drift
  omega

end

end EthCLSpecs.Proofs.Heze
