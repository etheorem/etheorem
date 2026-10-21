import EthCLSpecs.Proofs.Heze.RunVotes
import EthCLLib.Proofs.IndicesWhere

/-!
# `EthCLSpecs.Proofs.Heze.TargetStake`: the target balance as a sum of stake

The weigh step compares the target balance of an epoch with the total active balance
(`tgtBal`, `totBal`, `RunWeighs.lean`). The target balance is `get_total_balance` of the
unslashed participating indices: a checked `uint64` sum of effective balances, with a floor of
`EFFECTIVE_BALANCE_INCREMENT`. This module turns a passed test into a `Nat` bound on a sum of
stake, as the FFG model reads it.

- `getUnslashedParticipatingIndices_ok_toList`: a successful read of the indices returns a
  filter of the active indices. Each one is active at the epoch, unslashed, and has its target
  flag (`mem_participating`). They are distinct.
- `getTotalBalance_ok_toNat`: a successful balance sum is the `Nat` sum of the effective
  balances, or the floor. Its checked additions did not overflow.
- `RunTotals u`: the premises on the totals of a state. The floor does not apply to two
  thirds of the total. Three times the sum of all effective balances fits a `uint64`, and so
  does the size of the registry. The weigh step multiplies a balance by three, so the factor
  three keeps that product in range. Under them, a successful read of the counted indices
  gives the target balance as the `Nat` sum of their effective balances, or the floor
  (`tgtBal_toNat`).
- `linkStake u i`: the effective balance of `i` in `u` when `i` is active at the current or the
  previous epoch of `u`, else zero. The previous-epoch test counts validators active at the
  previous epoch against the total of the current epoch, so a validator that exits at the
  current epoch still counts.
- `link_weight`: a passed test bounds the `linkStake` sum over any list that holds every
  counted index.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Epoch ValidatorIndex Validator
  currentEpochOf previousEpochOf isActiveValidator)

/-! ## Sums over lists -/

/-- A sum over a list without duplicates is at most the sum over a list that holds its
elements. -/
theorem sum_map_le_of_subset {α : Type} [DecidableEq α] (f : α → Nat) :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → (l₁.map f).sum ≤ (l₂.map f).sum
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hnd, hsub => by
    have ha : a ∈ l₂ := hsub a List.mem_cons_self
    have hp := ((List.perm_cons_erase ha).map f).sum_nat
    rw [hp, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    obtain ⟨hat, htnd⟩ := List.nodup_cons.mp hnd
    refine Nat.add_le_add_left (sum_map_le_of_subset f t (l₂.erase a) htnd fun x hx => ?_) _
    exact (List.mem_erase_of_ne (fun he => hat (by rw [← he]; exact hx))).mpr
      (hsub x (List.mem_cons_of_mem _ hx))

/-- A `uint64` fold of sums is the `Nat` sum when the `Nat` sum fits. -/
theorem foldl_add_toNat {α : Type} (f : α → UInt64) :
    ∀ (l : List α) (a : UInt64), a.toNat + (l.map fun x => (f x).toNat).sum < 2 ^ 64 →
      (l.foldl (fun acc x => acc + f x) a).toNat = a.toNat + (l.map fun x => (f x).toNat).sum
  | [], a, _ => by simp
  | x :: l, a, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at h ⊢
    have h1 : a.toNat + (f x).toNat < 2 ^ 64 := by omega
    rw [foldl_add_toNat f l (a + f x) (by rw [UInt64.toNat_add, Nat.mod_eq_of_lt h1]; omega),
      UInt64.toNat_add, Nat.mod_eq_of_lt h1]
    omega

/-- `umax` is the larger value. -/
theorem umax_toNat (a b : UInt64) : (umax a b).toNat = max a.toNat b.toNat := by
  unfold umax
  split
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt] at h
    omega
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt] at h
    omega

/-- A successful `mapM` over a list in `Except` maps `g`, when each successful step returns
`g` of its element. -/
theorem list_mapM_ok_eq {ε α β : Type} {f : α → Except ε β} {g : α → β}
    (hf : ∀ a b, f a = .ok b → b = g a) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r = l.map g
  | [], r, h => by
    rw [List.mapM_nil] at h
    injection h with h
    exact h.symm
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_eq_ok h
    obtain ⟨bs, hbs, h⟩ := except_bind_eq_ok h
    injection h with h
    rw [← h, hf a b hb, list_mapM_ok_eq hf l bs hbs]
    rfl

/-- A `mapM` over a list in `Except` whose steps succeed on its elements returns the map. -/
theorem list_mapM_ok_of {ε α β : Type} {f : α → Except ε β} {g : α → β} :
    ∀ l : List α, (∀ a ∈ l, f a = .ok (g a)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self,
      list_mapM_ok_of l fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

/-- Two `mapM` runs over one list in `Except` agree when their steps agree on its elements. -/
theorem list_mapM_congr {ε α β : Type} {f g : α → Except ε β} :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
      list_mapM_congr l fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- A checked sum over a list succeeds when the `Nat` sum fits a `uint64`. -/
theorem list_foldlM_checkedAdd_ok_of {d : String} :
    ∀ (l : List UInt64) (a : UInt64), a.toNat + (l.map UInt64.toNat).sum < 2 ^ 64 →
      l.foldlM (fun acc b => (checkedAdd acc b d : Except StateTransitionError UInt64)) a
        = .ok (UInt64.ofNat (a.toNat + (l.map UInt64.toNat).sum))
  | [], a, _ => by
    rw [List.foldlM_nil]
    simp only [List.map_nil, List.sum_nil, Nat.add_zero, UInt64.ofNat_toNat]
    rfl
  | x :: l, a, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have h1 : a.toNat + x.toNat < 2 ^ 64 := by omega
    have hax : (a + x).toNat = a.toNat + x.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt h1]
    have hno : ¬ (a + x < a) := by
      rw [UInt64.lt_iff_toNat_lt, hax]
      omega
    have hca : (checkedAdd a x d : Except StateTransitionError UInt64) = pure (a + x) := by
      unfold checkedAdd
      rw [if_neg hno]
    rw [List.foldlM_cons, hca, pure_bind,
      list_foldlM_checkedAdd_ok_of l (a + x) (by rw [hax]; omega), hax, Nat.add_assoc]

/-- A successful `filterAuxM` over a list in `Except`. Each successful test returns `g` of
its element, so the result is the filter by `g`, reversed, before the accumulator. -/
theorem list_filterAuxM_ok {ε α : Type} {p : α → Except ε Bool} {g : α → Bool}
    (hp : ∀ a b, p a = .ok b → b = g a) :
    ∀ (l acc r : List α), List.filterAuxM p l acc = .ok r → r = (l.filter g).reverse ++ acc
  | [], acc, r, h => by
    simp only [List.filterAuxM] at h
    injection h with h
    rw [← h]
    rfl
  | a :: l, acc, r, h => by
    simp only [List.filterAuxM] at h
    obtain ⟨b, hb, h⟩ := except_bind_eq_ok h
    rw [list_filterAuxM_ok hp l _ r h, hp a b hb]
    cases hg : g a <;> simp [hg]

/-- A successful `filterM` over a list in `Except` is the filter by `g`, when each successful
test returns `g` of its element. -/
theorem list_filterM_ok {ε α : Type} {p : α → Except ε Bool} {g : α → Bool}
    (hp : ∀ a b, p a = .ok b → b = g a) (l r : List α) (h : l.filterM p = .ok r) :
    r = l.filter g := by
  unfold List.filterM at h
  obtain ⟨r', hr', h⟩ := except_bind_eq_ok h
  injection h with h
  rw [← h, list_filterAuxM_ok hp l [] r' hr', List.append_nil, List.reverse_reverse]

/-- A successful checked sum over a list adds the `Nat` values: no step overflowed. -/
theorem list_foldlM_checkedAdd_ok {d : String} :
    ∀ (l : List UInt64) (a r : UInt64),
      l.foldlM (fun acc b => (checkedAdd acc b d : Except StateTransitionError UInt64)) a
        = .ok r → r.toNat = a.toNat + (l.map UInt64.toNat).sum
  | [], a, r, h => by
    rw [List.foldlM_nil] at h
    injection h with h
    rw [← h]
    simp
  | x :: l, a, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s, hs, h⟩ := except_bind_eq_ok h
    unfold checkedAdd at hs
    split at hs
    · unfold throwArithmetic at hs
      cases hs
    · rename_i hno
      injection hs with hs
      subst hs
      rw [list_foldlM_checkedAdd_ok l _ r h, EthCLLib.Proofs.toNat_add_of_not_lt _ _ hno,
        List.map_cons, List.sum_cons]
      omega

/-- A loop over a list that pushes the elements that pass `p` is a filter. -/
theorem forIn_push_filter_list {α : Type} (p : α → Bool) :
    ∀ (l : List α) (acc : Array α),
      (forIn (m := Id) l acc fun i r =>
        if p i = true then pure (ForInStep.yield (r.push i)) else pure (ForInStep.yield r)).toList =
        acc.toList ++ l.filter p
  | [], acc => (List.append_nil _).symm
  | i :: l, acc => by
    by_cases h : p i = true <;>
      simp [List.forIn_cons, h, forIn_push_filter_list p l]

section
variable [Preset] [HasherTag]

omit [Preset] [HasherTag] in
/-- The read of an `SSZList` is the read of its array. -/
theorem sszList_getElem!_eq {α : Type} [Inhabited α] {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) : xs[i]! = xs.val[i]! := by
  by_cases h : i < xs.val.size
  · rw [getElem!_pos xs i h, getElem!_pos xs.val i h]
    rfl
  · rw [getElem!_neg xs i h, getElem!_neg xs.val i h]

/-- A successful read of the unslashed participating indices: the active indices with the
flag and without the slashing. The flag reads went through `sszGetIdx`, so they read the
entries that the list holds. -/
theorem getUnslashedParticipatingIndices_ok_toList {u : BeaconState} {flag : Nat} {e : Epoch}
    {idx : Array ValidatorIndex}
    (h : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u) flag e = .ok idx) :
    idx.toList =
      (EthCLSpecs.Heze.getActiveValidatorIndices (pureState u) e).toList.filter fun i =>
        hasFlag ((if (e == currentEpochOf (pureState u)) = true then u.currentEpochParticipation
          else u.previousEpochParticipation)[i.toNat]!) flag &&
        !(u.validators[i.toNat]!).slashed := by
  unfold EthCLSpecs.Heze.getUnslashedParticipatingIndices at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨parts, hparts, h⟩ := except_bind_eq_ok h
  injection h with h
  subst h
  -- The flag test reads each entry through `sszGetIdx`. A successful read is the entry.
  have hl := congrArg (Functor.map Array.toList) hparts
  rw [Array.toList_filterM] at hl
  have hp := list_filterM_ok (g := fun i : ValidatorIndex => hasFlag
      ((if (e == currentEpochOf (pureState u)) = true then u.currentEpochParticipation
        else u.previousEpochParticipation)[i.toNat]!) flag)
    (fun i b hb => by
      obtain ⟨fl, hfl, hb⟩ := except_bind_eq_ok hb
      injection hb with hb
      rw [← hb]
      unfold sszGetIdx liftErr at hfl
      split at hfl
      · rename_i y hy
        injection hfl with hfl
        subst hfl
        -- `hy` reads the list of the box, which is the list of `u`.
        have hy' : (if (e == currentEpochOf (pureState u)) = true then
            u.currentEpochParticipation else u.previousEpochParticipation).val[i.toNat]?
            = some y := hy
        dsimp only
        rw [sszList_getElem!_eq, getElem!_def]
        simp only [hy']
      · cases hfl) _ _ hl
  rw [Array.toList_filter, hp, List.filter_filter]
  congr 1
  funext i
  rw [Bool.and_comm]
  -- The slashed test reads the registry of the box, which is the registry of `u`.
  rfl

/-- The effective balance at `i` in `u`, or `0` past the registry. -/
def effBal (u : BeaconState) (i : ValidatorIndex) : Nat :=
  (u.validators.val[i.toNat]!).effectiveBalance.toNat

/-- A successful balance sum is the `Nat` sum of the effective balances, or the floor
`EFFECTIVE_BALANCE_INCREMENT`. The reads went through `sszGetIdx`, and the additions are
checked. -/
theorem getTotalBalance_ok_toNat {u : BeaconState} {idx : Array ValidatorIndex}
    {g : EthCLSpecs.Heze.Gwei}
    (h : EthCLSpecs.Heze.getTotalBalance (pureState u) idx = .ok g) :
    g.toNat = max ((idx.toList.map (effBal u)).sum)
      EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat := by
  unfold EthCLSpecs.Heze.getTotalBalance at h
  obtain ⟨bals, hbals, h⟩ := except_bind_eq_ok h
  obtain ⟨total, htotal, h⟩ := except_bind_eq_ok h
  injection h with h
  subst h
  -- The reads of the effective balances.
  rw [Array.mapM_eq_mapM_toList] at hbals
  obtain ⟨l, hl, hb⟩ := except_map_eq_ok hbals
  have hl' := list_mapM_ok_eq (g := fun i : ValidatorIndex =>
      (u.validators.val[i.toNat]!).effectiveBalance)
    (fun i b hb' => by
      obtain ⟨v, hv, hb'⟩ := except_bind_eq_ok hb'
      injection hb' with hb'
      rw [← hb']
      unfold sszGetIdx liftErr at hv
      split at hv
      · rename_i y hy
        injection hv with hv
        subst hv
        -- `hy` reads the registry of the box, which is the registry of `u`.
        have hy' : u.validators.val[i.toNat]? = some y := hy
        simp only [getElem!_def, hy']
      · cases hv) _ _ hl
  subst hb
  -- The checked sum.
  rw [← Array.foldlM_toList] at htotal
  have hs := list_foldlM_checkedAdd_ok _ _ _ htotal
  rw [umax_toNat, hs, hl']
  simp only [UInt64.toNat_zero, Nat.zero_add, List.map_map]
  rfl

/-- A balance sum over registry indices succeeds when the `Nat` sum of their effective
balances fits a `uint64`. It returns that sum, or the floor. -/
theorem getTotalBalance_ok_of {u : BeaconState} {idx : Array ValidatorIndex}
    (hin : ∀ i ∈ idx.toList, i.toNat < u.validators.val.size)
    (hsum : (idx.toList.map (effBal u)).sum < 2 ^ 64) :
    EthCLSpecs.Heze.getTotalBalance (pureState u) idx =
      .ok (umax (UInt64.ofNat (idx.toList.map (effBal u)).sum)
        EthCLSpecs.Heze.Const.effectiveBalanceIncrementG) := by
  unfold EthCLSpecs.Heze.getTotalBalance
  dsimp only
  -- Each read is in range, so it returns the effective balance.
  rw [Array.mapM_eq_mapM_toList, list_mapM_ok_of (g := fun i : ValidatorIndex =>
    (u.validators.val[i.toNat]!).effectiveBalance) idx.toList fun i hi => by
      have hy : u.validators.val[i.toNat]? = some u.validators.val[i.toNat]! := by
        rw [getElem!_pos u.validators.val i.toNat (hin i hi),
          getElem?_pos u.validators.val i.toNat (hin i hi)]
      unfold sszGetIdx liftErr
      rw [show (pureState u).view.validators.val[i.toNat]? = _ from hy]
      rfl]
  -- The checked sum does not overflow.
  rw [show ∀ l : List EthCLSpecs.Heze.Gwei,
      (List.toArray <$> (Except.ok l : Except StateTransitionError (List EthCLSpecs.Heze.Gwei)))
        = Except.ok l.toArray from fun _ => rfl, EthCLLib.Proofs.except_bind_ok]
  rw [← Array.foldlM_toList, List.toList_toArray, list_foldlM_checkedAdd_ok_of _ _ (by
    simpa [List.map_map, Function.comp_def, effBal] using hsum)]
  simp only [List.map_map, Function.comp_def, UInt64.toNat_zero, Nat.zero_add]
  rfl

/-- The premises on the totals of a state. Two thirds of the total active balance is above
the floor `EFFECTIVE_BALANCE_INCREMENT` of `get_total_balance`. Three times the sum of all
effective balances fits a `uint64`, and so does the size of the registry. -/
def RunTotals (u : BeaconState) : Prop :=
  3 * EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat < 2 * (totBal u).toNat ∧
  3 * (u.validators.val.toList.map (·.effectiveBalance.toNat)).sum < 2 ^ 64 ∧
  u.validators.val.size < 2 ^ 64

/-- The effective balance of `i` in `u` when `i` is active at the current or the previous
epoch of `u`, else zero. -/
def linkStake (u : BeaconState) (i : ValidatorIndex) : Nat :=
  match u.validators.val[i.toNat]? with
  | some v =>
    if isActiveValidator v (currentEpochOf (pureState u)) ||
        isActiveValidator v (previousEpochOf (pureState u)) then v.effectiveBalance.toNat
    else 0
  | none => 0

omit [Preset] [HasherTag] in
/-- A sum over the indices below the size of an array is the sum over the array. -/
theorem sum_range_getElem! {α : Type} [Inhabited α] (xs : Array α) (f : α → Nat) :
    ((List.range xs.size).map fun i => f xs[i]!).sum = (xs.toList.map f).sum := by
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [getElem!_pos xs n h1]

/-- The active indices at `e`: a filter over the registry indices, cast to `uint64`. -/
theorem getActiveValidatorIndices_toList (u : BeaconState) (e : Epoch) :
    (EthCLSpecs.Heze.getActiveValidatorIndices (pureState u) e).toList =
      ((List.range u.validators.val.size).filter fun i =>
        isActiveValidator u.validators.val[i]! e).map UInt64.ofNat :=
  EthCLLib.Proofs.indicesWhere_toList _ _

/-- A counted index of a successful read is a registry index, active at the epoch, with the
flag. -/
theorem mem_participating {u : BeaconState} {flag : Nat} {e : Epoch} {x : ValidatorIndex}
    {idx : Array ValidatorIndex}
    (hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u) flag e = .ok idx)
    (h64 : u.validators.val.size < 2 ^ 64) (hx : x ∈ idx.toList) :
    x.toNat < u.validators.val.size ∧ isActiveValidator u.validators.val[x.toNat]! e = true ∧
      hasFlag ((if (e == currentEpochOf (pureState u)) = true then u.currentEpochParticipation
        else u.previousEpochParticipation)[x.toNat]!) flag = true := by
  rw [getUnslashedParticipatingIndices_ok_toList hidx, List.mem_filter,
    getActiveValidatorIndices_toList, List.mem_map] at hx
  obtain ⟨⟨i, hi, rfl⟩, hf⟩ := hx
  obtain ⟨hi, ha⟩ := List.mem_filter.mp hi
  have hi' := List.mem_range.mp hi
  have hc : (UInt64.ofNat i).toNat = i := EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)
  rw [hc] at hf ⊢
  rw [Bool.and_eq_true] at hf
  exact ⟨hi', of_decide_eq_true (by simpa using ha), hf.1⟩

/-- A counted index of the current or the previous epoch has its target flag set. -/
theorem targetFlag_of_participating {u : BeaconState} {e : Epoch} {x : ValidatorIndex}
    {idx : Array ValidatorIndex}
    (hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e = .ok idx)
    (h64 : u.validators.val.size < 2 ^ 64)
    (he : e = currentEpochOf (pureState u) ∨ e = previousEpochOf (pureState u))
    (hx : x ∈ idx.toList) :
    TargetFlagSet u x.toNat e := by
  obtain ⟨-, -, hf⟩ := mem_participating hidx h64 hx
  by_cases hc : e = currentEpochOf (pureState u)
  · rw [if_pos (by simp [hc])] at hf
    exact .inl ⟨hc, hf⟩
  · rw [if_neg (by simpa using hc)] at hf
    rcases he with he | he
    · exact absurd he hc
    · exact .inr ⟨he, hc, hf⟩

/-- The counted indices of a successful read are distinct. -/
theorem participating_nodup {u : BeaconState} {flag : Nat} {e : Epoch}
    {idx : Array ValidatorIndex}
    (hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u) flag e = .ok idx)
    (h64 : u.validators.val.size < 2 ^ 64) : idx.toList.Nodup := by
  rw [getUnslashedParticipatingIndices_ok_toList hidx]
  exact (EthCLLib.Proofs.indicesWhere_nodup _ _ (Nat.le_of_lt h64)).filter _

/-- Under `RunTotals`, a successful read of the counted indices gives the target balance as the
`Nat` sum of their effective balances, or the floor `EFFECTIVE_BALANCE_INCREMENT`. The balance
sum succeeds, since each counted index is in range and the sum fits a `uint64`. -/
theorem tgtBal_toNat {u : BeaconState} (ht : RunTotals u) {e : Epoch}
    {idx : Array ValidatorIndex}
    (hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e = .ok idx) :
    (tgtBal u e).toNat = max ((idx.toList.map (effBal u)).sum)
      EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat := by
  obtain ⟨-, hsum, h64⟩ := ht
  let g : Nat → Nat := fun i => (u.validators.val[i]!).effectiveBalance.toNat
  -- The sum over the counted indices is at most the sum over the registry.
  have hle : (idx.toList.map (effBal u)).sum ≤
      (u.validators.val.toList.map (·.effectiveBalance.toNat)).sum := by
    rw [← sum_range_getElem! u.validators.val,
      show idx.toList.map (effBal u) = (idx.toList.map UInt64.toNat).map g by
        rw [List.map_map]; rfl]
    refine sum_map_le_of_subset g _ _ ?_ fun i hi => ?_
    · exact EthCLLib.Proofs.nodup_map_of_injOn (participating_nodup hidx h64)
        fun a _ b _ hab => UInt64.toNat_inj.mp hab
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
      exact List.mem_range.mpr (mem_participating hidx h64 hx).1
  have hg := getTotalBalance_ok_of (u := u) (idx := idx)
    (fun i hi => (mem_participating hidx h64 hi).1) (by omega)
  rw [tgtBal_of_ok hidx hg, getTotalBalance_ok_toNat hg]

/-- Under `RunTotals`, a passed test bounds the `linkStake` sum over a list that holds every
counted index. When a read of the target balance faults, `tgtBal` is `0`, and the floor
premise rules the test out. Else the target balance is the `Nat` sum, above the floor, and each
counted index is active at the current or the previous epoch. -/
theorem link_weight {u : BeaconState} (ht : RunTotals u) {e : Epoch}
    (he : e = currentEpochOf (pureState u) ∨ e = previousEpochOf (pureState u))
    (htest : (tgtBal u e).toNat * 3 ≥ (totBal u).toNat * 2)
    (L : List ValidatorIndex)
    (hL : ∀ idx, EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e = .ok idx → ∀ x ∈ idx.toList, x ∈ L) :
    3 * (L.map (linkStake u)).sum ≥ 2 * (totBal u).toNat := by
  obtain ⟨hfl, -, h64⟩ := ht
  -- A fault in either read gives the target balance `0`, below two thirds of the total.
  unfold tgtBal at htest
  cases hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
    EthCLSpecs.Heze.Const.timelyTargetFlagIndex e with
  | error err =>
    rw [hidx] at htest
    simp at htest
    omega
  | ok idx =>
  rw [hidx] at htest
  dsimp only at htest
  cases hg : EthCLSpecs.Heze.getTotalBalance (pureState u) idx with
  | error err =>
    rw [hg] at htest
    simp at htest
    omega
  | ok g =>
  rw [hg] at htest
  dsimp only at htest
  -- The target balance is the `Nat` sum of the counted effective balances, or the floor.
  have htgt := getTotalBalance_ok_toNat hg
  -- Each counted index has its effective balance as its link stake.
  have hst : (idx.toList.map (effBal u)).sum = (idx.toList.map (linkStake u)).sum := by
    congr 1
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨hb, ha, -⟩ := mem_participating hidx h64 hx
    unfold linkStake effBal
    rw [getElem?_pos u.validators.val x.toNat hb]
    dsimp only
    rw [if_pos]
    · rw [getElem!_pos u.validators.val x.toNat hb]
    · rw [getElem!_pos u.validators.val x.toNat hb] at ha
      rcases he with rfl | rfl <;> simp [ha]
  have hsub := sum_map_le_of_subset (linkStake u) idx.toList L (participating_nodup hidx h64)
    (hL idx hidx)
  rw [htgt] at htest
  omega

end

end EthCLSpecs.Proofs.Heze
