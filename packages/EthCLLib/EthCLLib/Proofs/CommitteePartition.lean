import EthCLLib.Proofs.Lemmas

/-!
# `EthCLLib.Proofs.CommitteePartition`: committee slices cover the shuffled list once

`compute_committee` (`phase0/beacon-chain.md:881-892`) takes committee `k` of `c`
as the slice `[len * k / c, len * (k + 1) / c)` of the shuffled index list.
`slices_flatMap` states that the `c` slices, laid end to end, are `[0, len)`.
`committeeSlice_partition` adds the shuffle. If slot `p` of `perm` reads a
bijection `σ`, the committees together are a permutation of `indices`.

An epoch's committees are indexed by a slot offset `j` and a per-slot index
`idx`. `flatMap_range_mul` turns the pair `(j, idx)` into the committee number
`j * cps + idx`. `epochSlot_div` and `epochSlot_mod` recover `e` and `j` from the
spec's slot `compute_start_slot_at_epoch(e) + j`, written `e * spe + j`.
`epoch_partition` and `epoch_nodup` then state the epoch-level result once, for
any committee function the fork bridges tie to `committeeSlice`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

/-- The fork bodies' `compute_committee`, with the permutation array passed in. -/
def committeeSlice (indices perm : Array UInt64) (index count : Nat) : Array UInt64 :=
  let len := indices.size
  let start := len * index / count
  let stop := len * (index + 1) / count
  (Array.range (stop - start)).map (fun j => indices[(perm[start + j]!).toNat]!)


/-- The first `k` slices, laid end to end, are `[0, len * k / c)`. -/
private theorem slices_prefix (len c : Nat) (k : Nat) :
    (List.range k).flatMap (fun m =>
        List.range' (len * m / c) (len * (m + 1) / c - len * m / c)) =
      List.range (len * k / c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono : len * k / c ≤ len * (k + 1) / c :=
      Nat.div_le_div_right (Nat.mul_le_mul_left len (Nat.le_succ k))
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
      List.range_eq_range', List.range_eq_range']
    -- `range'_append_1` joins two adjacent runs. Its second run starts at `0 + m`.
    have happ := List.range'_append_1 (s := 0) (m := len * k / c)
      (n := len * (k + 1) / c - len * k / c)
    rw [Nat.zero_add] at happ
    rw [happ]
    congr 1
    omega

/-- The `c` slices of `[0, len)`, laid end to end, are `[0, len)`. -/
theorem slices_flatMap (len c : Nat) (hc : 0 < c) :
    (List.range c).flatMap (fun k =>
        List.range' (len * k / c) (len * (k + 1) / c - len * k / c)) =
      List.range len := by
  rw [slices_prefix, Nat.mul_div_cancel _ hc]

/-- A double walk over `j < a` and `i < b` is one walk over `j * b + i < a * b`. -/
theorem flatMap_range_mul {β : Type} (a b : Nat) (f : Nat → List β) :
    (List.range a).flatMap (fun j => (List.range b).flatMap (fun i => f (j * b + i))) =
      (List.range (a * b)).flatMap f := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
      Nat.succ_mul, List.range_add, List.flatMap_append, List.flatMap_map]

/-- The `c` committee slices together are a permutation of `indices`, when
`perm` reads a bijection `σ` of `[0, indices.size)`. -/
theorem committeeSlice_partition (indices perm : Array UInt64) (c : Nat) (hc : 0 < c)
    (σ : Nat → Nat)
    (hperm : ((List.range indices.size).map σ).Perm (List.range indices.size))
    (hget : ∀ p, p < indices.size → (perm[p]!).toNat = σ p) :
    ((List.range c).flatMap (fun k => (committeeSlice indices perm k c).toList)).Perm
      indices.toList := by
  let g : Nat → UInt64 := fun p => indices[σ p]!
  -- 1. Each committee is its slice of `[0, len)`, read through `σ`.
  have hslice : ∀ k ∈ List.range c, (committeeSlice indices perm k c).toList =
      (List.range' (indices.size * k / c)
        (indices.size * (k + 1) / c - indices.size * k / c)).map g := by
    intro k hk
    have hkc := List.mem_range.mp hk
    have hstop : indices.size * (k + 1) / c ≤ indices.size :=
      Nat.div_le_of_le_mul (by
        rw [Nat.mul_comm c indices.size]; exact Nat.mul_le_mul_left _ hkc)
    simp only [committeeSlice, Array.toList_map, Array.toList_range, List.map_map,
      List.range'_eq_map_range]
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    have hlt : indices.size * k / c + j < indices.size := by omega
    simp [g, hget _ hlt]
  rw [flatMap_congr_mem hslice]
  -- 2. The slices laid end to end are `[0, len)`.
  rw [← List.map_flatMap, slices_flatMap indices.size c hc]
  -- 3. `σ` permutes `[0, len)`, and reading `indices` over `[0, len)` is `indices`.
  have hself : (List.range indices.size).map (fun p => indices[p]!) = indices.toList := by
    apply List.ext_getElem
    · simp
    · intro i h1 _
      simp only [List.length_map, List.length_range] at h1
      simp [getElem!_pos, h1]
  rw [← hself, show (List.range indices.size).map g =
      ((List.range indices.size).map σ).map (fun p => indices[p]!) by simp [g, List.map_map]]
  exact hperm.map _

/-! ## Slots of an epoch

The spec writes slot `j` of epoch `e` as `compute_start_slot_at_epoch(e) + j`,
which the fork bodies compute as `e * spe + j` in `UInt64`. `hov` keeps the
epoch's last slot below `2 ^ 64`, so neither operation wraps. -/

/-- Slot `j` of epoch `e` does not wrap. -/
theorem epochSlot_toNat {e : UInt64} {spe j : Nat} (hj : j < spe) (hspe : spe < 2 ^ 64)
    (hov : (e.toNat + 1) * spe ≤ 2 ^ 64) :
    (e * UInt64.ofNat spe + UInt64.ofNat j).toNat = e.toNat * spe + j := by
  have hslot : e.toNat * spe + j < 2 ^ 64 := by rw [Nat.succ_mul] at hov; omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, toNat_ofNat_lt64 hspe,
    toNat_ofNat_lt64 (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : e.toNat * spe < 2 ^ 64),
    Nat.mod_eq_of_lt hslot]

/-- Slot `j` of epoch `e`, divided by the slots per epoch, is `e`. -/
theorem epochSlot_div {e : UInt64} {spe j : Nat} (hj : j < spe) (hspe : spe < 2 ^ 64)
    (hov : (e.toNat + 1) * spe ≤ 2 ^ 64) :
    (e * UInt64.ofNat spe + UInt64.ofNat j) / UInt64.ofNat spe = e := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, epochSlot_toNat hj hspe hov, toNat_ofNat_lt64 hspe,
    Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]

/-- Slot `j` of epoch `e`, mod the slots per epoch, is `j`. -/
theorem epochSlot_mod {e : UInt64} {spe j : Nat} (hj : j < spe) (hspe : spe < 2 ^ 64)
    (hov : (e.toNat + 1) * spe ≤ 2 ^ 64) :
    ((e * UInt64.ofNat spe + UInt64.ofNat j) % UInt64.ofNat spe).toNat = j := by
  rw [UInt64.toNat_mod, epochSlot_toNat hj hspe hov, toNat_ofNat_lt64 hspe,
    Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-! ## The epoch-level partition, once for every fork

`committee j idx` stands for a fork's `get_beacon_committee` at slot offset `j`
and index `idx`. `hcomm` is the fork bridge: that committee is slice
`j * cps + idx` of the `cps * spe` slices of `active`. -/

/-- Over one epoch, the committees for every slot and index are a permutation
of `active`. -/
theorem epoch_partition (active perm : Array UInt64) (spe cps : Nat) (hspe : 0 < spe)
    (hcps : 0 < cps) (σ : Nat → Nat)
    (hperm : ((List.range active.size).map σ).Perm (List.range active.size))
    (hget : ∀ p, p < active.size → (perm[p]!).toNat = σ p)
    (committee : Nat → Nat → Array UInt64)
    (hcomm : ∀ j, j < spe → ∀ idx, idx < cps →
      committee j idx = committeeSlice active perm (j * cps + idx) (cps * spe)) :
    ((List.range spe).flatMap fun j =>
        (List.range cps).flatMap fun idx => (committee j idx).toList).Perm
      active.toList := by
  -- Rewrite each committee to its slice.
  rw [flatMap_congr_mem fun j hj => flatMap_congr_mem fun idx hidx => by
    rw [hcomm j (List.mem_range.mp hj) idx (List.mem_range.mp hidx)]]
  -- Walk `(j, idx)` as the single committee number `j * cps + idx`.
  rw [flatMap_range_mul spe cps (fun k => (committeeSlice active perm k (cps * spe)).toList),
    Nat.mul_comm spe]
  exact committeeSlice_partition active perm _ (Nat.mul_pos hcps hspe) σ hperm hget

/-- A duplicate-free `active` gives duplicate-free committees: no entry sits in
two committees of the epoch, or twice in one. -/
theorem epoch_nodup (active perm : Array UInt64) (spe cps : Nat) (hspe : 0 < spe)
    (hcps : 0 < cps) (σ : Nat → Nat)
    (hperm : ((List.range active.size).map σ).Perm (List.range active.size))
    (hget : ∀ p, p < active.size → (perm[p]!).toNat = σ p)
    (committee : Nat → Nat → Array UInt64)
    (hcomm : ∀ j, j < spe → ∀ idx, idx < cps →
      committee j idx = committeeSlice active perm (j * cps + idx) (cps * spe))
    (hnd : active.toList.Nodup) :
    ((List.range spe).flatMap fun j =>
        (List.range cps).flatMap fun idx => (committee j idx).toList).Nodup :=
  (epoch_partition active perm spe cps hspe hcps σ hperm hget committee hcomm).nodup_iff.mpr hnd

/-- Every entry of `active` sits in some committee of the epoch. -/
theorem epoch_covers (active perm : Array UInt64) (spe cps : Nat) (hspe : 0 < spe)
    (hcps : 0 < cps) (σ : Nat → Nat)
    (hperm : ((List.range active.size).map σ).Perm (List.range active.size))
    (hget : ∀ p, p < active.size → (perm[p]!).toNat = σ p)
    (committee : Nat → Nat → Array UInt64)
    (hcomm : ∀ j, j < spe → ∀ idx, idx < cps →
      committee j idx = committeeSlice active perm (j * cps + idx) (cps * spe))
    (v : UInt64) (hv : v ∈ active.toList) :
    ∃ j, j < spe ∧ ∃ idx, idx < cps ∧ v ∈ (committee j idx).toList := by
  have hp :=
    (epoch_partition active perm spe cps hspe hcps σ hperm hget committee hcomm).mem_iff.mpr hv
  simpa only [List.mem_flatMap, List.mem_range] using hp

end EthCLLib.Proofs
