import LeanPoseidon
import Mathlib

/-!
# `LeanPoseidonProofs.Padding` — the sponge padding is injective

Phase 6, Target 2. The sponge `pad` (append a marker `1`, then `0`s to a
multiple of `rate = 2`) is **injective** — the structural hypothesis a sponge
needs (it keeps inputs differing only by trailing structure distinct, and is a
premise of sponge indifferentiability). `Sponge.lean` only `#guard`s the
plumbing; this proves the property.

The argument (mapped to `List` via `Array.toList_inj`): `pad xs` is
`xs ++ [1] ++ replicate k 0` with `k = (|xs|+1) % 2 ∈ {0,1}`. The **last
element** is the marker `1` (if `k = 0`) or a pad `0` (if `k = 1`); since
`1 ≠ 0`, equal outputs force equal `k`, and with the equal total length this
forces `|xs| = |ys|`. Equal prefix lengths then strip the shared suffix
(`List.append_inj_left`). `1 ≠ 0` is the load-bearing field fact.
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

open LeanPoseidon

/-- The padding marker differs from the padding filler. -/
private theorem mark_ne_fill : Bn254Fr.ofNat 1 ≠ Bn254Fr.ofNat 0 := by decide

/-- `getLast?` of a list ending in `1 :: replicate k 0`: the marker `1` if no
zeros, otherwise a `0`. -/
private theorem getLast?_suffix (l : List Bn254Fr) (k : Nat) :
    (l ++ Bn254Fr.ofNat 1 :: List.replicate k (Bn254Fr.ofNat 0)).getLast?
      = if k = 0 then some (Bn254Fr.ofNat 1) else some (Bn254Fr.ofNat 0) := by
  cases k with
  | zero => simp
  | succ n =>
    have hrw : l ++ Bn254Fr.ofNat 1 :: List.replicate (n + 1) (Bn254Fr.ofNat 0)
             = (l ++ [Bn254Fr.ofNat 1]) ++ List.replicate (n + 1) (Bn254Fr.ofNat 0) := by simp
    rw [hrw, List.getLast?_append]
    simp [List.getLast?_replicate]

/-- `pad`'s underlying list: input, marker `1`, then `(|xs|+1) % 2` copies of `0`. -/
private theorem pad_toList (xs : Array Bn254Fr) :
    (pad xs).toList =
      xs.toList ++ Bn254Fr.ofNat 1 :: List.replicate ((xs.size + 1) % 2) (Bn254Fr.ofNat 0) := by
  have hzeros : (if (xs.size + 1) % 2 = 0 then 0 else 2 - (xs.size + 1) % 2) = (xs.size + 1) % 2 := by
    have : (xs.size + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    split <;> omega
  simp only [pad, rate, Array.size_push, Array.toList_append, Array.toList_push,
    Array.toList_replicate, hzeros, List.append_assoc, List.singleton_append]

/-- The sponge padding is injective. -/
theorem pad_injective : Function.Injective pad := by
  intro xs ys h
  have hl : (pad xs).toList = (pad ys).toList := congrArg Array.toList h
  rw [pad_toList, pad_toList] at hl
  -- last element pins the parity ⇒ equal zero-counts
  have hlast := congrArg List.getLast? hl
  rw [getLast?_suffix, getLast?_suffix] at hlast
  have hkeq : (xs.size + 1) % 2 = (ys.size + 1) % 2 := by
    have hkx2 : (xs.size + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hky2 : (ys.size + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases hx0 : (xs.size + 1) % 2 = 0 <;> by_cases hy0 : (ys.size + 1) % 2 = 0
    · omega
    · rw [if_pos hx0, if_neg hy0] at hlast; exact absurd (Option.some.inj hlast) mark_ne_fill
    · rw [if_neg hx0, if_pos hy0] at hlast; exact absurd (Option.some.inj hlast).symm mark_ne_fill
    · omega
  -- equal total length + equal counts ⇒ equal input sizes ⇒ strip the suffix
  have hlen : xs.toList.length = ys.toList.length := by
    have hL := congrArg List.length hl
    simp only [List.length_append, List.length_cons, List.length_replicate,
      Array.length_toList] at hL ⊢
    omega
  exact Array.toList_inj.mp (List.append_inj_left hl hlen)

end LeanPoseidon.Poseidon2
