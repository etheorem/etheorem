import EthCLLib.Spec.SigningRoot
import EthCLLib.Spec.Arith

/-!
# `EthCLLib.Proofs.SwapOrNot`: the swap-or-not shuffle is a permutation

`compute_shuffled_permutation` (`phase0/beacon-chain.md:819-842`) runs
`SHUFFLE_ROUND_COUNT` rounds. Each round moves every value `x` in `[0, n)` to
`flip x = (pivot + n - x) % n`, or leaves it. One bit decides. The round reads
that bit at `max x (flip x)`. The pair `x`, `flip x` reads the same bit, so the
pair swaps together or stays together. Each round is therefore an involution. A
chain of involutions is a bijection.

Nothing here reads the hash. `swapOrNotRound` takes the bit as any
`Nat → Bool`. `swapOrNotBit` names the bit function the fork bodies compute.
The theorems therefore hold for every `HasherTag`, and they cite no hash axiom.

No fork appears in this file. Each fork's `computeShuffledPermutation` is its own
constant. `EthCLSpecs/Proofs/<Fork>/Shuffle.lean` shows that each constant equals
`swapOrNotArray`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-! ## One round, for any bit function -/

/-- One swap-or-not round on a value `x`. `Nat.max` matches the fork bodies'
spelling, so the bridge lemmas close without a `max` rewrite. -/
def swapOrNotRound (n pivot : Nat) (b : Nat → Bool) (x : Nat) : Nat :=
  let flip := (pivot + n - x) % n
  if b (Nat.max x flip) then flip else x

/-- Flipping twice about the same pivot returns `x`. -/
theorem swapOrNotFlip_flip {n p x : Nat} (hp : p < n) (hx : x < n) :
    (p + n - (p + n - x) % n) % n = x := by
  rcases Nat.lt_or_ge p x with h | h
  · -- `p < x`: the first flip needs no reduction.
    rw [Nat.mod_eq_of_lt (by omega : p + n - x < n)]
    rw [(by omega : p + n - (p + n - x) = x), Nat.mod_eq_of_lt hx]
  · -- `x ≤ p`: the first flip is `p - x`, one `n` below the raw sum.
    rw [(by omega : p + n - x = (p - x) + n), Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : p - x < n)]
    rw [(by omega : p + n - (p - x) = x + n), Nat.add_mod_right, Nat.mod_eq_of_lt hx]

/-- A round keeps a value inside `[0, n)`. -/
theorem swapOrNotRound_lt {n p x : Nat} (b : Nat → Bool) (hn : 0 < n) (hx : x < n) :
    swapOrNotRound n p b x < n := by
  unfold swapOrNotRound
  dsimp only
  split
  · exact Nat.mod_lt _ hn
  · exact hx

/-- A round undoes itself, for every bit function `b`. This is the fact the
whole permutation proof rests on. -/
theorem swapOrNotRound_involutive {n p x : Nat} (b : Nat → Bool)
    (hp : p < n) (hx : x < n) :
    swapOrNotRound n p b (swapOrNotRound n p b x) = x := by
  have hff := swapOrNotFlip_flip hp hx
  by_cases hb : b (Nat.max x ((p + n - x) % n)) = true
  · -- Swapped: the image is `flip x`, and its partner is `x`. The pair has the
    -- same max, so the image reads the same set bit. The round then moves the
    -- image back to `x`.
    -- Core states `Nat.max_comm` for `max`. `Nat.max` is the body of the
    -- `Max Nat` instance, so the equation also holds for `Nat.max` by unfolding.
    have hcomm : Nat.max ((p + n - x) % n) x = Nat.max x ((p + n - x) % n) :=
      Nat.max_comm _ _
    have hb' : b (Nat.max ((p + n - x) % n) x) = true := by rwa [hcomm]
    simp [swapOrNotRound, hb, hff, hb']
  · -- Kept: the round leaves `x`, and running it again leaves `x` again.
    have hb' : b (Nat.max x ((p + n - x) % n)) = false := by simpa using hb
    simp [swapOrNotRound, hb']

end EthCLLib.Proofs
