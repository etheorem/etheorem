import EthCLLib.Spec.SigningRoot
import EthCLLib.Spec.Arith
import EthCLLib.Proofs.Lemmas

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

/-! ## The rounds the fork bodies run -/

/-- Round `r`'s pivot: the first eight bytes of `hash(seed ++ r)`, little-endian,
reduced mod `n`. -/
def swapOrNotPivot [HasherTag] (seed : ByteArray) (n r : Nat) : Nat :=
  le8 (sha (seed.push (UInt8.ofNat r))) % n

/-- Round `r`'s bit at `position`: bit `position % 8` of byte
`(position % 256) / 8` of `hash(seed ++ r ++ u32le(position / 256))`. -/
def swapOrNotBit [HasherTag] (seed : ByteArray) (r position : Nat) : Bool :=
  let source := sha (seed.push (UInt8.ofNat r) ++ u32leBytes (position / 256))
  let byteVal := (source.get! ((position % 256) / 8)).toNat
  (byteVal >>> (position % 8)) % 2 == 1

/-- Round `r` as a function on values. -/
def roundAt [HasherTag] (n : Nat) (seed : ByteArray) (r : Nat) : Nat → Nat :=
  swapOrNotRound n (swapOrNotPivot seed n r) (swapOrNotBit seed r)

/-- Rounds `0 … R-1` applied to `x`, round `0` first. -/
def shuffleNat [HasherTag] (n : Nat) (seed : ByteArray) : Nat → Nat → Nat
  | 0, x => x
  | R + 1, x => roundAt n seed R (shuffleNat n seed R x)

/-- Rounds `R-1 … 0` applied to `y`, the last round first. Each round is its own
inverse, so this undoes `shuffleNat`. -/
def unshuffleNat [HasherTag] (n : Nat) (seed : ByteArray) : Nat → Nat → Nat
  | 0, y => y
  | R + 1, y => unshuffleNat n seed R (roundAt n seed R y)

/-- `swapOrNotRound_lt` for the fork bodies' round. -/
theorem roundAt_lt [HasherTag] {n x : Nat} (seed : ByteArray) (r : Nat)
    (hn : 0 < n) (hx : x < n) : roundAt n seed r x < n :=
  swapOrNotRound_lt _ hn hx

/-- `swapOrNotRound_involutive` for the fork bodies' round. -/
theorem roundAt_involutive [HasherTag] {n x : Nat} (seed : ByteArray) (r : Nat)
    (hn : 0 < n) (hx : x < n) : roundAt n seed r (roundAt n seed r x) = x :=
  -- `swapOrNotPivot` reduces the pivot `% n`. That gives the `p < n` bound the
  -- involution needs.
  swapOrNotRound_involutive _ (Nat.mod_lt _ hn) hx

/-- The shuffle keeps a value inside `[0, n)`. -/
theorem shuffleNat_lt [HasherTag] {n x : Nat} (seed : ByteArray) (R : Nat)
    (hn : 0 < n) (hx : x < n) : shuffleNat n seed R x < n := by
  induction R with
  | zero => exact hx
  | succ R ih => exact roundAt_lt seed R hn ih

/-- The inverse shuffle keeps a value inside `[0, n)`. -/
theorem unshuffleNat_lt [HasherTag] {n y : Nat} (seed : ByteArray) (R : Nat)
    (hn : 0 < n) (hy : y < n) : unshuffleNat n seed R y < n := by
  induction R generalizing y with
  | zero => exact hy
  | succ R ih => exact ih (roundAt_lt seed R hn hy)

/-- `unshuffleNat` is a left inverse of `shuffleNat` on `[0, n)`. -/
theorem unshuffleNat_shuffleNat [HasherTag] {n x : Nat} (seed : ByteArray) (R : Nat)
    (hn : 0 < n) (hx : x < n) : unshuffleNat n seed R (shuffleNat n seed R x) = x := by
  induction R with
  | zero => rfl
  | succ R ih =>
    simp only [shuffleNat, unshuffleNat]
    rw [roundAt_involutive seed R hn (shuffleNat_lt seed R hn hx), ih]

/-- `unshuffleNat` is a right inverse of `shuffleNat` on `[0, n)`. -/
theorem shuffleNat_unshuffleNat [HasherTag] {n y : Nat} (seed : ByteArray) (R : Nat)
    (hn : 0 < n) (hy : y < n) : shuffleNat n seed R (unshuffleNat n seed R y) = y := by
  induction R generalizing y with
  | zero => rfl
  | succ R ih =>
    simp only [shuffleNat, unshuffleNat]
    rw [ih (roundAt_lt seed R hn hy), roundAt_involutive seed R hn hy]

/-- `shuffleNat` maps `[0, n)` onto itself one to one, so its image of
`List.range n` is a permutation of `List.range n`. -/
theorem shuffleNat_perm [HasherTag] {n : Nat} (seed : ByteArray) (R : Nat) :
    ((List.range n).map (shuffleNat n seed R)).Perm (List.range n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- The image has no duplicates: `unshuffleNat` undoes `shuffleNat` on `[0, n)`.
  have hnd : ((List.range n).map (shuffleNat n seed R)).Nodup := by
    refine nodup_map_of_injOn List.nodup_range ?_
    intro x hx y hy hxy
    have h := congrArg (unshuffleNat n seed R) hxy
    rwa [unshuffleNat_shuffleNat seed R hn (List.mem_range.mp hx),
      unshuffleNat_shuffleNat seed R hn (List.mem_range.mp hy)] at h
  refine perm_of_nodup_of_mem_iff hnd List.nodup_range fun a => ?_
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact shuffleNat_lt seed R hn hx
  · intro ha
    exact ⟨unshuffleNat n seed R a, unshuffleNat_lt seed R hn ha,
      shuffleNat_unshuffleNat seed R hn ha⟩

end EthCLLib.Proofs
