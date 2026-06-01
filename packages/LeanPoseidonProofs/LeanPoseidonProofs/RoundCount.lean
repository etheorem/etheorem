import LeanPoseidon
import Mathlib.Data.Nat.Log

/-!
# `LeanPoseidonProofs.RoundCount` — the shipped round numbers meet the paper's floor

Phase 6, Target 4. A decidable, build-time check that the shipped Poseidon2
round numbers (`R_F = 8`, `R_P = 56`) satisfy the **minimum-round inequalities**
from the reference parameter-selection script
(HorizenLabs `poseidon2_rust_params.sage`, `sat_inequiv_alpha`). This certifies
a *different* axis than the differential conformance test (which only proves the
implementation matches `zkhash`): here we check the chosen rounds against the
*published security floor*.

## What is and is not checked

The reference predicate is a `max` of five full-round lower bounds plus a
Gröbner/binomial cost bound, evaluated in **floating point**. Two of the five
bounds recast **exactly** to decidable `Nat` arithmetic and are checked here:

* **statistical / differential–linear** (`R_F_1`): `R_F ≥ 6` (resp. `10`) when
  `M ≤ ⌊log₂ p − (d−1)/2⌋·(t+1)` — `⌊log₂ p⌋` is `Nat.log 2 p`;
* **interpolation** (`R_F_2`): `R_F + R_P ≥ 1 + ⌈log_d(2^min(M,n))⌉ + ⌈log_d t⌉`,
  where `⌈log_d(2^k)⌉ = Nat.clog d (2^k)` and `n` is the field bit-length.

The remaining three bounds (`R_F_3..R_F_5`) are dominated by `R_P` (trivially
satisfied for these parameters) and the Gröbner *cost* bound involves
`⌈2·log₂ C(over,under)⌉` of a several-hundred-digit binomial; those rest on the
reference's floating-point evaluation and are **not** re-encoded here. So this
file certifies the two crisply-recastable security-floor inequalities hold (with
margin) for both shipped instances — not the full float predicate.

`M = 128` (the target security level for the shipped instances). `Nat.clog`/`Nat.log`
are kernel-computable, so every check below is a `#guard` (no axioms, no
`native_decide`).
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

/-- Target security level (bits) for the shipped `t = 3` instances. -/
def secLevel : Nat := 128

/-- Statistical / differential–linear minimum full rounds (`R_F_1`): `6` if the
field is large enough relative to `M`, else `10`. `⌊log₂ p⌋ = Nat.log 2 p`. -/
def rfStatBound (p t d M : Nat) : Nat :=
  if M ≤ (Nat.log 2 p - (d - 1) / 2) * (t + 1) then 6 else 10

/-- Interpolation-attack minimum (`R_F_2`), recast via `Nat.clog`: the chosen
`R_F + R_P` must reach `1 + ⌈log_d(2^min(M,n))⌉ + ⌈log_d t⌉`, where `n` is the
field's bit-length `⌊log₂ p⌋ + 1`. -/
def interpBound (p t d M : Nat) : Nat :=
  let n := Nat.log 2 p + 1
  1 + Nat.clog d (2 ^ min M n) + Nat.clog d t

/-- The shipped round numbers of `par` over a field of modulus `p` meet both
recastable security-floor bounds at security level `M`. Decidable. -/
abbrev meetsFloor (p : Nat) {R : Type} (par : Params R) (M : Nat) : Prop :=
  par.fullRounds ≥ rfStatBound p par.t par.sboxDegree M ∧
  par.fullRounds + par.partialRounds ≥ interpBound p par.t par.sboxDegree M

/-! ## The shipped instances pass (BN254 and BLS12-381, `t = 3`, `d = 5`, `M = 128`)

For BN254: `⌊log₂ p⌋ = 253`, so `R_F_1 = 6 ≤ 8 = R_F`; and
`1 + ⌈log₅ 2¹²⁸⌉ + ⌈log₅ 3⌉ = 1 + 56 + 1 = 58 ≤ 64 = R_F + R_P`. -/

#guard meetsFloor bn254FrModulus bn254Params secLevel
#guard meetsFloor blsFrModulus bls12Params secLevel

-- The interpolation bound is the binding one; record the slack explicitly.
#guard bn254Params.fullRounds + bn254Params.partialRounds
        ≥ interpBound bn254FrModulus bn254Params.t bn254Params.sboxDegree secLevel
#guard interpBound bn254FrModulus bn254Params.t bn254Params.sboxDegree secLevel = 58

end LeanPoseidon.Poseidon2
