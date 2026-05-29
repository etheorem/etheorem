import LeanPoseidon.Poseidon2.LinearLayers

/-!
# `LeanPoseidon.Permutation` — the Poseidon2 permutation

The full Poseidon2 schedule over a width-3 state, in both the shipped
*fast* form (`permute`) and a structurally identical *dense* reference
(`permuteRef`), plus the build-time **anchor KAT** that locks the
implementation against the HorizenLabs `zkhash` BN254 t=3 reference.

## The schedule (for the Lean-fluent reader)

Recall (from `Params.lean`): a *full round* applies the non-linear S-box
`x ↦ x⁵` to all three state elements; a *partial round* applies it to
element 0 only. *Round constants* (ARK, "add round key") are added before
each S-box; a *linear layer* (`LinearLayers.lean`) diffuses the state
after it. The BN254 t=3 schedule is:

1. an initial external linear layer `M_E`;
2. `fullRounds / 2 = 4` **full** rounds — add the 3 round constants → S-box
   all → `M_E`;
3. `partialRounds = 56` **partial** rounds — add 1 round constant to
   element 0 → S-box element 0 → internal layer `M_I`;
4. `fullRounds / 2 = 4` **full** rounds (as step 2).

This matches `zkhash`'s `Poseidon2::permutation` exactly, including where
each round constant is read from the flattened ARK array (the layout is
documented on `Params.roundConstants`).

## Factoring for a clean (deferred) proof

`permute` and `permuteRef` are both `permuteWith` applied to the schedule;
the *only* difference is which linear-layer functions they pass
(`mul*Fast` vs `mul*Ref`). The round-constant additions and the S-box are
byte-for-byte shared. So the (deferred) equivalence `permute = permuteRef`
is a straight congruence on the two layer equalities (`docs/PLAN.md`
Phase 3), not a fight against structural mismatch.

The output width is `3` *in the type* (`Vector R 3`), so there is no
separate "output has the right size" lemma to prove — the type carries it.

## The anchor KAT and `native_decide`

A single `example … := by native_decide` at the bottom locks `permute` on
input `[0, 1, 2]` to the three expected BN254 t=3 outputs. `native_decide`
evaluates the goal via *compiled* code (here: the whole permutation over
GMP-backed `Nat`) and trusts the compiler's reduction — it adds one
`Lean.ofReduceBool` axiom. Building this library runs the gate: it passes
or the implementation (field codec, a constant, a layer, the schedule
order) is wrong, caught at compile time. This mirrors the three in-file
FIPS §B asserts that anchor `LeanSha256`.
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

variable {R : Type} [Add R] [Mul R] [Sub R] [One R] [Inhabited R]

/-! ## Non-linear and ARK building blocks -/

/-- The `x ↦ x⁵` S-box, as `x² · x² · x` (two squarings and a
multiply — exactly `zkhash`'s `sbox_p` for degree `d = 5`). Written with
explicit multiplications rather than `Bn254Fr.pow` so the term is a polynomial
the `ring` tactic can normalise in the (deferred) equivalence proof. -/
def sbox (x : R) : R := let x2 := x * x; x2 * x2 * x

/-- One **full round**: add the three round constants `c`, S-box all three
elements, then apply the external linear layer. -/
def fullRound (extLayer : Vector R 3 → Vector R 3)
    (c : Fin 3 → R) (st : Vector R 3) : Vector R 3 :=
  let afterArk : Vector R 3 := Vector.ofFn (fun i => st[i] + c i)
  extLayer (Vector.ofFn (fun i => sbox afterArk[i]))

/-- One **partial round**: add the single round constant `c` to element 0,
S-box element 0 only, then apply the internal linear layer. -/
def partialRound (intLayer : Vector R 3 → Vector R 3)
    (c : R) (st : Vector R 3) : Vector R 3 :=
  let x0 := sbox (st[0] + c)
  intLayer (Vector.ofFn (fun i => if i = 0 then x0 else st[i]))

/-! ## The shared schedule

`permuteWith` is the schedule parameterised over the two linear-layer ops.
`Nat.fold n (fun i _ acc => …) init` folds the accumulator over
`i = 0, …, n−1` (ascending) — the same idiom `LeanSha256` uses for its 64
compression rounds. The round-constant indices follow the flattened ARK
layout on `Params.roundConstants`. -/

/-- The Poseidon2 round schedule, abstracted over the two linear-layer ops.
`permute` / `permuteRef` are its fast / dense instantiations; everything
else (the initial layer, the round-constant additions, the S-box, the
full/partial/full split) is shared, so they differ *only* in `extLayer` /
`intLayer`. Reads round constants from `par.roundConstants` per the
flattened ARK layout. -/
def permuteWith (par : Params R)
    (extLayer intLayer : Vector R 3 → Vector R 3)
    (st0 : Vector R 3) : Vector R 3 :=
  let rc := par.roundConstants
  let half := par.fullRounds / 2
  let np := par.partialRounds
  -- (1) initial external linear layer
  let st := extLayer st0
  -- (2) beginning full rounds r = 0 .. half−1; constants at flat[3r + i]
  let st := Nat.fold half (fun r _ st =>
      fullRound extLayer (fun i => rc[3 * r + i.val]!) st) st
  -- (3) partial rounds j = 0 .. np−1; constant at flat[3·half + j]
  let st := Nat.fold np (fun j _ st =>
      partialRound intLayer (rc[3 * half + j]!) st) st
  -- (4) end full rounds k = 0 .. half−1; constants at flat[3·half + np + 3k + i]
  let st := Nat.fold half (fun k _ st =>
      fullRound extLayer (fun i => rc[3 * half + np + 3 * k + i.val]!) st) st
  st

/-- The shipped Poseidon2 permutation: the schedule with the **fast**
linear layers. -/
def permute (par : Params R) (st : Vector R 3) : Vector R 3 :=
  permuteWith par mulExternalFast (mulInternalFast par) st

/-- The reference Poseidon2 permutation: the *same* schedule with the
**dense** linear layers. Equal to `permute` by the (deferred) layer
equivalences; exists so that equality can be proved. -/
def permuteRef (par : Params R) (st : Vector R 3) : Vector R 3 :=
  permuteWith par mulExternalRef (mulInternalRef par) st

/-! ## Anchor KATs — the build-time conformance gates

Input state `[0, 1, 2]` through each pinned `t = 3` instance produces the
outputs below, taken from the HorizenLabs `zkhash` v0.2.0 reference
(`poseidon2_tests_bn256::kats` / `poseidon2_tests_bls12::kats`).
`native_decide` evaluates `permute` via compiled code and checks the
equality. The **same generic `permute`** runs over both fields — the BLS12
gate is the field abstraction's anchor: a different field, zero code
changes. -/

-- BN254 scalar field (the shipped default).
example :
    permute bn254Params (#v[Bn254Fr.ofNat 0, Bn254Fr.ofNat 1, Bn254Fr.ofNat 2])
      = #v[Bn254Fr.ofNat 0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033,
           Bn254Fr.ofNat 0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570,
           Bn254Fr.ofNat 0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8] := by
  native_decide

-- BLS12-381 scalar field (a second field through the same `permute`).
example :
    permute bls12Params (#v[Bls12Fr.ofNat 0, Bls12Fr.ofNat 1, Bls12Fr.ofNat 2])
      = #v[Bls12Fr.ofNat 0x1b152349b1950b6a8ca75ee4407b6e26ca5cca5650534e56ef3fd45761fbf5f0,
           Bls12Fr.ofNat 0x4c5793c87d51bdc2c08a32108437dc0000bd0275868f09ebc5f36919af5b3891,
           Bls12Fr.ofNat 0x1fc8ed171e67902ca49863159fe5ba6325318843d13976143b8125f08b50dc6b] := by
  native_decide

end LeanPoseidon.Poseidon2
