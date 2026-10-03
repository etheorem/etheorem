import LeanHazmatBn254

/-!
# `LeanHazmatBn254Tests.Vectors`: alt_bn128 Known-Answer-Tests

Self-contained KAT gate for the mcl-backed shims. There is no pure-Lean
reference for BN254 pairing computation, so this is the *only*
validation of the FFI boundary (packages/hazmat/docs/ARCHITECTURE.md §10).
Three kinds of case:

* **Point arithmetic anchors** generated from `ethereum/py_ecc` (the
  reference implementation EIP-197 itself links): G1 doubling,
  addition, and scalar multiplication (including the `(q-1)` negation
  and the scalar-0 → infinity case); G2 doubling, addition, and a
  small scalar product; and the infinity-absorbing additions.
* **Pairing-check anchors** on the same ground truth: a two-pair
  product whose discrete-log sum vanishes (`2·3 + 3·(q-2) ≡ 0 mod q`)
  passes, a non-vanishing one fails, and the empty pair set is one
  (the EIP-197 empty-input rule). The check composes the three
  primitives exactly as a consumer would: `millerLoopVec`, then
  `finalExp`, then `gtIsOne`. `millerLoopVec`'s empty sentinel maps
  to `none`, which a precompile caller must reject: EIP-197 fails
  the call on invalid input, and `gtIsOne` alone would report it as
  a successful "product is not one".
* **Negatives**: an off-curve G1 point, G1 and G2 coordinates equal
  to the field modulus `p`, a G2 point outside the order-`q` subgroup,
  a pair-array length mismatch, a bad point inside a pair array, and
  wrong-length inputs (a short G1 point, a short GT input, a GT
  coefficient `≥ p`) all yield the empty `ByteArray`; scalars at and
  above the group order reduce (`q → infinity`, `q+5 → 5·P1`,
  `2^256-1 → the reduced product`).

Each case is one `native_decide`, the mcl computation runs as compiled
code at proof-check time (one `Lean.ofReduceBool` axiom per case), the
acceptable regime for a KAT (CLAUDE.md "Proofs involving SSZ hashes"
generalises to all FFI crypto).
-/

set_option autoImplicit false

namespace LeanHazmatBn254Tests.Vectors

open LeanHazmat.Bn254

/-! ### Hex helper -/

/-- Value of a single hex digit (`0` for any non-hex char, inputs here
are always well-formed). -/
private def hexVal (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else 0

/-- Pair adjacent hex digits into bytes. Structural recursion on the
char list (each step drops two elements). -/
private def hexBytes : List Char → List UInt8
  | a :: b :: rest => (hexVal a * 16 + hexVal b) :: hexBytes rest
  | _ => []

/-- Decode a hex string (no `0x` prefix) into a `ByteArray`. -/
private def hex (s : String) : ByteArray := ⟨(hexBytes s.toList).toArray⟩

/-! ### Vector definitions (py_ecc ground truth) -/

/-- The G1 generator `(1, 2)`, 64-byte EIP-196 encoding. -/
private def g1P1 : ByteArray :=
  hex ("0000000000000000000000000000000000000000000000000000000000000001" ++
       "0000000000000000000000000000000000000000000000000000000000000002")

/-- `2 · P1` (py_ecc ground truth). -/
private def g1P2 : ByteArray :=
  hex ("030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd3" ++
       "15ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4")

/-- `3 · P1` (py_ecc ground truth). -/
private def g1P3 : ByteArray :=
  hex ("0769bf9ac56bea3ff40232bcb1b6bd159315d84715b8e679f2d355961915abf0" ++
       "2ab799bee0489429554fdb7c8d086475319e63b40b9c5b57cdf1ff3dd9fe2261")

/-- `5 · P1` (py_ecc ground truth). -/
private def g1Five : ByteArray :=
  hex ("17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
       "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c")

/-- `(q-1) · P1 = -P1` (py_ecc ground truth). -/
private def g1Neg : ByteArray :=
  hex ("0000000000000000000000000000000000000000000000000000000000000001" ++
       "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45")

/-- The G1 point at infinity (all zeros, EIP-196). -/
private def g1Inf : ByteArray :=
  hex ("0000000000000000000000000000000000000000000000000000000000000000" ++
       "0000000000000000000000000000000000000000000000000000000000000000")

/-- Scalars are exactly 32 bytes (the EL field width); the shim rejects other lengths. -/
private def kFive : ByteArray :=
  hex "0000000000000000000000000000000000000000000000000000000000000005"

/-- The scalar `q - 1`: the group order minus one, so `k · P = -P`. -/
private def kNegOne : ByteArray :=
  hex "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000"

/-- The scalar 0: the product is the point at infinity. -/
private def kZero : ByteArray := hex "0000000000000000000000000000000000000000000000000000000000000000"

/-- The scalar `2^256 - 1`: the largest 32-byte value, `>= q`, so the
shim reduces it mod the group order (EIP-196's rule). -/
private def kMaxVec : ByteArray :=
  hex "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

/-- `kMaxVec` reduces to a value below `q`; this is the pinned product. -/
private def g1MulKMax : ByteArray :=
  hex ("2f588cffe99db877a4434b598ab28f81e0522910ea52b45f0adaa772b2d5d352" ++
       "12f42fa8fd34fb1b33d8c6a718b6590198389b26fc9d8808d971f8b009777a97")

/-- The scalar `q + 5`: above the order, reduces to 5, so the product
is the pinned `5 * P1`. -/
private def kQPlusFive : ByteArray :=
  hex "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000006"

/-- The scalar `q` (the group order itself): the product is the
point at infinity. -/
private def kOrderVec : ByteArray :=
  hex "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"

/-- An off-curve point: `(0, 1)` fails `y^2 = x^3 + 3`. -/
private def g1Bad : ByteArray :=
  hex ("0000000000000000000000000000000000000000000000000000000000000000" ++
       "0000000000000000000000000000000000000000000000000000000000000001")

/-- The G2 generator `P2`, 128-byte EIP-197 encoding (imaginary half first). -/
private def g2P1 : ByteArray :=
  hex ("198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2" ++
       "1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed" ++
       "090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b" ++
       "12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa")

/-- `2 · P2` (py_ecc ground truth). -/
private def g2P2 : ByteArray :=
  hex ("203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad79" ++
       "27dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9" ++
       "195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de152" ++
       "04bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e")

/-- `3 · P2` (py_ecc ground truth). -/
private def g2P3 : ByteArray :=
  hex ("1014772f57bb9742735191cd5dcfe4ebbc04156b6878a0a7c9824f32ffb66e85" ++
       "06064e784db10e9051e52826e192715e8d7e478cb09a5e0012defa0694fbc7f5" ++
       "021e2335f3354bb7922ffcc2f38d3323dd9453ac49b55441452aeaca147711b2" ++
       "058e1d5681b5b9e0074b0f9c8d2c68a069b920d74521e79765036d57666c5597")

/-- `5 · P2` (py_ecc ground truth). -/
private def g2Five : ByteArray :=
  hex ("0a09ccf561b55fd99d1c1208dee1162457b57ac5af3759d50671e510e428b2a1" ++
       "2e539c423b302d13f4e5773c603948eaf5db5df8ae8a9a9113708390a06410d8" ++
       "19b763513924a736e4eebd0d78c91c1bc1d657fee4214057d21414011cfcc763" ++
       "2f8d9f9ab83727c77a2fec063cb7b6e5eb23044ccf535ad49d46d394fb6f6bf6")

/-- The G2 point at infinity (all zeros). -/
private def g2Inf : ByteArray :=
  hex ("0000000000000000000000000000000000000000000000000000000000000000" ++
       "0000000000000000000000000000000000000000000000000000000000000000" ++
       "0000000000000000000000000000000000000000000000000000000000000000" ++
       "0000000000000000000000000000000000000000000000000000000000000000")

/-- Pair 1 of the true check: `(2·P1, 3·P2)`. Its G1 half is `2·P1`. -/
private def trueA1 : ByteArray := g1P2
/-- Pair 1 G2 of the true pairing check: `3 · P2`. -/
private def trueB1 : ByteArray := g2P3

/-- Pair 2 of the true check: `(3·P1, (q-2)·P2)`. Its G1 half is `3·P1`. -/
private def trueA2 : ByteArray := g1P3
/-- Pair 2 G2 of the true pairing check: `(q-2) · P2`. -/
private def trueB2 : ByteArray :=
  hex ("203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad79" ++
       "27dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9" ++
       "1705c3cd29af2bc64624b9a1485000c0627c1426199281b8a33f062687df1bf5" ++
       "2ba8faba49b3409717940e8f3ebcd55452dbcf4181c00a46cdf61e69c651a019")

/-- Pair 2 of the false check: `(3·P1, 4·P2)` (discrete-log sum `2·3 + 3·4 ≠ 0`).
Its G1 half is `3·P1`. -/
private def falseA2 : ByteArray := g1P3
/-- Pair 2 G2 of the false pairing check: `4 · P2`. -/
private def falseB2 : ByteArray :=
  hex ("290668479e567ad5a2485a93f976d784206f66f690a18c3f5a6d85c29571236f" ++
       "29dddbf86f6a2f47c38063a850ccc442131570e5084c45fd7709b4ddb436e22c" ++
       "1e74a4bf519c267a5b16431b2413b00402d4d3b670c9414b8efff5bee661a8f6" ++
       "299f0af7f72b3a93ca7c3cc32443c83b05d041bd14276e5adca2546728bc37f7")

/-- The infinity pair `(q·P1, P2)`: `q·P1 = ∞`, trivially true.
Its G1 half is the infinity point. -/
private def infA : ByteArray := g1Inf
/-- `P2`, the G2 half of the trivial infinity pair. -/
private def infB : ByteArray := g2P1

/-- A single non-degenerate pairing `(P1, P2)`, for the not-one probe.
Its G1 half is the generator. -/
private def probeA : ByteArray := g1P1
/-- `P2`, the G2 half of the non-degenerate not-one probe. -/
private def probeB : ByteArray := g2P1

/-! ### G1 (EIP-196) -/

/-- `P1 + P1 = 2·P1`. -/
example : g1Add g1P1 g1P1 = g1P2 := by native_decide

/-- `2·P1 + P1 = 3·P1`. -/
example : g1Add g1P2 g1P1 = g1P3 := by native_decide

/-- `5 · P1`. -/
example : g1Mul g1P1 kFive = g1Five := by native_decide

/-- `(q-1) · P1 = -P1`. -/
example : g1Mul g1P1 kNegOne = g1Neg := by native_decide

/-- `2^256 - 1` reduces mod `q` to exactly this pinned product. -/
example : g1Mul g1P1 kMaxVec = g1MulKMax := by native_decide

/-- `q + 5` reduces to 5, so the product is the pinned `5 * P1`. -/
example : g1Mul g1P1 kQPlusFive = g1Five := by native_decide

/-- The order itself annihilates the generator (all zeros). -/
example : g1Mul g1P1 kOrderVec = g1Inf := by native_decide

/-- The infinity absorbs: `P1 + ∞ = P1`. -/
example : g1Add g1P1 g1Inf = g1P1 := by native_decide

/-- Scalar 0 gives the infinity encoding (all zeros). -/
example : g1Mul g1P1 kZero = g1Inf := by native_decide

/-! ### G2 (EIP-197) -/

/-- `P2 + P2 = 2·P2`. -/
example : g2Add g2P1 g2P1 = g2P2 := by native_decide

/-- `2·P2 + P2 = 3·P2`. -/
example : g2Add g2P2 g2P1 = g2P3 := by native_decide

/-- `5 · P2`. -/
example : g2Mul g2P1 kFive = g2Five := by native_decide

/-- Scalar 0 sends any G2 point to the infinity encoding. -/
example : g2Mul g2P1 kZero = g2Inf := by native_decide

/-- The infinity absorbs: `P2 + ∞ = P2`. -/
example : g2Add g2P1 g2Inf = g2P1 := by native_decide

/-! ### Pairing check (EIP-197 / 1108) -/

/-- The consumer-side composition, spelled out once: miller product,
final exponentiation, identity test. `millerLoopVec`'s empty
sentinel becomes `none`: EIP-197 fails the precompile on invalid
input, and the caller must check for `none` before `gtIsOne`'s
`Bool` means anything. -/
private def pairingCheck (g1s : Array ByteArray) (g2s : Array ByteArray) :
    Option Bool :=
  match millerLoopVec g1s g2s with
  | .empty => none
  | gt => some (gtIsOne (finalExp gt))

/-- The vanishing discrete-log sum: `2·3 + 3·(q-2) = 3q ≡ 0`, so the
two-pair product of pairings is one. -/
example : pairingCheck #[trueA1, trueA2] #[trueB1, trueB2] = some true := by
  native_decide

/-- A non-vanishing sum `2·3 + 3·4`: the check fails. Pair 1 is the
same `(2·P1, 3·P2)` as the true check. -/
example : pairingCheck #[trueA1, falseA2] #[trueB1, falseB2] = some false := by
  native_decide

/-- The empty pair set is the GT identity (EIP-197's empty-input
rule: a pairing check over zero pairs passes). -/
example : pairingCheck #[] #[] = some true := by native_decide

/-- A single infinity pair (`q·P1 = ∞`) is trivially one. -/
example : pairingCheck #[infA] #[infB] = some true := by native_decide

/-- A non-degenerate single pairing is *not* one. -/
example : pairingCheck #[probeA] #[probeB] = some false := by native_decide

/-- A pair with the G2 point at infinity: `e(P1, ∞) = 1`, so the
product is one (millerLoopVec skips the zero pair). -/
example : pairingCheck #[probeA] #[g2Inf] = some true := by native_decide

/-- A bad point *inside* the pair array is rejected with the empty
sentinel, which the composition reports as `none` (the EIP-197
precompile must fail on invalid input; a bare `false` would read as a
completed negative check). Pair 1 is the true check's `(2·P1, 3·P2)`;
pair 2's G1 half is off-curve. -/
example : pairingCheck #[trueA1, g1Bad] #[trueB1, trueB2] = none := by
  native_decide

/-- A pair-array length mismatch is `none`, not a `Bool`. -/
example : pairingCheck #[trueA1] (#[] : Array ByteArray) = none := by
  native_decide

/-! ### Negatives -/

/-- An off-curve G1 point is rejected with the empty `ByteArray`. -/
example : g1Add g1Bad g1P1 = ByteArray.empty := by native_decide

/-- A G1 coordinate equal to `p` (the field modulus, so out of range)
is rejected: EIP-196 requires coordinates `< p`. -/
private def g1BigCoord : ByteArray :=
  hex ("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47" ++
      "0000000000000000000000000000000000000000000000000000000000000002")

example : g1Add g1BigCoord g1P1 = ByteArray.empty := by native_decide

/-- A G2 coordinate equal to `p` is rejected: `x = p·i, y = 0`, and the
EIP-197 range check requires coordinates `< p`. -/
private def g2BigCoord : ByteArray :=
  hex ("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000" ++
      "0000000000000000000000000000000000000000000000000000000000000000")

example : g2Add g2BigCoord g2P1 = ByteArray.empty := by native_decide

/-- An on-curve G2 point OUTSIDE the order-`q` subgroup is rejected by
deserialization: the EIP-197 membership rule. The point was generated
independently (square root in `F_p2`); `scripts/gen_vectors.py` carries
the provenance: it re-derives the point from the committed `x`, and
asserts with py_ecc both that the decoded (EIP-197 order) encoding is on
the curve and that `q · P ≠ ∞`, so a rejection here can only come from
the subgroup check the shim pins. -/
private def g2NonSubgroup : ByteArray :=
  hex ("0000000000000000000000000000000000000000000000000000000000000003" ++
      "0000000000000000000000000000000000000000000000000000000000000002" ++
      "1b3983aba87e776f3bce1885442ec3e9c6ad7f6f05321c57eebe5dcf0c2e7f32" ++
      "0239d6264efb1d130c43464ef93b83508adf1cf49b9571dc36dbbaa2a17dc655")

example : g2Add g2NonSubgroup g2P1 = ByteArray.empty := by native_decide

/-- A length mismatch between the two arrays is rejected. -/
example : millerLoopVec #[g1P1] (#[] : Array ByteArray) = ByteArray.empty := by
  native_decide

/-- A wrong-length G1 point is rejected. -/
example : g1Add ByteArray.empty g1P1 = ByteArray.empty := by native_decide

/-- A wrong-length GT input (383 bytes, one short) is rejected with the
empty `ByteArray`, as `finalExp`'s docstring promises. -/
private def gtShort : ByteArray := ⟨Array.replicate 383 (0 : UInt8)⟩

example : finalExp gtShort = ByteArray.empty := by native_decide

/-- `gtIsOne` answers `false` on the same wrong-length input. -/
example : gtIsOne gtShort = false := by native_decide

/-- A GT input whose leading coefficient equals `p` (out of range) is
rejected by the deserializer's per-coefficient range check. -/
private def gtBigCoeff : ByteArray :=
  hex ("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47" ++
       "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
       "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
       "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")

example : finalExp gtBigCoeff = ByteArray.empty := by native_decide

example : gtIsOne gtBigCoeff = false := by native_decide

/-! ### Negative-vector length pins

`hex` maps a bad character to 0 and drops an odd trailing digit, so a
mistyped literal still decodes, only short. Every vector below feeds a
negative test that expects the empty `ByteArray`; through such a typo
the shim would reject it on the length check instead of the check
under test, and the gate would pass for the wrong reason. The pins
move the failure to the build. -/

#guard g1Bad.size == 64
#guard g1BigCoord.size == 64
#guard g2BigCoord.size == 128
#guard g2NonSubgroup.size == 128

end LeanHazmatBn254Tests.Vectors
