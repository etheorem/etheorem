import LeanPoseidon.Field
import Mathlib.Data.Nat.Prime.Defs

/-!
# `LeanPoseidonProofs.Primality`: the cited primality axioms

The Phase 6 structural proofs need the shipped coefficient fields to be actual
*fields*, i.e. their moduli to be prime (`FpField.lean` builds `Field (Fp p)`
from `[Fact (Nat.Prime p)]`). These moduli are **not** numbers we chose: they
are the scalar-field orders of standardised pairing-friendly curves, **prime by
construction** (the curve is generated so that the pairing-group order is
prime) and re-checked by every conforming implementation.

We therefore *assume* their primality as two **cited axioms**, rather than
proving it. This is a deliberate, bounded trusted-base decision, a cited,
standardised constant in the same pragmatic family as the project's existing
`native_decide` / FFI concessions, **not** an arbitrary primality assertion:

* the axiom references the canonical modulus definition (`bn254FrModulus` /
  `blsFrModulus` from `LeanPoseidon.Field`), so there is no re-typed-literal
  transcription risk;
* it is attested by the curve specifications, BN254 (`alt_bn128`):
  [EIP-196](https://eips.ethereum.org/EIPS/eip-196) /
  [EIP-197](https://eips.ethereum.org/EIPS/eip-197) and the
  Barreto–Naehrig construction; BLS12-381: the BLS12-381 specification;
* **policy:** only standardised, literature-attested prime-field moduli may be
  axiomatised this way; arbitrary primality facts must be proved.

Each axiom is swappable, in one line, for a kernel-checked Pratt/Lucas
certificate (mathlib `lucas_primality`; a BN254 certificate already exists in
the Verified-zkEVM `CompPoly` library). `instance … := ⟨bn254FrModulus_prime⟩`
becomes `⟨theCertificate⟩` with no other change. The axioms' blast radius is
exactly the concrete `Bn254Fr` / `Bls12Fr` specialisations of the structural
theorems; the generic theorems (over `[Fact (Nat.Prime p)]`) cite none of them.
-/

namespace LeanPoseidon

/-- **Cited axiom.** The BN254 (`alt_bn128`) scalar-field order is prime, a
standardised curve parameter (EIP-196/197; Barreto–Naehrig construction), prime
by construction. References the canonical `bn254FrModulus`. See the module
docstring for the trusted-base rationale and the certificate upgrade path. -/
axiom bn254FrModulus_prime : Nat.Prime bn254FrModulus

/-- **Cited axiom.** The BLS12-381 scalar-field order is prime, a standardised
curve parameter, prime by construction. References the canonical `blsFrModulus`.
See the module docstring. -/
axiom blsFrModulus_prime : Nat.Prime blsFrModulus

/-- `Bn254Fr` is a field: its modulus is (axiomatically) prime. This is what
lets `FpField`'s `instance [Fact (Nat.Prime p)] : Field (Fp p)` specialise to
`Bn254Fr`. -/
instance : Fact (Nat.Prime bn254FrModulus) := ⟨bn254FrModulus_prime⟩

/-- `Bls12Fr` is a field: its modulus is (axiomatically) prime. -/
instance : Fact (Nat.Prime blsFrModulus) := ⟨blsFrModulus_prime⟩

end LeanPoseidon
