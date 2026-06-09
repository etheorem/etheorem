/-!
# `LeanPoseidon.Field`: a prime field over `Nat`, and the BN254 default

This file provides two things:

* **`Fp (p : Nat)`**: the *prime-field abstraction*, integers mod `p`,
  carried as a `Nat` below the modulus. Generic arithmetic and the byte
  codec are defined once, parameterised by the modulus; adding a field is
  then a modulus (and its `NeZero` proof), not a copy of the arithmetic.
* **`Bn254Fr`**: the library's default coefficient field, an `abbrev`
  for `Fp bn254FrModulus`, where `bn254FrModulus` is the **scalar field**
  order `r` of the BN254 ("alt_bn128") curve (the group order, *not* the
  ~256-bit base-field prime `q`). This is the field Poseidon2's BN254
  `t = 3` instance is defined over.

This realises ARCHITECTURE.md §3 *Abstracting the field* (Phase 4
Stage 10a). The field is shared and construction-agnostic, so it lives at
the top level; the Poseidon2 construction lives under `Poseidon2`.

## For the crypto-fluent reader (the Lean idioms)

* `structure Fp (p : Nat) where val : Nat; isLt : val < p` is the standard
  "bounded `Nat`" encoding of a field element. A `Prop` field like `isLt`
  is **proof-irrelevant** in Lean, two values with the same `val` are
  definitionally equal regardless of *which* proof they carry, which is why
  `DecidableEq (Fp p)` reduces to `DecidableEq` on the `val`.
* `[NeZero p]` (a Lean-core class meaning `p ≠ 0`) is what lets the
  arithmetic discharge the `_ % p < p` bound via `Nat.mod_lt`; for `p = 0`
  the field would be empty and `% 0` the identity. `Bn254Fr` supplies the
  instance from `bn254FrModulus`.
* Why `Nat` and not a Montgomery limb representation? Lean's `Nat` is
  GMP-backed, so `mul` / `mod` on a 254-bit prime are fast both at runtime
  and under `native_decide`. **The abstraction is purely structural: every
  concrete field (including `Bn254Fr`) keeps this `Nat`/GMP representation,
  no typeclass-method indirection at the leaves, so `permute` /
  `compress` reduce in the kernel and under `native_decide` exactly as a
  hand-monomorphised field would.** That is the hot-path constraint
  (ARCHITECTURE.md §3 / Phase 4).
* `ofBytes?` returns `Option` (`?` is the Lean convention for a partial
  function) because a 32-byte value can exceed the modulus; the codec
  **never silently reduces**, it rejects out-of-range input.

## The byte codec is the one home for endianness

`toBytes` / `ofBytes?` are the *single* canonical 32-byte **big-endian**
encoding, pinned against the HorizenLabs `zkhash` reference (whose
`from_hex` reads field elements as `from_be_bytes_mod_order`). 32 bytes
suit any field with `p < 2²⁵⁶` (BN254 and the usual pairing-friendly
scalar fields); the FFI oracle ABI (§8) and any future SSZ binding consume
this codec.
-/

set_option autoImplicit false

namespace LeanPoseidon

/-- The BN254 / alt_bn128 **scalar-field** order, a 254-bit prime `r`,
the modulus of `Bn254Fr`. -/
def bn254FrModulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- `0 < bn254FrModulus`. `decide` settles it by a single GMP comparison on
the literal, no unary unfolding. -/
theorem bn254FrModulus_pos : 0 < bn254FrModulus := by decide

/-- The `NeZero` instance that powers `Bn254Fr`'s arithmetic. -/
instance : NeZero bn254FrModulus := ⟨by decide⟩

/-- A prime-field element: a `Nat` below the modulus `p`, carrying an
erased proof of that bound. Generic over the modulus, `Bn254Fr` (below) is
the `p = bn254FrModulus` instance. -/
structure Fp (p : Nat) where
  /-- The canonical representative in `[0, p)`. -/
  val  : Nat
  /-- Proof that `val` is a canonical (reduced) representative. -/
  isLt : val < p

namespace Fp

variable {p : Nat} [NeZero p]

/-- `0 < p`, from `NeZero p`. Discharges the `_ % p < p` bound below. -/
protected theorem modulus_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)

/-- Reduce an arbitrary `Nat` into `Fp p`. Total: `n % p < p` holds for
every `n` by `Nat.mod_lt`. This is how `Params.lean` builds the
(already-reduced) round constants and how `#guard`s / callers mint literal
field elements without writing a bound proof. -/
def ofNat (n : Nat) : Fp p := ⟨n % p, Nat.mod_lt n Fp.modulus_pos⟩

/-- `0 : Fp p`. -/
protected def zero : Fp p := ⟨0, Fp.modulus_pos⟩

/-- `1 : Fp p` (i.e. `1 % p`, which is `0` only in the degenerate `p = 1`
field). -/
protected def one : Fp p := ⟨1 % p, Nat.mod_lt 1 Fp.modulus_pos⟩

/-- Field addition, reduced mod `p` by construction. -/
protected def add (a b : Fp p) : Fp p := ⟨(a.val + b.val) % p, Nat.mod_lt _ Fp.modulus_pos⟩

/-- Field multiplication, reduced mod `p`. -/
protected def mul (a b : Fp p) : Fp p := ⟨(a.val * b.val) % p, Nat.mod_lt _ Fp.modulus_pos⟩

/-- Additive inverse: `(p - val) % p`. The outer `% p` maps `0 ↦ 0`
(otherwise `p - 0 = p` would be out of range). -/
protected def neg (a : Fp p) : Fp p := ⟨(p - a.val) % p, Nat.mod_lt _ Fp.modulus_pos⟩

/-- Field subtraction, `a + (p - b)` reduced mod `p`. Adding the complement
`p - b.val` (rather than `Nat` subtraction, which truncates at 0) keeps the
result correct when `b.val > a.val`. -/
protected def sub (a b : Fp p) : Fp p := ⟨(a.val + (p - b.val)) % p, Nat.mod_lt _ Fp.modulus_pos⟩

instance : Zero (Fp p)     := ⟨Fp.zero⟩
instance : One (Fp p)      := ⟨Fp.one⟩
instance : Add (Fp p)      := ⟨Fp.add⟩
instance : Mul (Fp p)      := ⟨Fp.mul⟩
instance : Neg (Fp p)      := ⟨Fp.neg⟩
instance : Sub (Fp p)      := ⟨Fp.sub⟩
instance : Inhabited (Fp p) := ⟨Fp.zero⟩

/-- Exponentiation by a `Nat` (for the `x^5` S-box check and field
identities). Structural recursion on the exponent: `a^(n+1) = a^n · a`.
(The shipped S-box in `Poseidon2/Permutation.lean` uses explicit
multiplications `x²·x²·x`, keeping the term `ring`-friendly for the
equivalence proof; this `pow` is for the field-level `#guard`s.) -/
protected def pow (a : Fp p) : Nat → Fp p
  | 0     => Fp.one
  | n + 1 => (Fp.pow a n).mul a

instance : Pow (Fp p) Nat := ⟨Fp.pow⟩

/-- Decidable equality. By proof irrelevance on `isLt` this reduces to
deciding `a.val = b.val` (a fast `Nat` comparison), exactly what
`native_decide` evaluates when checking the anchor KAT. -/
instance : DecidableEq (Fp p) := fun a b =>
  if h : a.val = b.val then
    .isTrue (by cases a; cases b; simp_all)
  else
    .isFalse (by intro he; exact h (congrArg Fp.val he))

/-- Readable error output (the `val`) when a `native_decide` / `#guard`
gate fails, `Fp` carries a proof field, so the default deriving handler
cannot print it. -/
instance : Repr (Fp p) := ⟨fun a _ => repr a.val⟩

/-! ## Byte codec (32-byte big-endian, endianness pinned here)

`toBytes` writes the most-significant byte first; `ofBytes?` reads the same
way and **rejects** (`none`) any 32-byte value `≥ p`. Neither needs
`NeZero` (the bound on a decoded value comes from the explicit `if`). -/

/-- Field-element width in bytes (for `p < 2²⁵⁶`). -/
def byteLen : Nat := 32

/-- 32-byte **big-endian** encoding. Byte `i` (from the front) holds bits
`[8·(31−i), 8·(31−i)+8)` of `val`. -/
def toBytes (a : Fp p) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := byteLen) (fun i =>
    Nat.toUInt8 ((a.val >>> (8 * (byteLen - 1 - i.val))) &&& 0xff)))

/-- Parse a 32-byte **big-endian** buffer into `Fp p`. Returns `none` if the
buffer is not exactly 32 bytes or if the decoded value is `≥ p` (never
silently reduces). `Nat.fold` accumulates most-significant-first. -/
def ofBytes? (bs : ByteArray) : Option (Fp p) :=
  if bs.size = byteLen then
    let n := Nat.fold byteLen (fun i _ acc => acc * 256 + (bs[i]!).toNat) 0
    if h : n < p then some ⟨n, h⟩ else none
  else
    none

end Fp

/-- The library's default field: the BN254 scalar field. An `abbrev` (so
the generic `Fp` instances and `native_decide`-reducibility transfer
unchanged), `= Fp bn254FrModulus`. -/
abbrev Bn254Fr : Type := Fp bn254FrModulus

/-! ## `Bn254Fr` qualified-name re-exports

Dot notation (`x.toBytes`) already resolves through the `Fp` head, but the
*qualified* `Bn254Fr.ofNat` / `Bn254Fr.toBytes` / `Bn254Fr.ofBytes?` forms
used across the package need these aliases (an `abbrev` for an `abbrev`'s
namespace does not auto-inherit the parent's declarations). They specialise
`Fp.*` at `p = bn254FrModulus`. -/

/-- `Bn254Fr.ofNat` = `Fp.ofNat` at the BN254 modulus. -/
abbrev Bn254Fr.ofNat (n : Nat) : Bn254Fr := Fp.ofNat n

/-- `Bn254Fr.toBytes` = `Fp.toBytes` at the BN254 modulus. -/
abbrev Bn254Fr.toBytes (a : Bn254Fr) : ByteArray := Fp.toBytes a

/-- `Bn254Fr.ofBytes?` = `Fp.ofBytes?` at the BN254 modulus. -/
abbrev Bn254Fr.ofBytes? (bs : ByteArray) : Option Bn254Fr := Fp.ofBytes? bs

/-! ## A second field: BLS12-381 `Fr`

The whole point of the abstraction: a different field is *only* a modulus
plus its `NeZero` instance plus the qualified re-exports, **no arithmetic
is rewritten**, and the generic `Poseidon2.permute` / layers work over it
unchanged. `Bls12Fr` is the scalar field of BLS12-381; Poseidon2's BLS12
instance lives in `Poseidon2/Params.lean`. (BLS12-381 `Fr` is a 255-bit
prime, so the shared `< 2²⁵⁶` 32-byte codec applies.) -/

/-- The BLS12-381 scalar-field order `r` (a 255-bit prime). -/
def blsFrModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- The `NeZero` instance powering `Bls12Fr`'s arithmetic. -/
instance : NeZero blsFrModulus := ⟨by decide⟩

/-- The BLS12-381 scalar field, `Fp blsFrModulus`. -/
abbrev Bls12Fr : Type := Fp blsFrModulus

/-- `Bls12Fr.ofNat` = `Fp.ofNat` at the BLS12-381 modulus. -/
abbrev Bls12Fr.ofNat (n : Nat) : Bls12Fr := Fp.ofNat n
/-- `Bls12Fr.toBytes` = `Fp.toBytes` at the BLS12-381 modulus. -/
abbrev Bls12Fr.toBytes (a : Bls12Fr) : ByteArray := Fp.toBytes a
/-- `Bls12Fr.ofBytes?` = `Fp.ofBytes?` at the BLS12-381 modulus. -/
abbrev Bls12Fr.ofBytes? (bs : ByteArray) : Option Bls12Fr := Fp.ofBytes? bs

/-! ## Acceptance gates

`#guard` evaluates a decidable proposition at compile time and fails the
build if it is false. These exercise the concrete `Bn254Fr`; a final
generic gate confirms the abstraction works at a *different* modulus too. -/

-- `(r − 1) + 1 = 0`: the additive identity wraps at the modulus.
#guard Bn254Fr.ofNat (bn254FrModulus - 1) + 1 = 0

-- The `x ↦ x⁵` S-box on a small input: `2⁵ = 32`.
#guard (Bn254Fr.ofNat 2) ^ 5 = Bn254Fr.ofNat 32

-- Multiplication reduces mod the modulus: `(r − 1)² ≡ 1`.
#guard (Bn254Fr.ofNat (bn254FrModulus - 1)) * (Bn254Fr.ofNat (bn254FrModulus - 1)) = 1

-- Codec width and round-trips.
#guard (Bn254Fr.toBytes (Bn254Fr.ofNat 5)).size = Fp.byteLen
#guard Bn254Fr.ofBytes? (Bn254Fr.toBytes (Bn254Fr.ofNat 0))       = some (Bn254Fr.ofNat 0)
#guard Bn254Fr.ofBytes? (Bn254Fr.toBytes (Bn254Fr.ofNat 12345))   = some (Bn254Fr.ofNat 12345)
#guard Bn254Fr.ofBytes? (Bn254Fr.toBytes (Bn254Fr.ofNat (bn254FrModulus - 1)))
         = some (Bn254Fr.ofNat (bn254FrModulus - 1))

-- A 32-byte all-`0xff` buffer decodes to `2²⁵⁶ − 1 ≥ r`, so it is rejected.
#guard Bn254Fr.ofBytes? (ByteArray.mk (Array.replicate 32 0xff)) = none

-- The second field runs through the *same* code: in `Bls12Fr`, `(r−1)+1 = 0`.
#guard Bls12Fr.ofNat (blsFrModulus - 1) + 1 = 0

-- The abstraction is real: the *same* `Fp` arithmetic works at another
-- modulus. In `Fp 7`, `5 + 4 = 9 ≡ 2` and `3 · 4 = 12 ≡ 5`.
section
private instance : NeZero (7 : Nat) := ⟨by decide⟩
#guard (Fp.ofNat 5 + Fp.ofNat 4 : Fp 7) = Fp.ofNat 2
#guard (Fp.ofNat 3 * Fp.ofNat 4 : Fp 7) = Fp.ofNat 5
end

end LeanPoseidon
