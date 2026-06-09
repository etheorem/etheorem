import LeanPoseidonTests.Ffi

/-!
# `LeanPoseidonTests.Differential`: the `poseidon_fuzz` differential test

Poseidon2 has no centralised official KAT suite, so conformance is
*differential*: generate many "random" inputs, run both the pure-Lean
`permute` and the trusted Rust `zkhash` oracle (`ffiPermute`), and assert
they agree. The committed `Kat.lean` vectors anchor a fixed handful; this
executable extends coverage to thousands of seeded-random states at
runtime.

The PRNG is a pure-Lean **splitmix64** so the trials are *deterministic*
(same seed ⇒ same inputs ⇒ reproducible failures), with no dependence on
system entropy. Each field element is drawn from a full 256-bit splitmix
draw reduced mod `bn254FrModulus`, so inputs cover the whole field, not just small
values.

This is the *only* part of the project that links the Rust oracle, and it
links it into this executable alone, so `lake build LeanPoseidon` and
`lake build LeanPoseidonTests` need no Rust toolchain. The oracle never
appears in the shipped path or in a proof term.

Run with `just fuzz-poseidon` (default 10 000 trials) or
`lake exe poseidon_fuzz <N>`. The trial count is printed (never a silent
cap).
-/

set_option autoImplicit false

namespace LeanPoseidonTests

open LeanPoseidon LeanPoseidon.Poseidon2

/-- One step of the splitmix64 PRNG. Returns `(output, nextState)`. All
`UInt64` arithmetic wraps mod 2⁶⁴ by construction. -/
def splitmixNext (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  let z := z ^^^ (z >>> 31)
  (z, s)

/-- Draw a field element of `Fp p`: four splitmix64 words assembled into a
256-bit `Nat` and reduced mod `p` (so the draw spans the whole field).
Generic over the field, like the permutation it feeds. -/
def nextFp {p : Nat} [NeZero p] (s : UInt64) : Fp p × UInt64 :=
  let (w0, s) := splitmixNext s
  let (w1, s) := splitmixNext s
  let (w2, s) := splitmixNext s
  let (w3, s) := splitmixNext s
  let n := (w0.toNat <<< 192) + (w1.toNat <<< 128) + (w2.toNat <<< 64) + w3.toNat
  (Fp.ofNat n, s)

/-- Draw a width-3 `Fp p` state. -/
def nextState {p : Nat} [NeZero p] (s : UInt64) : Vector (Fp p) 3 × UInt64 :=
  let (a, s) := nextFp s
  let (b, s) := nextFp s
  let (c, s) := nextFp s
  (#v[a, b, c], s)

/-- Run `trials` seeded-random differential comparisons of `permute par`
against the oracle `ffi`, for an instance over field `Fp p`. Throws
(non-zero exit) if any disagree. Generic over the field, the same body
serves every instance. -/
def runDifferential {p : Nat} [NeZero p]
    (label : String) (par : Params (Fp p)) (ffi : Vector (Fp p) 3 → Vector (Fp p) 3)
    (trials : Nat) (seed : UInt64) : IO Unit := do
  -- Smoke check: the oracle agrees with the in-source anchor before fuzzing.
  let anchor : Vector (Fp p) 3 := #v[Fp.ofNat 0, Fp.ofNat 1, Fp.ofNat 2]
  if ffi anchor ≠ permute par anchor then
    throw <| IO.userError s!"{label}: oracle anchor mismatch — the FFI ABI is broken"
  let mut s := seed
  let mut fails := 0
  for i in [0:trials] do
    let (st, s') := nextState s
    s := s'
    if permute par st ≠ ffi st then
      fails := fails + 1
      IO.eprintln s!"  {label} MISMATCH at trial {i}"
  IO.println s!"  {label}: {trials - fails}/{trials} agreed (lean permute == zkhash oracle)"
  if fails != 0 then
    throw <| IO.userError s!"{label}: {fails}/{trials} differential mismatches"

/-- The `poseidon_fuzz` body. Optional first argument overrides the trial
count (default 10 000). Runs the differential for **both** shipped fields
(BN254 and BLS12-381 at t=3) through the *same* generic `runDifferential`,
demonstrating the field abstraction end to end. Invoked from the top-level
`FuzzMain` exe root (kept out of this test library so Lake compiles a real
exe `main`). -/
def runMain (args : List String) : IO Unit := do
  -- Default 10 000 trials; a present-but-unparseable argument is an error
  -- (rather than silently falling back to the default).
  let trials ← match args.head? with
    | none => pure 10000
    | some a => match a.toNat? with
      | some n => pure n
      | none => throw <| IO.userError s!"poseidon_fuzz: bad trial count {a.quote}"
  IO.println s!"poseidon_fuzz: {trials} seeded-random differential trials per instance (lean vs zkhash oracle)"
  runDifferential "BN254 t=3"  bn254Params ffiPermute      trials 0x0123456789ABCDEF
  runDifferential "BLS12 t=3"  bls12Params ffiPermuteBls12 trials 0x0FEDCBA987654321

end LeanPoseidonTests
