import Lean

/-!
# `EthCLLib.TheoremVectors.Scalar`: the scalar family the solver takes

The scalar analysis the witness search shares (`THEOREM_VECTORS_ARCHITECTURE.md`
§9.4). One place names the scalar kinds, their SSZ wire widths, and the
literal form each kind takes in a hypothesis; the bit-vector source
(§9.4), the random source (§9.4), and the probe's container reads (§11.1)
all read it, so a wire width or a literal form is defined once.

## Lean idioms annotated

- `MetaM` in a `def`'s type: `scalarKind` runs instance-free whnf with
  reducible transparency, so an alias (`Gwei` for `UInt64`) reduces before
  the head constant is read.
- `whnf` over `Nat.decLt` extracts the proof of a literal comparison
  (`⟨v, pf⟩`'s `pf`), the way `Decidable.decide`'s instance carries it.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The scalar shape of an input type, after the reducible aliases
(`Slot`, `Gwei`, and the other SSZ aliases) reduce (§9.4). -/
inductive ScalarKind where
  /-- `Bool`, one byte. -/
  | bool
  /-- `Nat`, eight bytes on the wire, the same width the probe's `Nat`
  reads take. -/
  | nat
  /-- A fixed-width unsigned integer at its byte width. -/
  | uint (width : Nat)
  /-- `Fin n`, the `uintN 64` encoding of `Fin.val` (§11.2). -/
  | fin (n : Expr)
  deriving Repr, BEq

/-- The scalar kind of a type, `none` for everything the solver's wire
form does not cover: the container types, and anything else. -/
def scalarKind (ty : Expr) : MetaM (Option ScalarKind) := do
  let t ← Meta.withReducible (Meta.whnf ty)
  match t with
  | .const c _ =>
    match c with
    | ``Bool   => return some .bool
    | ``Nat    => return some .nat
    | ``UInt64 => return some (.uint 64)
    | ``UInt32 => return some (.uint 32)
    | ``UInt16 => return some (.uint 16)
    | ``UInt8  => return some (.uint 8)
    | _        => return none
  | .app (.const ``Fin _) n => return some (.fin n)
  | _ => return none

/-- The little-endian `uintN` bytes of `v` at byte width `w`, the SSZ wire
form of the scalar family (§9.4's "serialization of each value to its SSZ
width"). -/
def leBytes (w : Nat) (v : Nat) : ByteArray :=
  ByteArray.mk ((Array.range w).map fun i =>
    UInt8.ofNat ((v / 2 ^ (8 * i)) % 256))

/-- The SSZ bytes of one scalar value at its kind (§9.4). -/
def scalarBytes (k : ScalarKind) (v : Nat) : ByteArray :=
  match k with
  | .bool => leBytes 1 (v % 2)
  | .nat | .uint 64 => leBytes 8 v
  | .uint 32 => leBytes 4 v
  | .uint 16 => leBytes 2 v
  | .uint 8 => leBytes 1 v
  | .uint _ => leBytes 8 v
  | .fin _ => leBytes 8 v

/-- The byte width one scalar kind takes on the wire. -/
def ScalarKind.width : ScalarKind → Nat
  | .bool => 1
  | .nat => 8
  | .uint w => w / 8
  | .fin _ => 8

/-- The little-endian read of a scalar's wire bytes back to `Nat`, `none`
when the byte string is not exactly the kind's width (§9.3's strict
decode). The random source reads the probe's serialized container reads
back through this (§9.4). -/
def scalarNatOf (k : ScalarKind) (b : ByteArray) : Option Nat :=
  if b.size != k.width then none
  else
    some <| (Array.range b.size).foldl (fun acc i =>
      acc + (if h : i < b.size then (b.get i h).toNat * 2 ^ (8 * i) else 0)) 0

/-- The proof of `v < n` that `Nat.decLt` reduces to, for a `v` literal
and an `n` that reduces to one. `Fin`'s literal form needs it: `⟨v, pf⟩`
carries the bound, and no `Inhabited`-style instance can (§11.2). -/
private def natLtProof (v : Nat) (n : Expr) : MetaM (Option Expr) := do
  let inst := mkAppN (.const ``Nat.decLt []) #[mkRawNatLit v, n]
  match ← (try Meta.whnf inst catch _ => pure inst) with
  | .app (.const ``Decidable.isTrue _) pf => return some pf
  | _ => return none

/-- Every fvar id in `e`, each once. The witness search's walkers (the
read grounding, the read plan, the `Fin` bridge) share it. -/
partial def collectFVarIds (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .fvar id => if acc.contains id then acc else acc.push id
  | .app f a => collectFVarIds a (collectFVarIds f acc)
  | .lam _ t b _ => collectFVarIds b (collectFVarIds t acc)
  | .letE _ t v b _ => collectFVarIds b (collectFVarIds v (collectFVarIds t acc))
  | .forallE _ t b _ => collectFVarIds b (collectFVarIds t acc)
  | .mdata _ b => collectFVarIds b acc
  | .proj _ _ b => collectFVarIds b acc
  | _ => acc

/-- The literal form of one scalar value at its input type: the form a
fixed scalar takes when a source substitutes it into the hypotheses
(§9.4's read substitution). `none` when the type has no literal form the
substitution can write: a `Fin` whose bound does not reduce to a literal,
or a type outside the scalar family. -/
def literalTerm (ty : Expr) (v : Nat) : MetaM (Option Expr) := do
  match ← scalarKind ty with
  | some .bool => return some (.const (if v == 0 then ``Bool.false else ``Bool.true) [])
  | some .nat => return some (mkRawNatLit v)
  | some (.uint _) =>
    let lit := mkRawNatLit v
    let inst? ← try
      some <$> Meta.synthInstance
        (mkAppN (.const ``OfNat [levelZero]) #[ty, lit])
    catch _ =>
      pure none
    match inst? with
    | some inst => return some (mkAppN (.const ``OfNat.ofNat [levelZero]) #[ty, lit, inst])
    | none => return none
  | some (.fin n) => do
    let some pf ← natLtProof v n | return none
    return some (mkAppN (.const ``Fin.mk []) #[n, mkRawNatLit v, pf])
  | none => return none

end EthCLLib.TheoremVectors
