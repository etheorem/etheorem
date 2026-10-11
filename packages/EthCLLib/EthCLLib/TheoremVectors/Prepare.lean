import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Statement
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.TheoremVectors.Prepare`: the prepare pass

The prepare pass turns a `Statement` into the array of search problems the
sources solve (`THEOREM_VECTORS_ARCHITECTURE.md` §8). One pass, five steps:

1. **Sides** (§8.3). An `.iffTrue` conclusion doubles the problem: one side
   adds `q` to the statement's hypotheses, the other adds `¬q`. Every other
   shape runs one side with the statement's own hypotheses.
2. **Zeta.** A hypothesis or a side may name scratch values in `let`s
   (`canBuilderCoverBid_iff`'s right side does); the pass substitutes them
   before anything else looks at the term.
3. **Unfold** (§8.1). A hypothesis stated through a spec predicate is one
   opaque atom to a solver. The pass runs `simp only` with the equation
   lemmas of every captured spec function the hypothesis names, the
   `UInt64`-to-`Nat` bridge lemmas oriented back toward `UInt64` form, and
   the `Bool` normalization lemmas. Crypto predicates are not captured spec
   functions, so they stay as they are (§8.1).
4. **Split** (§8.2). The unfolded conjunction goes to disjunctive normal
   form, one `Case` per disjunct, with a structural walk that pushes `∨`
   out and applies De Morgan one `¬` at a time. The walk never enters a
   quantifier, so a gate such as `∀ i, p i` stays one atom. The disjunct
   cap is the `theorem_vectors.maxCases` option (§14.4); a theorem over the
   cap falls back to one case with the unsplit hypothesis and the pass
   reports the fallback (§8.2).
5. **Decidability** (§8.4). Every source ends with `decide` on its
   candidate, so every case must carry a `Decidable` instance for its
   conjunction. The pass synthesizes it once, at build time, over the
   statement's binders, and stores it beside the conjunction; the probe
   substitutes the instance binders into it (§11.2). A case whose synthesis
   fails is reported and dropped (§8.4).

## Lean idioms annotated

- `Meta.synthInstance` runs ordinary instance search on a `Prop` goal. It
  returns a term that may mention the statement's instance binders, which is
  why the pass, the probe, and everything downstream run inside the reader's
  telescope scope (`Statement.readIn`).
- `mkAnd` builds the conjunction right-associated, so the `Decidable` chain
  reads outermost-first, the binder order.
- The programmatic `simp only` introduces each hypothesis as a local
  declaration and hands its `FVarId` to `Simp.simpGoal` with
  `simplifyTarget := false`; simp re-asserts the hypothesis under the same
  user name (`Main.lean`'s `toAssert` carries `localDecl.userName`), so the
  pass reads the rewritten type back by name.
- `SimpTheorems.addConst` on a function name adds its equation lemmas, the
  same set `simp only [f]` would use.
-/

set_option autoImplicit false

open Lean
open Lean.Meta

namespace EthCLLib.TheoremVectors

/-- One search problem: a conjunction of hypotheses over the inputs
(`THEOREM_VECTORS_ARCHITECTURE.md` §5.4). The prepare pass produces one per DNF disjunct,
times two for `.iffTrue`. The conjunction and its `Decidable` instance sit
beside the conjuncts so the probe does not re-derive either (§8.4). -/
structure Case where
  /-- The case's position, which names its record directory (§12.1). -/
  index : Nat
  /-- The `.iffTrue` side this case serves, when the shape is `.iffTrue`
  (§8.3). -/
  side  : Option Bool
  /-- The conjuncts, in binder order, binders still free. -/
  hyps  : Array Expr
  /-- The conjunction of `hyps`, as one `Prop`. -/
  conj  : Expr
  /-- The `Decidable` instance of `conj` (§8.4). -/
  decidable : Expr
  deriving Inhabited

/-- The right-associated conjunction of the hypotheses, `True` for none. -/
def conjunction (hyps : Array Expr) : Expr :=
  hyps.foldr (fun h acc => mkApp2 (.const ``And []) h acc) (.const ``True [])

/-- `¬ e`. -/
def mkNot (e : Expr) : Expr :=
  mkApp (.const ``Not []) e

/-! ## The UInt64-to-Nat bridge lemmas (§8.1), oriented back toward `UInt64`

The corpus states several scalar bounds at the `Nat` level, through
`.toNat`. The bit-vector solver reads `UInt64` form, so the bridge lemmas
here face that way: their left sides are the `Nat`-level shapes the proofs
wrote. A hypothesis whose `Nat` arithmetic has no `UInt64` image
(`a.toNat + n = b.toNat` for `n > 1`, say) does not match any of them and
stays out of the solver's reach, as the plan's risk note predicts. -/

/-- `a.toNat < b.toNat` reads back as `a < b`. -/
theorem uint64_toNat_lt_iff {a b : UInt64} : a.toNat < b.toNat ↔ a < b :=
  ⟨UInt64.lt_iff_toNat_lt.mp, UInt64.lt_iff_toNat_lt.mpr⟩

/-- `a.toNat ≤ b.toNat` reads back as `a ≤ b`. -/
theorem uint64_toNat_le_iff {a b : UInt64} : a.toNat ≤ b.toNat ↔ a ≤ b :=
  ⟨UInt64.le_iff_toNat_le.mp, UInt64.le_iff_toNat_le.mpr⟩

/-- `a.toNat = b.toNat` reads back as `a = b`. -/
theorem uint64_toNat_eq_iff {a b : UInt64} : a.toNat = b.toNat ↔ a = b :=
  UInt64.toNat_inj

/-- The successor form of a `Nat`-level `UInt64` equality reads toward
`UInt64`: `slot.toNat + 1 = curSlot.toNat` is `slot + 1 = curSlot` with the
guard `curSlot ≠ 0`, which excludes `slot` at `UInt64.max`. The guard is a
`UInt64` comparison, so the rewritten hypothesis stays in the solver's
fragment. -/
theorem uint64_toNat_add_one_eq {a b : UInt64} :
    a.toNat + 1 = b.toNat ↔ a + 1 = b ∧ b ≠ 0 := by
  have toNatOfZero : (0 : UInt64).toNat = 0 :=
    UInt64.toNat_ofNat_of_lt (by decide)
  constructor
  · intro h
    have hlt : a.toNat + 1 < 2 ^ 64 := by
      rw [h]
      exact b.toNat_lt
    refine ⟨UInt64.toNat_inj.mp ?_, ?_⟩
    · rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt (by decide),
        Nat.mod_eq_of_lt hlt]
      exact h
    · intro h0
      have h1 : a.toNat + 1 = b.toNat := h
      rw [h0, toNatOfZero] at h1
      exact Nat.succ_ne_zero a.toNat h1
  · intro ⟨h, hb0⟩
    have h1 : (a + 1).toNat = b.toNat := UInt64.toNat_inj.mpr h
    have hbNat : b.toNat ≠ 0 := by
      intro h0
      exact hb0 (UInt64.toNat_inj.mp (by rw [h0, toNatOfZero]))
    have h2 : (a + 1).toNat ≠ 0 := by
      intro h0
      rw [h1] at h0
      exact hbNat h0
    have h3 : (a + 1).toNat = a.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt (by decide)]
      by_cases hlt : a.toNat + 1 < 2 ^ 64
      · exact Nat.mod_eq_of_lt hlt
      · exfalso
        apply h2
        have hle : a.toNat + 1 ≤ 2 ^ 64 := Nat.lt_iff_add_one_le.mp a.toNat_lt
        have hge : 2 ^ 64 ≤ a.toNat + 1 := Nat.le_of_not_lt hlt
        have heq : a.toNat + 1 = 2 ^ 64 :=
          Nat.le_antisymm hle hge
        show (a + 1).toNat = 0
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt (by decide), heq,
          Nat.mod_self]
    rw [← h3]
    exact h1

/-- Zeta-reduce the leading `let`s of a term. A side or hypothesis may name
scratch values between itself and its comparisons
(`canBuilderCoverBid_iff`'s right side does); substituting the values is the
whole reduction. Public, because the probe's `.iffTrue` run needs the same
reduction before it synthesizes the sides' `Decidable` instances. -/
partial def Prepare.zeta (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => Prepare.zeta (b.instantiate1 v)
  | _ => e

/-- The size of an expression, one node each. -/
private partial def exprSize (e : Expr) (acc : Nat) : Nat :=
  match e with
  | .app f a => exprSize a (exprSize f (acc + 1))
  | .lam _ t b _ => exprSize b (exprSize t (acc + 1))
  | .letE _ t v b _ => exprSize b (exprSize v (exprSize t (acc + 1)))
  | .forallE _ t b _ => exprSize b (exprSize t (acc + 1))
  | .mdata _ b => exprSize b (acc + 1)
  | .proj _ _ b => exprSize b (acc + 1)
  | _ => acc + 1

/-- The body-size cutoff of the unfold (§8.1): a captured spec function
whose definition exceeds this many expression nodes stays one atom, and the
bit-vector source grounds the closed call in compiled code instead (§9.4). -/
def unfoldBodyCutoff : Nat := 100

/-- The simp step budget of one hypothesis's unfold (§8.1). The budget keeps
a predicate whose equations unfold into a fold or a `do` block from burning
the command's heartbeats; §8.2's cap is the split-side answer, this is the
unfold-side one. -/
def unfoldStepBudget : Nat := 128

/-- The captured spec functions a hypothesis names (§8.1), restricted to
the ones with a small body. `isSpecFunction` is the forkdef test, so crypto
predicates and preset constants stay out. A forkdef whose body is a fold
over a state container (a pending-balance sum, say) unfolds into a term
whose simp walk burns the command's heartbeats without exposing a single
comparison, so the pass leaves those to the bit-vector source, which
evaluates the closed call in compiled code instead (§9.4). -/
private def unfoldNames (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let candidates := e.getUsedConstants.filter (EthCLLib.Internal.isSpecFunction env)
  candidates.filterM fun n => do
    match env.find? n with
    | some (.defnInfo v) => pure (exprSize v.value 0 < unfoldBodyCutoff)
    | _ => pure false

/-- The `simp only` context for one hypothesis (§8.1): the named spec
functions as unfold targets, plus the bridge lemmas and `Bool`
normalization as rewrite rules. The `bne` / `ne` pair turns the corpus's
`((vi &&& flag) != 0) = true` form into the `¬(… = 0)` the solver's
fragment takes. -/
private def mkUnfoldCtx (names : Array Name) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  -- the captured spec functions unfold by their equation lemmas, the way
  -- `simp only [f]` unfolds a function
  for n in names do
    thms ← thms.addDeclToUnfold n
  for n in #[``uint64_toNat_lt_iff, ``uint64_toNat_le_iff, ``uint64_toNat_eq_iff,
             ``uint64_toNat_add_one_eq, ``UInt64.not_lt, ``UInt64.not_le,
             ``bne_iff_ne, ``ne_eq,
             ``decide_eq_true_eq, ``Bool.and_eq_true,
             ``Bool.or_eq_true, ``Bool.not_eq_true] do
    thms ← thms.addConst n
  -- the step budget keeps a predicate whose equations unfold into a fold
  -- or a `do` block from burning the command's heartbeats (§8.2's cap is
  -- the split-side answer; this is the unfold-side one). Instance
  -- discharge stays off: the fold bodies' `if _ == _ then` conditions
  -- would otherwise pull `Decidable` synthesis over SSZ types.
  Simp.mkContext { failIfUnchanged := false, maxSteps := unfoldStepBudget,
                   instances := false, maxDischargeDepth := 0 }
    (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)

/-- Unfold one hypothesis (§8.1): `simp only` over the spec functions it
names, with the bridge and `Bool` sets. A hypothesis that names no captured
spec function still goes through the bridge set, whose rewrites need no
spec function; a simp failure leaves the hypothesis as it was. A
hypothesis simp closes (its negation followed from the others, or it
reduced to a contradiction) becomes `False`, so the split keeps the case
and the search reports it unsatisfiable; a hypothesis simp drops became
trivial and becomes `True`. -/
def Prepare.unfoldHyp (e : Expr) : MetaM Expr := do
  let names ← unfoldNames e
  let run : MetaM (Option Expr) := do
    let ctx ← mkUnfoldCtx names
    Meta.withLocalDeclD `tvHyp e fun h => do
      let g ← mkFreshExprMVar (mkConst ``True [])
      let (res?, _) ← simpGoal g.mvarId! ctx (simplifyTarget := false)
        (fvarIdsToSimp := #[h.fvarId!])
      match res? with
      | none => return some (.const ``False [])
      | some (_, g') =>
        let lctx ← g'.withContext getLCtx
        match lctx.findFromUserName? `tvHyp with
        | some d => return some d.type
        | none => return some (.const ``True [])
  match ← (try run catch _ => pure none) with
  | some e' => return e'
  | none => return e

/-- The disjunctive normal form of one proposition, as one conjunction per
disjunct (§8.2). `none` when the split exceeds `cap`. The walk pushes `∨`
out and applies De Morgan over `∧`; it never enters a quantifier or an
atom, so a gate stays one conjunct. -/
private partial def dnfCases (cap : Nat) (e : Expr) : Option (Array (Array Expr)) :=
  match e.getAppFn, e.getAppArgs with
  | .const c _, args =>
    if c == ``Or && args.size == 2 then
      match dnfCases cap args[0]! with
      | some x =>
        match dnfCases cap args[1]! with
        | some y => if x.size + y.size > cap then none else some (x ++ y)
        | none => none
      | none => none
    else if c == ``Not && args.size == 1 then
      match args[0]!.getAppFn with
      | .const c' _ =>
        let args' := args[0]!.getAppArgs
        if c' == ``And && args'.size == 2 then
          match dnfCases cap (mkNot args'[0]!) with
          | some x =>
            match dnfCases cap (mkNot args'[1]!) with
            | some y => if x.size + y.size > cap then none else some (x ++ y)
            | none => none
          | none => none
        else some #[#[e]]
      | _ => some #[#[e]]
    else if c == ``And && args.size == 2 then
      match dnfCases cap args[0]! with
      | some x =>
        match dnfCases cap args[1]! with
        | some y =>
          if x.size * y.size > cap then none
          else some (x.flatMap fun xc => y.map (fun yc => xc ++ yc))
        | none => none
      | none => none
    else some #[#[e]]
  | _, _ => some #[#[e]]

/-- The pass's full form (§8): sides, zeta, unfold, DNF split with the cap,
and the `Decidable` synthesis of §8.4. Returns the cases, in side order
(true side first for `.iffTrue`), plus the report lines: the dropped cases'
reasons and the cap fallback's. -/
def Prepare.pass (stmt : Statement) : MetaM (Array Case × Array String) := do
  let cap := theorem_vectors.maxCases.get (← getOptions)
  -- §8.3: the `.iffTrue` sides. `q` carries `let`s in the corpus
  -- (`canBuilderCoverBid_iff`), so zeta applies before anything else.
  let sides : Array (Option Bool × Array Expr) :=
    match stmt.shape with
    | .iffTrue _ q =>
      let q := Prepare.zeta q
      #[(some true, stmt.hyps.push q), (some false, stmt.hyps.push (mkNot q))]
    | _ => #[(none, stmt.hyps)]
  let mut cases : Array Case := #[]
  let mut dropped : Array String := #[]
  let mut capHit := false
  let mut index := 0
  for (side, hyps0) in sides do
    let mut hyps : Array Expr := #[]
    for h in hyps0 do
      hyps := hyps.push (← Prepare.unfoldHyp (Prepare.zeta h))
    -- §8.2: one case per disjunct; over the cap, the unsplit fallback
    let groups ←
      match dnfCases (cap - cases.size) (conjunction hyps) with
      | some g => pure g
      | none =>
        capHit := true
        pure #[hyps]
    for g in groups do
      let conj := conjunction g
      match ← (try some <$> Meta.synthInstance (mkApp (.const ``Decidable []) conj)
        catch _ => pure none) with
      | some dec =>
        cases := cases.push { index, side, hyps := g, conj, decidable := dec }
        index := index + 1
      | none =>
        -- §8.4: a case whose synthesis fails is reported and dropped
        dropped := dropped.push s!"case {index}: no `Decidable` instance for \
          the hypothesis conjunction"
  if capHit then
    dropped := dropped.push s!"the DNF split exceeded the case cap ({cap}); \
      the theorem falls back to the unsplit hypothesis (§8.2)"
  return (cases, dropped)

end EthCLLib.TheoremVectors
