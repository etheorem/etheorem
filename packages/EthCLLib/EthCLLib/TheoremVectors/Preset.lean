import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement

/-!
# `EthCLLib.TheoremVectors.Preset`: binding one preset

Phase B1 (`THEOREM_VECTORS_ARCHITECTURE.md` §10): fix the statement's instance binders to
the fork binding's constants for one preset. The four known seams answer
from the binding, one table (§10's binder table); an unknown seam is a
reader skip (§7.5) that never reaches this module. The preset-free type
check (§10) lives here too: it answers whether an input type mentions the
preset at all, which is what lets a scalar witness move from an earlier
preset to a later one.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The instance constant one seam binds to at one preset (`THEOREM_VECTORS_ARCHITECTURE.md`
§10). An `.other` seam has no constant: the reader already reported it, so
this answers an error the command turns into a build failure if it ever
sees one. -/
def Preset.constOf (binding : ForkBinding) (p : PresetId) :
    InstanceKind → Except String Name
  | .preset =>
    match binding.presets.find? fun (q, _) => q == p with
    | some (_, inst) => .ok inst.preset
    | none =>
      .error s!"theorem_vectors: the `{binding.tag}` binding has no \
        {p.tag} preset"
  | .config =>
    match binding.presets.find? fun (q, _) => q == p with
    | some (_, inst) => .ok inst.config
    | none =>
      .error s!"theorem_vectors: the `{binding.tag}` binding has no \
        {p.tag} preset"
  | .hasherTag => .ok binding.hasherTag
  | .cryptoBackend => .ok binding.crypto
  | .other c =>
    .error s!"theorem_vectors: the `{binding.tag}` binding cannot fix an \
      instance of `{c}`"

/-- Does one binder type of a constant name the fork's `Preset` or
`Config` class? The binder's type is an application whose head the
`getAppFn` peel names: `[p : Preset]` and `{p : Preset}` both carry the
class constant as the head. -/
private def binderIsPresetBound (presetClass configClass : Name)
    (binderType : Expr) : Bool :=
  match binderType.getAppFn with
  | .const c _ => c == presetClass || c == configClass
  | _ => false

/-- The leading binder types of an expression, innermost first. The
recursion pushes each binder's type after the recursive call, so the
outermost binder lands last. The only caller folds with `any`, so the
order carries no behavior. -/
private def binderTypes : Expr → Array Expr
  | .forallE _ bt b _ => binderTypes b |>.push bt
  | .letE _ _ _ b _ => binderTypes b
  | _ => #[]

/-- Does the constant's type take a binder whose type names the fork's
`Preset` or `Config` class? A constant such as `slotsPerEpoch` takes
`[Preset]`, so any input type that mentions it is preset-bound. A
constant the environment does not know is preset-bound too: the check is
conservative, and doubt answers `true` here so the caller refuses reuse
and runs the fresh search, which is always correct (§10). -/
private def constIsPresetBound (env : Environment) (presetClass configClass : Name)
    (c : Name) : Bool :=
  match env.find? c with
  | none => true
  | some info =>
    (binderTypes info.type).any (binderIsPresetBound presetClass configClass)

/-- Does the expression mention the instance binders' free variables, a
metavariable, or a constant whose type takes the fork's `Preset` or
`Config` class? A pre-order walk, because `Expr` in this toolchain
carries no generic subterm fold. -/
private def mentionsPreset (env : Environment)
    (presetClass configClass : Name) (instFvars : Array Expr) (e : Expr) :
    Bool :=
  match e with
  | .fvar id => instFvars.any fun f => f.fvarId? == some id
  | .mvar _ => true
  | .const c _ => constIsPresetBound env presetClass configClass c
  | .app f a => mentionsPreset env presetClass configClass instFvars f
      || mentionsPreset env presetClass configClass instFvars a
  | .lam _ bt b _ | .forallE _ bt b _ =>
    mentionsPreset env presetClass configClass instFvars bt
      || mentionsPreset env presetClass configClass instFvars b
  | .letE _ bt v b _ =>
    mentionsPreset env presetClass configClass instFvars bt
      || mentionsPreset env presetClass configClass instFvars v
      || mentionsPreset env presetClass configClass instFvars b
  | .mdata _ b | .proj _ _ b =>
    mentionsPreset env presetClass configClass instFvars b
  | _ => false

/-- Is one input type free of the preset (§10)? Two ways a type mentions
the preset: the instance binders' free variables appear in it
(`BeaconState` at this point in the reader's fold is
`BeaconState instFvar…`, and the preset is one of them), or some
constant in it takes the fork's `Preset` or `Config` class
(`Fin (3 * slotsPerEpoch)` mentions `slotsPerEpoch`, whose type takes
`[Preset]`). `Slot` and `UInt64` are free of both. An unknown constant
and a metavariable in the type count as preset-bound, so any doubt
refuses reuse. -/
private def typeIsPresetFree (env : Environment) (binding : ForkBinding)
    (instFvars : Array Expr) (t : Expr) : Bool :=
  let presetClass := binding.fork ++ `Preset
  let configClass := binding.fork ++ `Config
  !(mentionsPreset env presetClass configClass instFvars t)

/-- The preset-free type check (`THEOREM_VECTORS_ARCHITECTURE.md` §10): is every input type
of the statement free of the preset? The command runs this
once per preset's run, before the search, and fills the reuse searcher's
earlier-wins table only when it answers `true`. Facts worth naming: a
`Slot` or `UInt64` input is preset-free, and `Fin (3 * slotsPerEpoch)` is
preset-bound, because `slotsPerEpoch`'s own type takes the fork's
`Preset` class; every `BeaconState` is preset-bound, both through the
container's fields and through the instance free variables the reader
left in the type. The check is conservative in one direction: any doubt
answers `false`, which sends the disjunct to the fresh search, and the
fresh search is always correct.

`ctx.stmt.inputs[i].type` still mentions the telescope's instance free
variables, which is why the answer needs `ctx.instFvars` beside the
environment. -/
def Preset.presetFree (env : Environment) (binding : ForkBinding)
    (ctx : StatementCtx) : Bool :=
  ctx.stmt.inputs.all fun i => typeIsPresetFree env binding ctx.instFvars i.type

end EthCLLib.TheoremVectors
