import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Preset
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source

/-!
# `EthCLLib.TheoremVectors.Tests.Support`: the test drives' shared helpers

The scalar read and the search-context construction the toy drives
share. A drive that pins a relation over a witness's scalar value reads
the candidate's bytes through `Support.leOf`, so the pin carries the
relation the case's hypotheses state and the solver's exact choice
stays unpinned. A drive that runs the search
loop builds its context through `Support.searchCtxOf`, so every
construction names the binding, the preset, the output root, and the
cache stamp, and no site fills the remaining fields by hand.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors.Tests.Support

/-- The little-endian read of a scalar's eight wire bytes: byte `i`
counts `2^(8*i)`, and bytes past the end count zero. -/
def leOf (b : ByteArray) : Nat :=
  (Array.range 8).foldl (fun acc i =>
    acc + (if h : i < b.size then (b.get i h).toNat * 2 ^ (8 * i) else 0)) 0

/-- The search context one toy drive needs
(`THEOREM_VECTORS_ARCHITECTURE.md` §9.2): the preset's constants
substituted for the statement's instance binders, no seed terms, a fresh
draw memo, and an empty reuse table. The caller names the binding, the
preset, the output root, and the cache stamp; the toy drives stamp `""`,
because their cache entries live in a scratch tree that dies with the
drive. A drive that needs more (seed terms, a nonempty reuse table)
constructs `SearchCtx` inline. -/
def searchCtxOf (binding : ForkBinding) (p : PresetId)
    (outDir : System.FilePath) (builtStamp : String)
    (stmt : Statement) (ctx : StatementCtx) (info : ProbeInfo)
    (probe : Probe) : MetaM SearchCtx := do
  let instConsts ← stmt.instances.mapM fun (_, kind) =>
    match Preset.constOf binding p kind with
    | .ok c => pure c
    | .error e => throwError e
  return {
    probe := probe, info := info, binding := binding, preset := p,
    inputFvars := ctx.inputFvars, instFvars := ctx.instFvars,
    instConsts := instConsts, seedTerms := #[],
    drawMemo := ← IO.mkRef #[], outDir, builtStamp,
    earlierWins := #[] }

end EthCLLib.TheoremVectors.Tests.Support
