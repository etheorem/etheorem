import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement

/-!
# `EthCLLib.TheoremVectors.Preset`: binding one preset

Phase B1 (`THEOREM_VECTORS_ARCHITECTURE.md` §10): fix the statement's instance binders to
the fork binding's constants for one preset. The four known seams answer
from the binding, one table (§10's binder table); an unknown seam is a
reader skip (§7.5) that never reaches this module. The reuse check (§10)
lands in stage 8; this module binds one preset and nothing else.
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

end EthCLLib.TheoremVectors
