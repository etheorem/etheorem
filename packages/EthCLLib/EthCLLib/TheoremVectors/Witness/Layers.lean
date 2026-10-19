import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Scalar
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Probe

/-!
# `EthCLLib.TheoremVectors.Witness.Layers`: the candidate's byte layers

One home for the layering rule the candidate bytes follow
(`THEOREM_VECTORS_ARCHITECTURE.md` §9.4, §9.8). A position's bytes are the
drawn containers' bytes when a draw covers the position, then the manual
terms' serialized bytes when the author's term covers it, then the fixed
scalar's wire bytes when the fill names it, then the policy's edge. Three
callers assembled the same four layers by hand: the random searcher's
read grounding (`Random.readsBytesAt`), the bit-vector searcher's candidate
builder (`BitVec.buildAssignment`), and the hint searcher's rebuild arms
(`Hint.rebuild`). Their edges are the differences between them, so the
edges are explicit arguments here and each caller passes the one it
carries.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- What the layering answers at a position the drawn bytes, the manual
terms, and the scalar fill all leave open (§9.4, §9.8). -/
inductive FillPolicy where
  /-- Encode the zero/default bytes at the position and go on (§9.4's
  leniency). The read grounding takes this edge: a scalar the fill does
  not name is the solver's to fix, so the layer hands the default encoding
  over and the solve answers at that point. -/
  | default (defaults : Array ByteArray)
  /-- Answer `none` for the whole assignment when the position left open
  is no scalar (§9.8's strictness); a scalar the fill leaves unnamed takes
  its zero encoding first, `layeredAssignment`'s layer 3 (§9.4). The hint
  rebuild takes this edge: a stale hint must not replay, because the
  rebuilt bytes would be a different candidate than the entry recorded,
  and only the check would notice. -/
  | fail

/-- The candidate's bytes for every input, layered (§9.4, §9.8). For each
input position, in binder order:

1. the drawn bytes, when `drawn` holds a pair for the position (a draw
   replaces the author's choice, §9.2);
2. then the manual terms' serialized bytes, when `manuals` holds one;
3. then the fill's wire bytes, `scalarBytes` of the position's scalar kind
   at the value the fill names, or the zero encoding when the fill names
   none and the policy is `.fail`;
4. then the policy's edge: `.default` answers the zero/default encoding
   the caller's `defaults` array carries at the position, `.fail` answers
   `none` for the whole assignment.

The scalar kind is `scalarKind` of the input's type, the same computation
the reader ran to fill `Statement.scalarKinds`, so a caller holding that
table reads the same answers. The answer is `none` only on the `.fail`
edge; the `.default` edge answers every position. -/
def layeredAssignment (stmt : Statement)
    (drawn manuals : Array (Nat × ByteArray)) (fill : Array (Nat × Nat))
    (policy : FillPolicy) : MetaM (Option Assignment) := do
  let mut a : Array ByteArray := #[]
  for i in [0:stmt.inputs.size] do
    match drawn.find? fun (p, _) => p == i with
    | some (_, b) => a := a.push b
    | none =>
      match manuals.find? fun (p, _) => p == i with
      | some (_, b) => a := a.push b
      | none =>
        let k? ← scalarKind stmt.inputs[i]!.type
        match k?, (fill.find? fun (p, _) => p == i).map (·.2) with
        | some k, some v => a := a.push (scalarBytes k v)
        | some k, none =>
          match policy with
          | .fail => a := a.push (scalarBytes k 0)
          | .default defaults => a := a.push (defaults.getD i emptyBytes)
        | none, _ =>
          match policy with
          | .fail => return none
          | .default defaults => a := a.push (defaults.getD i emptyBytes)
  return some a

end EthCLLib.TheoremVectors
