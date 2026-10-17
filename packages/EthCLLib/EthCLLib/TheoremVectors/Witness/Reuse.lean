import Lean
import EthCLLib.TheoremVectors.Witness.Searcher

/-!
# `EthCLLib.TheoremVectors.Witness.Reuse`: the witness-reuse searcher

The reuse searcher (`THEOREM_VECTORS_ARCHITECTURE.md` §10). A witness won at
a preset earlier in the line's preset list carries to a later preset of
the same line when it passes the later preset's check. The searcher sits
immediately after the hint searcher on every searcher list. That position
keeps §9.8's replay promise: a committed second-preset hint replays as
`.hinted (.reused p)`, and a fresh run wins as `.reused p` and writes
that hint entry, so a later build replays it. (§3's B2 sketch drew the
reuse searcher before the search; the placement after the hint searcher
is a recorded deviation.)

The searcher proposes only; the search loop's `safe` and `check` gates
arbitrate, and a failed check falls through to the later searchers, which
is the fresh search §10 sends a rejected witness to. The loop
(`searchDisjunct`) never changed for this.

The module lives beside `Witness.Searcher` and imports only it. The type
check that gates reuse, `Preset.presetFree`, sits in `Preset.lean`,
which `Probe` imports; `Probe` cannot import back from here, so a
`SearchCtx` field (`earlierWins`) carries the wins across that seam and
this module reads them out of the context. That is also why the searcher
cannot live in `Preset.lean`: `Witness.Searcher` defines the
`WitnessSearcher` shape the searcher must take, and `Preset.lean` sits
below it in the import order.
-/

set_option autoImplicit false

namespace EthCLLib.TheoremVectors

/-- The witness-reuse searcher (`THEOREM_VECTORS_ARCHITECTURE.md` §10). It applies when the
statement has no block inputs, every input is a scalar, the line named no
manual terms, and an earlier preset of this line won this exact
`(disjunct index, side)`; the command filled the context's table only
when the statement passed `Preset.presetFree`, so a matching entry is
preset-free by construction. The manual gate keeps §18's claim checkable:
a fully-covering set of manual terms must win its own disjunct at every
preset, so a manual line never carries its witness over. The tag is
a placeholder that never names a record: every candidate carries its own
origin in `tag?`, so the record names `reused-<fromPreset>`, and the tag
shows only in a `notFound` reason's tried list. -/
def reuseSearcher : WitnessSearcher where
  tag := .reused PresetId.minimal
  applies ctx stmt d :=
    stmt.blockInputs.isEmpty &&
    (stmt.scalarKinds.all Option.isSome) &&
    ctx.probe.manuals.isEmpty &&
    ctx.earlierWins.any fun w => w.disjunctIndex == d.index && w.side == d.side
  search ctx _ d := do
    match ctx.earlierWins.find? fun w => w.disjunctIndex == d.index && w.side == d.side with
    | some w => pure (.candidate w.assignment (some (.reused w.fromPreset)))
    | none => pure (.nothing)

end EthCLLib.TheoremVectors
