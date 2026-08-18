import EthCLLib.Spec.Forms

/-!
# `EthCLLib.Spec.Tiers`: the per-fork `Preset` / `Config` classes

Four capturing forms declare a fork's two threaded tiers and the concrete value
sets the runner injects (`FRAMEWORK_ARCHITECTURE.md` §4):

* `forkpreset where …` / `forkconfig where …` declare the fork's `Preset` /
  `Config` class.
* `forkpresetvalues minimal where …` / `forkconfigvalues minimalConfig where …`
  declare one injected `@[reducible] def` value set.

Each fork owns its own classes, so a Gloas function constrains `[Gloas.Preset]`
and never mentions Fulu. What the author writes is the fork's **diff**; the form
merges the lineage's diffs by entry name (child-most-wins) and emits one flat
class, so a grandchild composes transitively without restating a grandparent's
fields. `inherit` cannot do this job: a class is one declaration, and per-name
replay has no way to fuse two of them.

## The downgrade instance

Per-fork classes create two unrelated instance families, and the fork-upgrade
boundary sits between them. `upgradeToGloas` copies a
`Vector Root Fulu.Const.slotsPerHistoricalRoot` field into a
`Vector Root Gloas.Const.slotsPerHistoricalRoot` field *symbolically*, before any
concrete preset is injected, and for unrelated classes those cap types are not
defeq.

So a child's `forkpreset` also emits

```lean
namespace Downgrade
@[reducible] scoped instance toFuluPreset [Preset] : Fulu.Preset := { … }
end Downgrade
```

projecting every parent field out of the child's class. The upgrade then runs
under a single `[Gloas.Preset]` binder: the Fulu side's instance is a reducible
structure literal, `Fulu.Preset.slotsPerHistoricalRoot (toFuluPreset)` reduces by
iota to the Gloas field, and cap-type defeq holds with the preset still symbolic.
The runner gets the same bridge for free, injecting only `Gloas.minimal` and
reaching the Fulu spine through the projection.

The `Downgrade` sub-namespace is what contains it. `scoped` on its own would
not: a fork's body files all sit *inside* the fork's namespace, where a scoped
instance is already active. One namespace deeper, only a file that writes
`open scoped Downgrade` can satisfy a parent-class constraint, so the two
boundary files (`Upgrade.lean`, `Interface.lean`) declare the reach in one line
and everything else stays sealed. The fork author never writes the parent's name;
the form reads it from `lineageExt`.
-/

set_option autoImplicit false

open Lean Elab Command
open EthCLLib.Internal

namespace EthCLLib.Spec

/-! ## Entry syntax

Two entry shapes, deliberately narrower than Lean's `structFields`: a tier is a
flat list of `name : type` fields or `name := value` assignments, and nothing
else. Both put the name at index 1, so `tierEntryName` reads either.

These two are plain (not `scoped`) syntax abbreviations, which Lean's `syntax _
:= _` form does not accept a visibility modifier on. They name no author-facing
command; only the four `fork*` commands below reference them. -/

/-- One field of a tier class: `slotsPerEpoch : Nat`, or a proof field
`slotsPerEpochPos : 0 < slotsPerEpoch`. -/
syntax tierField := (docComment)? ident " : " term
/-- One assignment in a tier value set: `slotsPerEpoch := 8`, or a proof-field
assignment `slotsPerEpochPos := by decide`. -/
syntax tierAssign := (docComment)? ident " := " term

-- `manyIndent` is what Lean's own `structFields` uses: it saves the block's
-- column so a field's `term` stops at the next line rather than swallowing the
-- following field name as a function argument. The whole `where` clause is
-- optional: a fork that adds no field of its own still writes `forkconfig`, to
-- materialize its own class out of the lineage's merged fields.
/-- `forkpreset where <fields>`: declare this fork's `Preset` class as a diff
over its ancestors', and (in a child) the scoped downgrade instance to the
parent's. -/
scoped syntax (name := forkpresetCmd)
  (docComment)? "forkpreset" (" where " manyIndent(ppLine tierField))? : command
/-- `forkconfig where <fields>`: the `Config` counterpart of `forkpreset`. -/
scoped syntax (name := forkconfigCmd)
  (docComment)? "forkconfig" (" where " manyIndent(ppLine tierField))? : command
/-- `forkpresetvalues minimal where <assignments>`: declare one injected value
set of this fork's `Preset`, as a diff over the ancestors' same-named set. -/
scoped syntax (name := forkpresetvaluesCmd)
  (docComment)? "forkpresetvalues " ident (" where " manyIndent(ppLine tierAssign))? : command
/-- `forkconfigvalues minimalConfig where <assignments>`: the `Config`
counterpart of `forkpresetvalues`. -/
scoped syntax (name := forkconfigvaluesCmd)
  (docComment)? "forkconfigvalues " ident (" where " manyIndent(ppLine tierAssign))? : command

/-! ## Emission -/

/-- The sub-namespace a child fork's downgrade instances land in, relative to the
fork. Naming it once keeps the emitter and the docs from drifting. -/
def downgradeNs : Name := `Downgrade

/-- The entries an optional `where <block>` carries: the clause parses as a null
node holding either nothing or the `where` atom plus the block. -/
def tierEntryBlock (clause : Syntax) : Array Syntax :=
  if clause.getArgs.isEmpty then #[] else clause[1].getArgs

/-- Rebuild one merged `tierField` as the `structSimpleBinder` a `class` takes,
carrying the author's docstring through so the merged class stays literate. -/
def tierFieldBinder (entry : Syntax) :
    CommandElabM (TSyntax ``Parser.Command.structSimpleBinder) := do
  let nameId : Ident := ⟨entry[1]⟩
  let type   : Term  := ⟨entry[3]⟩
  if entry[0].getArgs.isEmpty then
    `(Parser.Command.structSimpleBinder| $nameId:ident : $type)
  else
    `(Parser.Command.structSimpleBinder| $(⟨entry[0][0]⟩):docComment $nameId:ident : $type)

/-- Rebuild one merged `tierAssign` as a structure-instance field. -/
def tierAssignField (entry : Syntax) :
    CommandElabM (TSyntax ``Parser.Term.structInstField) :=
  `(Parser.Term.structInstField| $(⟨entry[1]⟩):ident := $(⟨entry[3]⟩):term)

/-- Record this fork's diff under `key`, then return the whole lineage's merged
block. Recording first is what makes the fork's own entries the last word. -/
def captureTier (key : Name) (entries : Array Syntax) : CommandElabM (Name × Array Syntax) := do
  let forkNs := (← getScope).currNamespace
  modifyEnv (recordCapture · { forkNs, name := key, kind := .tier, val := mkNullNode entries })
  return (forkNs, mergedTier (← getEnv) forkNs key)

/-- Emit the downgrade instance bridging this fork's `key` class to its parent's,
one projection per parent field. Does nothing at a root fork, which has no parent
class to bridge to. -/
def emitDowngrade (forkNs key : Name) : CommandElabM Unit := do
  let some parent := parentOf (← getEnv) forkNs | return
  let classId := mkIdent key
  -- The bridge is named after the fork it reaches, `toFuluPreset` / `toFuluConfig`,
  -- so a reader at an `open scoped` site sees which boundary it opens.
  let instId := mkIdent (Name.mkSimple s!"to{parent.getString!}{key.getString!}")
  let projections ← (mergedTier (← getEnv) parent key).mapM fun entry => do
    let field := entry[1].getId
    -- One dotted ident (`Preset.height`), not `.`-notation on the term `Preset`,
    -- which would try to project a field out of a type.
    `(Parser.Term.structInstField| $(mkIdent field):ident := $(mkIdent (key ++ field)):ident)
  -- `scoped` alone would not contain this: every body file of the fork sits
  -- *inside* the fork's namespace, where a scoped instance is already active. The
  -- extra `Downgrade` namespace is what makes the two boundary files spell
  -- `open scoped Downgrade` to reach the bridge, and leaves it unreachable
  -- elsewhere. The body files still resolve `Preset` and its projections here,
  -- since the fork's namespace encloses this one.
  elabCommand (← `(namespace $(mkIdent downgradeNs)))
  elabCommand (← `(@[reducible] scoped instance $instId:ident [$classId] :
    $(mkIdent (parent ++ key)) := { $[$projections:structInstField],* }))
  elabCommand (← `(end $(mkIdent downgradeNs)))

/-- The author's leading docstring as `declModifiers`, optionally with
`@[reducible]`. A tier form's docstring belongs on the declaration it emits, so
it is threaded through rather than dropped. -/
def tierMods (doc : Syntax) (reducible : Bool) :
    CommandElabM (TSyntax ``Parser.Command.declModifiers) :=
  match doc.getArgs.isEmpty, reducible with
  | true,  false => `(declModifiers|)
  | false, false => `(declModifiers| $(⟨doc[0]⟩):docComment)
  | true,  true  => `(declModifiers| @[reducible])
  | false, true  => `(declModifiers| $(⟨doc[0]⟩):docComment @[reducible])

/-- Emit a tier class: the merged field block as a `class`, plus the downgrade
instance in a child. Shared by `forkpreset` and `forkconfig`. -/
def elabTierClass (key : Name) : CommandElab := fun stx => do
  let (forkNs, entries) ← captureTier key (tierEntryBlock stx[2])
  let mods ← tierMods stx[0] (reducible := false)
  let fields ← `(Parser.Command.structFields| $(← entries.mapM tierFieldBinder)*)
  elabCommand (← `($mods:declModifiers class $(mkIdent key) where $fields:structFields))
  emitDowngrade forkNs key

/-- Emit a tier value set: the merged assignments as an `@[reducible] def` of the
fork's own class. Reducible (not an instance) so `minimal` and `mainnet` coexist
and the runner picks one per vector. -/
def elabTierValues (key : Name) : CommandElab := fun stx => do
  let setId : Ident := ⟨stx[2]⟩
  let (_, entries) ← captureTier setId.getId (tierEntryBlock stx[3])
  let mods ← tierMods stx[0] (reducible := true)
  let assignments ← entries.mapM tierAssignField
  elabCommand (← `($mods:declModifiers def $setId:ident : $(mkIdent key) :=
    { $[$assignments:structInstField],* }))

@[command_elab forkpresetCmd]       def elabForkpreset       := elabTierClass  `Preset
@[command_elab forkconfigCmd]       def elabForkconfig       := elabTierClass  `Config
@[command_elab forkpresetvaluesCmd] def elabForkpresetvalues := elabTierValues `Preset
@[command_elab forkconfigvaluesCmd] def elabForkconfigvalues := elabTierValues `Config

end EthCLLib.Spec
