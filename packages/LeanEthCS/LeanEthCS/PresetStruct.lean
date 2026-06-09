import Lean
import LeanEthCS.Preset
import SizzLean.Repr.Class

/-!
# `LeanEthCS.PresetStruct`: preset-aware structure macro

Lean 4 elaboration macro that takes a single SSZ-container template
and emits one concrete `structure … deriving SSZRepr` per preset listed
in `for [...]`. Each emitted structure is an ordinary Lean structure
with literal `Nat`s baked into its field types, the existing
`SSZRepr` deriving handler in `SizzLean.Repr.Deriving` fires on it
unchanged.

## Why

Several consensus-spec containers (`BeaconState`, `HistoricalBatch`,
`SyncCommittee`, `ExecutionPayload`, …) embed preset-sensitive `Nat`
constants directly in their `Vector` / `SSZList` / `Bitvector` field
types. Writing each container twice (once per preset) would violate
DRY across ~7 types × 5 forks. This macro lets us write each
container once with `@@CONST` placeholders and have the macro stamp
out the minimal + mainnet variants automatically.

## Usage

```lean
ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Phase0
    for [minimal, mainnet] where
  genesisTime  : UInt64
  blockRoots   : Vector Root @@SLOTS_PER_HISTORICAL_ROOT
  eth1DataVotes : SSZList Eth1Data
                    (@@EPOCHS_PER_ETH1_VOTING_PERIOD * @@SLOTS_PER_EPOCH)
```

Expands to two `structure`s `BeaconState.Minimal` /
`BeaconState.Mainnet` inside `LeanEthCS.Forks.Phase0`, each with literal
`Nat`s substituted in.

## Design notes

* The `@@FOO` syntax is declared as a `term`-level extension. It only
  has meaning inside `ssz_struct_for_presets`; outside, elaboration
  fails (the macro intercepts and substitutes before elaboration).
* The macro substitutes *literal* `Nat`s into the emitted structures,
  it doesn't rely on the deriving handler to reduce
  `Preset.minimal.FOO` projections at structure-elaboration time.
  This keeps the emitted structures byte-identical to what a human
  would type, sidestepping reducibility concerns.
* Preset name → variant suffix: `minimal` → `.Minimal`, `mainnet` →
  `.Mainnet`. First letter capitalized; rest passed through.
-/

set_option autoImplicit false

namespace LeanEthCS.Macros

open SizzLean


open Lean Elab Command Meta

/-- Placeholder for a preset-sensitive numeric constant inside an SSZ
field type. The macro `ssz_struct_for_presets` recognizes this syntax
and replaces `@@FOO` with the literal value of `Preset.<preset>.FOO`.

Declared at `max` precedence so it parses as a function-application
argument (e.g. `Vector UInt8 @@SLOTS_PER_HISTORICAL_ROOT`). -/
syntax:max (name := presetPlaceholder) "@@" ident : term

/-- Placeholder for a preset-variant *type* reference inside an SSZ
field type. The macro `ssz_struct_for_presets` recognizes this syntax
and replaces `@%X` with `X.Minimal` (or `.Mainnet`, …) depending on
which preset's structure it's currently emitting.

Used for fields whose type is itself a preset-variant container, e.g.

```lean
ssz_struct_for_presets ContributionAndProof in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  contribution : @%SyncCommitteeContribution
```

The `ident` may be a dotted-path identifier
(`@%LeanEthCS.Forks.Altair.SyncCommitteeContribution`). The macro
appends the capitalized preset suffix verbatim to the supplied path. -/
syntax:max (name := presetVariantPlaceholder) "@%" ident : term

/-- Resolve `Preset.<preset>.<field>` to a literal `Nat`. Strategy:
elaborate the equivalent Lean source string and run `evalNat` on the
elaborated expression after reducing through projections. `evalNat`
alone won't see through a structure-field projection (`Preset.X.FOO`)
without help, so we run `Lean.Meta.unfoldDefinition?` / `whnf` first. -/
private def evalPresetField (presetName : Name) (field : Name) :
    TermElabM Nat := do
  let presetConst := mkConst (`LeanEthCS.Preset ++ presetName)
  let projConst   := mkConst (`LeanEthCS.Preset ++ field)
  let app := mkApp projConst presetConst
  -- Reduce: unfold the projection through the explicit `Preset.minimal`
  -- constructor (a single `def`), then through the projection redex.
  let reduced ← Lean.Meta.reduce app (skipProofs := true) (skipTypes := false)
  match ← (Lean.Meta.evalNat reduced).run with
  | some n => return n
  | none   =>
      throwError s!"`@@{field}`: cannot evaluate \
         `LeanEthCS.Preset.{field}` on \
         `LeanEthCS.Preset.{presetName}` to a `Nat` literal \
         (reduced to: {reduced})"

/-- Walk `stx` (a `Syntax` tree representing a Lean term), replacing:

* every `@@FOO` placeholder with a numeric literal carrying the value
  of `Preset.<presetName>.FOO`;
* every `@%T` placeholder with the identifier `T.<Variant>` where
  `Variant` is the capitalized preset name. -/
private partial def substitutePresetPlaceholders (presetName : Name)
    (stx : Syntax) : TermElabM Syntax := do
  -- Recognize the `@@FOO` (numeric) placeholder.
  if let some field ← matchNumPlaceholder? stx then
    let n ← evalPresetField presetName field
    return Syntax.mkNumLit (toString n)
  -- Recognize the `@%T` (type-variant) placeholder.
  if let some typeBase ← matchVariantPlaceholder? stx then
    let variantSuffix := Name.mkSimple (capitalizeFirstStr presetName.toString)
    return mkIdentFrom stx (typeBase ++ variantSuffix)
  -- Otherwise, recurse into compound `Syntax.node`s.
  match stx with
  | Syntax.node info kind args =>
      let args' ← args.mapM (substitutePresetPlaceholders presetName)
      return Syntax.node info kind args'
  | _ => return stx
where
  /-- Match `@@ident` and return the inner identifier name. -/
  matchNumPlaceholder? (s : Syntax) : TermElabM (Option Name) := do
    match s with
    | `(@@$idStx:ident) => return some idStx.getId
    | _ => return none
  /-- Match `@%ident` and return the inner identifier name. -/
  matchVariantPlaceholder? (s : Syntax) : TermElabM (Option Name) := do
    match s with
    | `(@%$idStx:ident) => return some idStx.getId
    | _ => return none
  /-- Inline copy of `capitalizeFirst`. (Calling the outer `private def`
  from inside the `where` clause loops the elaborator on certain Lean
  versions.) -/
  capitalizeFirstStr (s : String) : String :=
    if s.isEmpty then s
    else String.singleton s.front.toUpper ++ s.drop 1

/-- Capitalize the first letter of `s`. Used to derive the variant
suffix from a preset name (`minimal` → `Minimal`). -/
private def capitalizeFirst (s : String) : String :=
  if s.isEmpty then s
  else String.singleton s.front.toUpper ++ s.drop 1

/-- One field declaration in `ssz_struct_for_presets`. Same shape as a
plain `structure` field; the type slot may contain `@@FOO` (numeric)
or `@%X` (preset-variant-type) placeholders. -/
declare_syntax_cat sszPresetField
syntax (name := sszPresetField_def) ident " : " term : sszPresetField

/-- One container template, materialized per preset.

```
ssz_struct_for_presets <Name> in <Namespace> for [<preset>, …] where
  <field> : <type>,
  <field> : <type>,
  …
```

Fields are *comma-separated*. Lean's default term parser is greedy
across newlines, so an explicit separator is required to bound each
field's type. The trailing comma is optional. -/
syntax (name := sszStructForPresets)
  "ssz_struct_for_presets " ident " in " ident
  " for " "[" ident,+ "] " "where"
  (ppLine sszPresetField),+ : command

@[command_elab sszStructForPresets]
private def elabSSZStructForPresets : CommandElab := fun stx => do
  match stx with
  | `(ssz_struct_for_presets $nameStx:ident in $nsStx:ident
        for [ $[$presets:ident],* ] where
        $[$fields:sszPresetField],*) => do
      let baseName : Name := nameStx.getId
      let nsName : Name := nsStx.getId
      for presetSyn in presets do
        let presetName : Name := presetSyn.getId
        let variantSuffix : Name :=
          Name.mkSimple (capitalizeFirst presetName.toString)
        -- Fully-qualified emitted name: `<ns>.<base>.<Variant>`. Use a
        -- `_root_`-anchored identifier so the structure lands at the
        -- correct absolute path regardless of the surrounding namespace
        -- the macro is invoked inside.
        let structIdent : Ident :=
          mkIdent (`_root_ ++ nsName ++ baseName ++ variantSuffix)
        -- For each field, substitute placeholders in its type and
        -- construct a `structSimpleBinder` for the structure body.
        let fieldBinders : Array (TSyntax `Lean.Parser.Command.structSimpleBinder)
          ← liftTermElabM do
            fields.mapM fun fieldSyn => do
              let `(sszPresetField| $fname:ident : $ftype:term) := fieldSyn
                | throwError s!"ill-formed sszPresetField: {fieldSyn}"
              let ftypeStx' ← substitutePresetPlaceholders presetName ftype.raw
              let ftype' : Term := ⟨ftypeStx'⟩
              `(Lean.Parser.Command.structSimpleBinder|
                  $fname:ident : $ftype':term)
        -- Emit the structure (no inline `deriving`, that confuses the
        -- quotation parser when combined with the spliced binder
        -- array) and the deriving as a separate `deriving instance`
        -- command.
        elabCommand (← `(
          structure $structIdent where
            $[$fieldBinders]*))
        elabCommand (← `(
          deriving instance SizzLean.SSZRepr for $structIdent))
  | _ => throwUnsupportedSyntax

end LeanEthCS.Macros
