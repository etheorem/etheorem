import SizzLean
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.Spec.Forms`: the capturing declaration forms

The author-facing commands that drive fork inheritance: `fork`, `forkdef`,
`forkabbrev`, `forkinstance`, `forkcontainer`, `forkstruct`, and `inherit`. Each
producer emits its real declaration *and* records the author's raw body in
`captureExt` (`EthCLLib.Internal.Capture`); `inherit` replays a captured ancestor
body in the current namespace, where its unqualified sibling references
late-bind to the child's overrides.

Every producer keys its capture through `captureKey`, which splits the
elaboration-time namespace at the nearest enclosing fork. So a form written
inside a nested `namespace Const` files under the fork with a dotted name, and
`inherit Const.foo` in the child finds it.

The forms are `scoped`, so `open EthCLLib.Spec` activates them along with the
rest of the author surface and a spec file opens exactly one namespace.

## Why re-emit by quotation rather than copy a constant

A symbol-level copy or alias early-binds: an inherited caller keeps calling the
parent's callee even after the child overrides it (the open-recursion trap).
Re-elaborating the *captured syntax* in the child namespace makes the body's
sibling names resolve at the child site, so late binding falls out for free.
The captured `Syntax` is the author's own tokens, un-stamped, so no blanket
hygiene override is needed (`FRAMEWORK_ARCHITECTURE.md` §3.1).
-/

set_option autoImplicit false

open Lean Elab Command
open EthCLLib.Internal

namespace EthCLLib.Spec

/-! ## `fork … from …`: the lineage declaration -/

/-- `fork Name` declares a base fork; `fork Name from Parent` records that the
current fork inherits from `Parent`. Written in the fork's root module, inside
`namespace EthCLSpecs.<Name>`. The fork's identity is its current namespace;
the parent is resolved as the sibling namespace `<prefix>.<Parent>`. -/
-- `fork` is a reserved command keyword. SSZ conformance is by field *order*, not
-- field name (the wire format and root never see Lean names), so a container
-- whose spec field is `fork` (e.g. `BeaconState.fork`) is named `forkData` in
-- Lean to avoid the keyword. This is the behavioral-conformance freedom at work.
scoped syntax (name := forkCmd) "fork " ident (" from " ident)? : command

@[command_elab forkCmd]
def elabFork : CommandElab := fun stx => do
  let forkNs := (← getScope).currNamespace
  -- `(" from " ident)?` elaborates to a null node: empty when absent, the
  -- `from` atom plus the parent ident when present.
  let fromArgs := stx[2].getArgs
  let parent? : Option Name :=
    if fromArgs.size == 2 then some (forkNs.getPrefix ++ fromArgs[1]!.getId) else none
  modifyEnv (recordLineage · forkNs parent?)

/-! ## Capture keying

Every producer files its entry under the *fork* it was written in, with the path
from that fork down to the declaration as the name. `keyFor` does the split; the
producers below differ only in which syntax slots they fill. -/

/-- The `(forkNs, name)` capture key for `declName` at the current namespace. -/
def keyFor (declName : Name) : CommandElabM (Name × Name) := do
  return captureKey (← getEnv) (← getScope).currNamespace declName

/-! ## `forkdef` / `forkabbrev`: steps, helpers, aliases, constants -/

/-- `forkdef name … := …`, shaped exactly like `def`. Emits the `def` and
captures its signature and value for per-fork replay. The only thing it adds
over a plain `def` is the capture that powers inheritance. -/
scoped syntax (name := forkdefCmd)
  declModifiers "forkdef " declId optDeclSig declVal : command

@[command_elab forkdefCmd]
def elabForkdef : CommandElab := fun stx => do
  let mods   : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let declId : TSyntax ``Parser.Command.declId        := ⟨stx[2]⟩
  let sig    : TSyntax ``Parser.Command.optDeclSig     := ⟨stx[3]⟩
  let val    : TSyntax ``Parser.Command.declVal        := ⟨stx[4]⟩
  let (forkNs, name) ← keyFor stx[2][0].getId
  modifyEnv (recordCapture · { forkNs, name, kind := .def_, sig := sig.raw, val := val.raw })
  elabCommand (← `($mods:declModifiers def $declId:declId $sig:optDeclSig $val:declVal))

/-- `forkabbrev name … := …`, shaped exactly like `abbrev`. Used for the fork's
type aliases (`Slot`, `Gwei`, `Root`, …) and for every `Const` entry.

The abbrev-ness does real work here: `@[reducible]` is what lets
SSZRepr instance synthesis see through `Root` to `Vector UInt8 32`, and what lets
a symbolic list cap `Const.validatorRegistryLimit` reduce to a literal once a
concrete `Preset` is injected. Replay re-emits an `abbrev` for the same reason. -/
scoped syntax (name := forkabbrevCmd)
  declModifiers "forkabbrev " declId optDeclSig declVal : command

@[command_elab forkabbrevCmd]
def elabForkabbrev : CommandElab := fun stx => do
  let mods   : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let declId : TSyntax ``Parser.Command.declId        := ⟨stx[2]⟩
  let sig    : TSyntax ``Parser.Command.optDeclSig     := ⟨stx[3]⟩
  let val    : TSyntax ``Parser.Command.declVal        := ⟨stx[4]⟩
  let (forkNs, name) ← keyFor stx[2][0].getId
  modifyEnv (recordCapture · { forkNs, name, kind := .abbrev_, sig := sig.raw, val := val.raw })
  elabCommand (← `($mods:declModifiers abbrev $declId:declId $sig:optDeclSig $val:declVal))

/-! ## `forkinstance`: typeclass registrations that mention fork names -/

/-- `forkinstance name <binders> : Class arg := …`, shaped like `instance`.

The name is mandatory, unlike Lean's `instance`, because the capture key *is* a
name: `inherit` has nothing else to spell. `forkdef` cannot stand in here, since
the capturing forms drop `declModifiers` on replay and an `@[instance]`
attribute would be lost with them.

The users are registrations whose subject is a fork-owned name, e.g. a
`ValidModulus` on `Const.slotsPerEpoch`: each fork needs its own copy, bound to
its own `Preset`. An instance that mentions no spec name belongs in `EthCLLib`
instead, where no fork owns it. -/
-- `declSig` is `bracketedBinder* >> ": " term`, so the author's `[Preset]` and
-- friends ride inside `sig` with no separate binder slot, exactly as they do for
-- Lean's own `instance`.
scoped syntax (name := forkinstanceCmd)
  declModifiers "forkinstance " declId Parser.Command.declSig declVal : command

/-- Emit a named `instance`. Shared by `forkinstance` and `inherit`'s instance
arm, so a replayed instance regenerates identically. -/
def emitInstance (declId : TSyntax ``Parser.Command.declId)
    (sig : TSyntax ``Parser.Command.declSig) (val : TSyntax ``Parser.Command.declVal) :
    CommandElabM Unit := do
  elabCommand (← `(instance $declId:declId $sig:declSig $val:declVal))

@[command_elab forkinstanceCmd]
def elabForkinstance : CommandElab := fun stx => do
  let declId : TSyntax ``Parser.Command.declId   := ⟨stx[2]⟩
  let sig    : TSyntax ``Parser.Command.declSig  := ⟨stx[3]⟩
  let val    : TSyntax ``Parser.Command.declVal  := ⟨stx[4]⟩
  let (forkNs, name) ← keyFor stx[2][0].getId
  modifyEnv (recordCapture · { forkNs, name, kind := .instance_, sig := sig.raw, val := val.raw })
  emitInstance declId sig val

/-! ## `forkcontainer` / `forkstruct`: SSZ and non-SSZ structures

Both capture a raw field block and regenerate a `structure`. `forkcontainer`
adds the SSZ derive (the container front-end); `forkstruct` runs ordinary
`deriving` only, for non-SSZ records like the fork-choice `Store`. Every
container is `[Preset]`-parameterized uniformly (`FRAMEWORK_ARCHITECTURE.md` §5);
a preset-free one carries the binder too, and its concrete-preset instances are
definitionally equal, so the uniformity costs nothing. -/

/-- An empty `declModifiers`, for the `inherit` arms (a replayed container needs
no docstring). -/
def emptyMods : CommandElabM (TSyntax ``Parser.Command.declModifiers) :=
  `(declModifiers|)

/-- Emit an SSZ container: a `[Preset]`-parameterized `structure` deriving
`Inhabited`, `DecidableEq`, `BEq`, `Ord`, `Hashable`, and SizzLean's `SSZRepr`
(serialize / deserialize / hash-tree-root). Shared by `forkcontainer` and the
container arm of `inherit`, so a replayed container regenerates identically.
`Ord` / `Hashable` derive universally now that SizzLean carries them for the
collection types (`SSZList` / `Bitvector` / `Bitlist`), so a map-key container
(`Checkpoint`, …) needs no hand-written `deriving instance` (`FRAMEWORK_ARCHITECTURE.md`
§5). -/
def emitContainer (mods : TSyntax ``Parser.Command.declModifiers) (nameId : Ident)
    (fields : TSyntax ``Parser.Command.structFields) : CommandElabM Unit := do
  let presetId := mkIdent `Preset
  elabCommand (← `($mods:declModifiers structure $nameId [$presetId] where
    $fields:structFields))
  -- Derive in a separate command so the class names resolve as ordinary globals
  -- (an inline `deriving … SizzLean.SSZRepr` in the quotation hygiene-stamps the
  -- name to `SizzLean.SSZRepr✝`).
  elabCommand (← `(deriving instance Inhabited, DecidableEq, BEq, Ord, Hashable, SizzLean.SSZRepr for $nameId))

/-- Emit a non-SSZ structure: a `[Preset]`-parameterized `structure` with no SSZ
derive, plus any extra `binders` the author wrote (e.g. the fork-choice `Store`'s
`(map : MapKind) [HasherTag]`). Used for the fork-choice `Store`, `FcNode`,
`LatestMessage`. -/
def emitStruct (mods : TSyntax ``Parser.Command.declModifiers) (nameId : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (fields : TSyntax ``Parser.Command.structFields) : CommandElabM Unit := do
  let presetId := mkIdent `Preset
  elabCommand (← `($mods:declModifiers structure $nameId [$presetId] $binders* where
    $fields:structFields))

/-- `forkcontainer Name where <fields>`: declare an SSZ container and capture its
field block for per-fork replay. `declModifiers` lets the author attach a `/-- …
-/` docstring, the literate-by-default discipline. -/
scoped syntax (name := forkcontainerCmd)
  declModifiers "forkcontainer " ident " where " Parser.Command.structFields : command

/-- Whether `stx` mentions the identifier `n`. Used to see
`@[sizzlean_progressive]` on a `forkcontainer`'s modifiers. -/
private def syntaxHasIdent (stx : Syntax) (n : Name) : Bool :=
  stx.find? (fun s => s.isIdent && s.getId == n) |>.isSome

/-- The positions of a `@[sizzlean_progressive_gaps …]` attribute on a
`forkcontainer`'s modifiers, or `#[]` when there is none. The attribute is its own
syntax kind (`SizzLean.Repr.Deriving.sizzlean_progressive_gaps`), and its `[1]` child
holds the `num+` repetition. -/
private def progressiveGapsOf (stx : Syntax) : Array Nat :=
  match stx.find? (·.getKind == ``SizzLean.Repr.Deriving.sizzlean_progressive_gaps) with
  | some attr => attr[1].getArgs.filterMap (·.isNatLit?)
  | none => #[]

/-! ## The lineage cross-check for progressive containers

A progressive redeclaration's holes must sit where the ancestor's field block
lost fields. Hand-written gap positions can drift from that, and nothing below
the derive handler could tell. The check here diffs the child's field block
against the nearest ancestor's captured block and enforces the result:

* marker written and matching the diff: silent, the mask is a checked fact;
* marker written and disagreeing: an error at the declaration;
* marker absent: the computed gaps drive the mask, and a warning names the
  marker the author should write.

A fork whose diff is not expressible as gaps (a replaced or an inserted field,
`Fulu`'s payload header becoming `Gloas`'s bid) is skipped: no mask exists to
check, and the declaration keeps today's behaviour.
-/

/-- The field names of a `structFields` block, in declaration order. The block
holds one repetition node whose children are the four field-binder kinds; each
binder puts the field's own `ident` ahead of its type's, so the first ident in
the binder is its name. The blocks this reads never carry field attributes,
which the first-ident rule relies on. -/
private def fieldNamesOf (fields : TSyntax ``Parser.Command.structFields) : Array Name :=
  fields.raw.getArgs.flatMap (·.getArgs) |>.filterMap fun binder =>
    let fieldKinds : List SyntaxNodeKind :=
      [``Lean.Parser.Command.structSimpleBinder, ``Lean.Parser.Command.structExplicitBinder,
        ``Lean.Parser.Command.structImplicitBinder, ``Lean.Parser.Command.structInstBinder]
    if fieldKinds.contains binder.getKind then
      (binder.find? fun s => s.isIdent).map (·.getId)
    else
      none

/-- Does `n` appear in `xs` at or after `start`? Container blocks run to tens of
fields, so the slice-and-scan is free. -/
private def appearsFrom (xs : Array Name) (n : Name) (start : Nat) : Bool :=
  (xs.toList.drop start).contains n

/-- The parent positions `child` leaves empty, under the fork rules an
EIP-7495 mask can express: delete anywhere, append at the end. `parent` is the
ancestor's field names, `child` the redeclaration's.

The scan walks both blocks with two cursors. Equal names consume one position
each. A differing child name records the current parent position as a gap, but
only when its own name appears later in the parent, the signature of a
deletion; a name that appears nowhere later is a replacement or an insertion,
which no mask expresses, and the scan bails. A child that runs out leaves the
parent's remaining positions as gaps. A parent that runs out leaves the child's
remaining names as appends. Names, not positions, are the diff unit; a rename
inside a lineage also bails, and that is honest, since a renamed field breaks
every inherited function that reads the old name. -/
private def diffFieldGaps (parent child : Array Name) : Option (Array Nat) := do
  let mut gaps : Array Nat := #[]
  let mut j : Nat := 0
  for i in [0:parent.size] do
    if j < child.size then
      if parent[i]! == child[j]! then
        j := j + 1
      else if appearsFrom parent child[j]! (i + 1) then
        gaps := gaps.push i
      else
        -- A replacement or an insertion: no mask expresses it.
        failure
    else
      -- The child ran out: the parent's remaining positions are all gaps.
      gaps := (List.range (parent.size - i)).foldl (init := gaps) fun g k => g.push (i + k)
  -- The parent ran out: the child's remaining names are appends.
  return gaps

/-- Carry the ancestor's mask across a redeclaration: the diff's positions are
indices into the ancestor's *active* field list, so each maps to its mask
position through the ancestor's own holes, and the ancestor's holes join the
child's list, since a marker always carries every hole. Both inputs are
ascending, and the sort merges them; the blocks run under the 256-bit mask
cap, so the sort is free. -/
private def accumulateGaps (parentGaps : Array Nat) (parentFieldCount : Nat)
    (deleted : Array Nat) : Array Nat :=
  let width := parentFieldCount + parentGaps.size
  let actives : List Nat := (List.range width).filter fun p => !parentGaps.contains p
  let mapped : Array Nat := deleted.filterMap fun i => actives[i]?
  (parentGaps ++ mapped).qsort (· < ·)

/-- The gap positions a `forkcontainer` redeclaration implies, diffed against
the nearest ancestor's captured block, paired with that ancestor's fork
namespace. `none` when no ancestor captured a container of the name (a base
fork's declaration, or a name the fork added), the ancestor entry is not a
container, or the diff hit a field the mask cannot express. A progressive
ancestor's holes accumulate: the child re-states every hole, its own deletions
mapped through the ancestor's mask. -/
def expectedGapsFromLineage (env : Environment) (forkNs name : Name)
    (childFields : Array Name) : Option (Name × Array Nat) :=
  match resolveInherited env forkNs name with
  | some cap =>
    if cap.kind == CaptureKind.container then
      match diffFieldGaps (fieldNamesOf ⟨cap.val⟩) childFields with
      | none => none
      | some deleted =>
        if cap.progressive then
          let parentFields := fieldNamesOf ⟨cap.val⟩
          some (cap.forkNs, accumulateGaps cap.progressiveGaps parentFields.size deleted)
        else
          some (cap.forkNs, deleted)
    else
      none
  | none => none

/-- Render the marker a declaration should carry for the given gaps, e.g.
`@[sizzlean_progressive, sizzlean_progressive_gaps 8 9 10 28]`; the all-active
spelling when there are none. -/
private def gapsMarkerString (gaps : Array Nat) : String :=
  if gaps.isEmpty then
    "@[sizzlean_progressive]"
  else
    let nums := gaps.foldl (init := "") fun acc g => s!"{acc} {g}"
    s!"@[sizzlean_progressive, sizzlean_progressive_gaps{nums}]"

@[command_elab forkcontainerCmd]
def elabForkcontainer : CommandElab := fun stx => do
  let mods   : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let nameId : Ident := ⟨stx[2]⟩
  let fields : TSyntax ``Parser.Command.structFields := ⟨stx[4]⟩
  let (forkNs, name) ← keyFor nameId.getId
  let progressive := syntaxHasIdent mods.raw `sizzlean_progressive
  let mut progressiveGaps := progressiveGapsOf mods.raw
  -- The lineage cross-check. A matching marker changes nothing; an absent
  -- marker adopts the computed gaps, emits them on the structure so the derive
  -- sees them, and asks to be written down; a disagreeing marker fails the
  -- declaration.
  let mut emitMods := mods
  if progressive then
    match expectedGapsFromLineage (← getEnv) forkNs name (fieldNamesOf fields) with
    | some (parentFork, expected) =>
      if progressiveGaps.isEmpty && !expected.isEmpty then
        logWarning m!"'{forkNs}.{name}' is progressive and writes no gap marker. \
          The lineage diff against '{parentFork}.{name}' computes gaps {toString expected}. \
          Write {gapsMarkerString expected} so the mask is checked against the ancestor's \
          field block."
        progressiveGaps := expected
        let nums : Array (TSyntax `num) := expected.map Syntax.mkNatLit
        emitMods ← `(declModifiers| @[sizzlean_progressive, sizzlean_progressive_gaps $nums*])
      else if progressiveGaps != expected then
        throwError m!"'{forkNs}.{name}' declares {gapsMarkerString progressiveGaps}, but the \
          lineage diff against '{parentFork}.{name}' computes gaps {toString expected}. \
          Fix the marker or restate the field block so the two agree."
    | none => pure ()
  modifyEnv (recordCapture ·
    { forkNs, name, kind := .container, val := fields.raw, progressive, progressiveGaps })
  emitContainer emitMods nameId fields

/-- `forkstruct Name <binders> where <fields>`: declare a non-SSZ structure and
capture it (with its extra binders) for per-fork replay. The binders let a struct
carry parameters beyond the auto `[Preset]`, e.g. the fork-choice `Store`'s
`(map : MapKind) [HasherTag]`. -/
scoped syntax (name := forkstructCmd)
  declModifiers "forkstruct " ident (ppSpace bracketedBinder)* " where " Parser.Command.structFields : command

@[command_elab forkstructCmd]
def elabForkstruct : CommandElab := fun stx => do
  let mods    : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let nameId  : Ident := ⟨stx[2]⟩
  let binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := stx[3].getArgs.map (⟨·⟩)
  let fields  : TSyntax ``Parser.Command.structFields := ⟨stx[5]⟩
  let (forkNs, name) ← keyFor nameId.getId
  let cap : CapturedDecl :=
    { forkNs, name, kind := .struct,
      binders := mkNullNode (binders.map (·.raw)), val := fields.raw }
  modifyEnv (recordCapture · cap)
  emitStruct mods nameId binders fields

/-! ## `inherit`: the single consumer -/

/-- `inherit Foo Bar …` replays the nearest ancestor fork's captured `Foo`, `Bar`,
… in the current namespace. The current fork did not declare them; the resolver
walks its lineage to find each body and re-elaborates it here, so a replayed
body's sibling calls bind to this fork's overrides.

A name may be dotted (`inherit Const.slotsPerEpoch`), matching the capture key a
form written inside a nested namespace files under. Several names on one line
group related entries (`inherit Const.domainRandao Const.domainDeposit`) while
staying explicit per name, the same discipline one-per-line has. -/
scoped syntax (name := inheritCmd) "inherit " ident+ : command

/-- Replay one captured declaration. `spelled` is the name as the author wrote
it at the `inherit` site, which is also where the replay lands: emitting the
author's own ident (rather than the capture's key) keeps the residual namespace
path from being applied twice when `inherit` itself sits inside a nested
namespace. -/
def replayOne (spelled : Name) : CommandElabM Unit := do
  let (forkNs, key) ← keyFor spelled
  let some cap := resolveInherited (← getEnv) forkNs key
    | throwError "inherit: no ancestor of fork '{forkNs}' declares '{key}'; \
        a `fork … from …` edge and a captured '{key}' must both be in scope"
  let nameId := mkIdent spelled
  -- Lean places `def Const.foo` written inside `namespace Gloas` at
  -- `Gloas.Const.foo` *and* elaborates its body as if inside `Gloas.Const`, so a
  -- dotted key gets the same late binding a bare one does.
  let declId : TSyntax ``Parser.Command.declId := ⟨mkNode ``Parser.Command.declId
    #[nameId, mkNullNode]⟩
  match cap.kind with
  | .def_ =>
    elabCommand (← `(def $declId:declId $(⟨cap.sig⟩):optDeclSig $(⟨cap.val⟩):declVal))
  | .abbrev_ =>
    elabCommand (← `(abbrev $declId:declId $(⟨cap.sig⟩):optDeclSig $(⟨cap.val⟩):declVal))
  | .instance_ =>
    emitInstance declId ⟨cap.sig⟩ ⟨cap.val⟩
  | .container =>
    let mods ←
      if cap.progressive && !cap.progressiveGaps.isEmpty then
        -- Each position becomes one `num` of the attribute's `num+` repetition.
        let gaps : Array (TSyntax `num) := cap.progressiveGaps.map Syntax.mkNatLit
        `(declModifiers| @[sizzlean_progressive, sizzlean_progressive_gaps $gaps*])
      else if cap.progressive then
        `(declModifiers| @[sizzlean_progressive])
      else
        emptyMods
    emitContainer mods nameId ⟨cap.val⟩
  | .struct =>
    emitStruct (← emptyMods) nameId (cap.binders.getArgs.map (⟨·⟩)) ⟨cap.val⟩
  | .tier =>
    throwError "inherit: '{key}' is a tier declaration ({`Preset} / {`Config} or one of \
      their value sets), which composes by lineage merge, not by replay. Declare this \
      fork's diff with the matching `forkpreset` / `forkconfig` / `forkpresetvalues` / \
      `forkconfigvalues` form instead; the ancestors' entries merge in automatically"

@[command_elab inheritCmd]
def elabInherit : CommandElab := fun stx =>
  stx[1].getArgs.forM fun nameStx => replayOne nameStx.getId

end EthCLLib.Spec
