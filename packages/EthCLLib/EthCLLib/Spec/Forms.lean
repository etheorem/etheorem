import SizzLean
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.Spec.Forms`: the capturing declaration forms

The author-facing commands that drive fork inheritance: `fork`, `forkdef`,
`forkcontainer`, `forkstruct`, and `inherit`. Each producer (`forkdef` /
`forkcontainer` / `forkstruct`) emits its real declaration *and* records the
author's raw body in `captureExt` (`EthCLLib.Internal.Capture`); `inherit`
replays a captured ancestor body in the current namespace, where its
unqualified sibling references late-bind to the child's overrides.

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

/-! ## `forkdef`: steps and helpers -/

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
  let forkNs := (← getScope).currNamespace
  let name := stx[2][0].getId
  modifyEnv (recordCapture · { forkNs, name, kind := .def_, sig := sig.raw, val := val.raw })
  elabCommand (← `($mods:declModifiers def $declId:declId $sig:optDeclSig $val:declVal))

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

@[command_elab forkcontainerCmd]
def elabForkcontainer : CommandElab := fun stx => do
  let mods   : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let nameId : Ident := ⟨stx[2]⟩
  let fields : TSyntax ``Parser.Command.structFields := ⟨stx[4]⟩
  let forkNs := (← getScope).currNamespace
  let cap : CapturedDecl :=
    { forkNs := forkNs, name := nameId.getId, kind := .container,
      sig := .missing, val := fields.raw }
  modifyEnv (fun env => recordCapture env cap)
  emitContainer mods nameId fields

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
  let forkNs := (← getScope).currNamespace
  -- A struct otherwise leaves `sig` `.missing`; stash the binders there (as a null
  -- node) so `inherit` can replay the same parameter list.
  let cap : CapturedDecl :=
    { forkNs := forkNs, name := nameId.getId, kind := .struct,
      sig := mkNullNode (binders.map (·.raw)), val := fields.raw }
  modifyEnv (fun env => recordCapture env cap)
  emitStruct mods nameId binders fields

/-! ## `inherit`: the single consumer -/

/-- `inherit Foo` replays the nearest ancestor fork's captured `Foo` in the
current namespace. The current fork did not declare `Foo`; the resolver walks
its lineage to find the body and re-elaborates it here, so `Foo`'s sibling
calls bind to this fork's overrides. -/
scoped syntax (name := inheritCmd) "inherit " ident : command

@[command_elab inheritCmd]
def elabInherit : CommandElab := fun stx => do
  let forkNs := (← getScope).currNamespace
  let name := stx[1].getId
  let env ← getEnv
  let some cap := resolveInherited env forkNs name
    | throwError "inherit: no ancestor of fork '{forkNs}' declares '{name}'; \
        a `fork … from …` edge and a captured `{name}` must both be in scope"
  -- Re-emit in the current namespace. `mkIdent name` is the bare short name, so
  -- the replayed declaration lands in `fork` and its body's sibling references
  -- resolve against `fork`'s scope.
  let declId : TSyntax ``Parser.Command.declId := ⟨mkNode ``Parser.Command.declId
    #[mkIdent name, mkNullNode]⟩
  match cap.kind with
  | .def_ =>
    let sig : TSyntax ``Parser.Command.optDeclSig := ⟨cap.sig⟩
    let val : TSyntax ``Parser.Command.declVal    := ⟨cap.val⟩
    elabCommand (← `(def $declId:declId $sig:optDeclSig $val:declVal))
  | .container =>
    emitContainer (← emptyMods) (mkIdent name) ⟨cap.val⟩
  | .struct =>
    let binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := cap.sig.getArgs.map (⟨·⟩)
    emitStruct (← emptyMods) (mkIdent name) binders ⟨cap.val⟩

end EthCLLib.Spec
