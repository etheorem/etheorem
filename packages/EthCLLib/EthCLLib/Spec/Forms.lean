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

The abbrev-ness is load-bearing, not cosmetic: `@[reducible]` is what lets
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

@[command_elab forkcontainerCmd]
def elabForkcontainer : CommandElab := fun stx => do
  let mods   : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let nameId : Ident := ⟨stx[2]⟩
  let fields : TSyntax ``Parser.Command.structFields := ⟨stx[4]⟩
  let (forkNs, name) ← keyFor nameId.getId
  modifyEnv (recordCapture · { forkNs, name, kind := .container, val := fields.raw })
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
    emitContainer (← emptyMods) nameId ⟨cap.val⟩
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
