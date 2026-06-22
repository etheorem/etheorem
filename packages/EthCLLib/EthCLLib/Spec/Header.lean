import EthCLLib.Spec.State
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLLib.Spec.Header`: the section-header macros

A fork's state-transition surface is set up by two macros, split along the seam
that **declarations persist across modules but `variable`s do not**:

* `state_preamble BeaconState` runs **once per fork**, in the `State` module, right
  after the `BeaconState` container. It emits the declarations that must exist
  exactly once and survive into the `.olean`:

  ```lean
  abbrev State [Preset] [HasherTag] : Type := SSZ.Box HasherTag.H BeaconState
  @[inline] def modifyState [Preset] [HasherTag] {m : Type → Type}
      [MonadStateOf State m] (f : State → State) : m PUnit := modifyThe State f
  ```

  `State` is the boxed `BeaconState`; `modifyState` is its multi-field updater. The
  updater is declared here with the **concrete** `State → State` domain (rather than a
  generic framework function) so the expected type flows into a step's lambda binder,
  and the author writes `modifyState fun state => …` with no `(state : State)`
  annotation. Because `State` is per-fork, the framework cannot own one generic
  `modifyState`; this is the same generation pattern `forkcontainer` uses, a
  framework-owned macro emitting a fork's plumbing.

* `state_section` runs **once per section** (per operation file). It opens an
  anonymous `section` and emits the `variable` line that re-establishes the
  section-scoped instances and monad (these do not persist across files):

  ```lean
  variable [Preset] [HasherTag]
  variable [Config] [CryptoBackend]
  variable {StateTransition : Type → Type}
  variable [Monad StateTransition]
  variable [MonadStateOf State StateTransition]
  variable [MonadExceptOf StateTransitionError StateTransition]
  ```

  The author writes `state_section` (which opens the section) and closes it with the
  matching `end`. It takes no argument: it references the `State` the preamble already
  declared. `[Config]` and `[CryptoBackend]` are instance-implicit, so they attach only
  to the declarations that use them; a pure-accessor step carries neither.

`state_preamble` is the single declarer of `State` / `modifyState`, and the `State`
module is imported by every operation file, so there is no redeclaration and no guard.
`Preset` resolves to the fork's own preset class (the tier system is per fork,
`SPECS_ARCHITECTURE.md` §9.1); `State`, `StateTransition`, `StateTransitionError`,
`HasherTag` are named with use-site identifiers (`mkIdent`) so they resolve where the
macro expands, not where it is defined.
-/

set_option autoImplicit false

open Lean Elab Command

namespace EthCLLib.Spec

/-! ## `state_preamble`: the once-per-fork declarations -/

/-- `state_preamble BeaconState`: declare the fork's boxed `State` and its
concrete-domain `modifyState`. Written once, in the `State` module. -/
scoped syntax (name := statePreambleStx) "state_preamble " ident : command

@[command_elab statePreambleStx]
def elabStatePreamble : CommandElab := fun stx => do
  let stateTy : TSyntax `term := ⟨stx[1]⟩
  -- Use-site identifiers: resolve where the macro expands (the fork namespace).
  let stateId      := mkIdent `State
  let modifyId     := mkIdent `modifyState
  let presetId     := mkIdent `Preset
  let hasherTagId  := mkIdent ``HasherTag
  let hasherHId    := mkIdent (``HasherTag ++ `H)
  elabCommand (← `(abbrev $stateId [$presetId] [$hasherTagId] : Type :=
    SizzLean.Cache.SSZ.Box $hasherHId $stateTy))
  -- The concrete-domain `modifyState`: `State → State` so the binder type flows in
  -- and step bodies need no `(state : State)` annotation. `m` stays generic over the
  -- effect monad.
  elabCommand (← `(@[inline] def $modifyId [$presetId] [$hasherTagId] {m : Type → Type}
    [MonadStateOf $stateId m] (f : $stateId → $stateId) : m PUnit := modifyThe $stateId f))

/-! ## `state_section`: open a state-transition section -/

/-- `state_section`: open an anonymous `section` and emit the state-transition
`variable` line (re-established per file). Close with the matching `end`. -/
scoped syntax (name := stateSectionStx) "state_section" : command

@[command_elab stateSectionStx]
def elabStateSection : CommandElab := fun _ => do
  let stateId      := mkIdent `State
  let presetId     := mkIdent `Preset
  let hasherTagId  := mkIdent ``HasherTag
  let configId     := mkIdent `Config
  let cryptoId     := mkIdent `CryptoBackend
  let stId         := mkIdent `StateTransition
  let errId        := mkIdent ``StateTransitionError
  elabCommand (← `(section))
  elabCommand (← `(variable [$presetId] [$hasherTagId]))
  -- The `[Config]` constants tier and the `[CryptoBackend]` seam are in scope in every
  -- state section. Both are instance-implicit, so they attach only to the declarations
  -- that use them; a pure-accessor step carries neither.
  elabCommand (← `(variable [$configId] [$cryptoId]))
  elabCommand (← `(variable {$stId : Type → Type}))
  elabCommand (← `(variable [Monad $stId]))
  elabCommand (← `(variable [MonadStateOf $stateId $stId]))
  elabCommand (← `(variable [MonadExceptOf $errId $stId]))

/-! ## `fork_choice_section`: open a fork-choice section

The companion of `state_section` for the second state machine. The fork-choice map
cannot hide the way the hasher and box flavour do, since `map` appears in the `Store`
type itself, so the macro emits `{map : MapKind} [FcMap map]` explicitly and `Store map`
(`Store hashMap` and `Store treeMap` are distinct types). The store machine carries its
own three raw constraints over `StoreTransitionError`. Like `state_section`, it opens
the `section`; close with the matching `end`. -/
scoped syntax (name := forkChoiceSectionStx) "fork_choice_section " ident : command

@[command_elab forkChoiceSectionStx]
def elabForkChoiceSection : CommandElab := fun stx => do
  -- Use the author's own `map` ident for both the binder and the uses, so the section
  -- variable and the handlers' `Store map` / `FcMap map` resolve to the same variable.
  let mapIdent   : Ident := ⟨stx[1]⟩
  let storeId    := mkIdent `Store
  let mapKindId  := mkIdent ``MapKind
  let fcMapId    := mkIdent ``FcMap
  let presetId   := mkIdent `Preset
  let hasherTagId := mkIdent ``HasherTag
  let configId   := mkIdent `Config
  let cryptoId   := mkIdent `CryptoBackend
  let stId       := mkIdent `StoreTransition
  let errId      := mkIdent ``StoreTransitionError
  elabCommand (← `(section))
  -- `[Preset] [HasherTag]` first: `Store map` (preset- and hasher-parameterized) needs
  -- them before the `MonadStateOf (Store map)` line below. `[Config]` and `[CryptoBackend]`
  -- are in scope too (instance-implicit, attached only where used), as on the state side.
  elabCommand (← `(variable [$presetId] [$hasherTagId]))
  elabCommand (← `(variable [$configId] [$cryptoId]))
  elabCommand (← `(variable {$mapIdent : $mapKindId}))
  elabCommand (← `(variable [$fcMapId $mapIdent]))
  elabCommand (← `(variable {$stId : Type → Type}))
  elabCommand (← `(variable [Monad $stId]))
  elabCommand (← `(variable [MonadStateOf ($storeId $mapIdent) $stId]))
  elabCommand (← `(variable [MonadExceptOf $errId $stId]))

/-! ## `appendState`: append to a list field of the threaded state -/

/-- `appendState f v`: append `v` to the threaded state's list field `f`, the monadic
state-threading wrapper over SizzLean's `sszAppend`. Expands to
`modifyState fun state => sszAppend state f v`, so the per-fork `modifyState` (a use-site
identifier, resolved to the running fork's) threads the box and `sszAppend` does the
cap-clamping push. The append value `v` is evaluated under the `state` binder, so a `v` that
reads `state` keeps the explicit `modifyState fun state => sszAppend state f …` form instead. -/
scoped syntax (name := appendStateStx) "appendState " ident ppSpace term : term

macro_rules
  | `(appendState $head:ident $v) => do
      -- Expand straight to `sszModify`'s `as` form rather than `sszAppend`'s surface: a
      -- bare `$v` after `sszAppend state $head` would be misread as a path segment, whereas
      -- the `as` keyword stops the segment parse cleanly. (Both are the cap-clamping push.)
      let modifyId := mkIdent `modifyState
      `($modifyId fun state => sszModify state $head:ident as l => l.push $v)

end EthCLLib.Spec
