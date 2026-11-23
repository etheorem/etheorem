import EthCLLib

/-!
# `EthCLLib.Tests.CLInheritChecked`: a checked body through the inherit/replay path

A `forkdef` whose body does checked arithmetic must
survive the fork DSL's replay, which re-elaborates the author's raw body
syntax in the child namespace (`EthCLLib.Internal.Capture`, §4.3 "including
… inherited declarations"). The base fork's `scaledSlot` reads the state's
`slot`, multiplies by its sibling `factor`, and binds the checked product under
`←` in the machine monad, so the replay exercises the scoped operator
elaborator a second time in the child's scope.

`ChildChecked` overrides `factor` (2 → 3) and inherits `scaledSlot`. If replay
re-elaborated the body here, the child's `scaledSlot` reads the child's
`factor`: slot 4 gives 12, and the base's own body still gives 8. An
early-binding replay would answer 12's wrong twin, 8, in the child: a
term-level copy answers 8, and an alias would not even elaborate across the
two distinct `State` structure types; a replay that dropped the checked bind
would not compile, because
`cur * factor` under a monadic expected type needs the elaborator and the
§4.4 lift to elaborate at all.

Both forks mirror the real section preamble: a `forkcontainer`, a
`state_preamble` (which declares this fork's `State` and `modifyState`), and a
`state_section` around the `forkdef`s, the way a fork body's operation file is
laid out.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.CLInheritChecked

/-! ## The base fork -/

namespace BaseChecked

fork BaseChecked

/-- The base fork's preset stand-in. -/
class Preset where
  dummy : Nat := 0

/-- The base fork's config stand-in. -/
class Config where
  dummy : Nat := 0

@[reducible] def mini : Preset := {}

/-- A one-field toy state container. -/
forkcontainer Toy where
  slot : CLUint64

state_preamble Toy

state_section

/-- The sibling the child overrides: the base factor. -/
forkdef factor : CLUint64 := 2

/-- The checked body under test: read `slot`, multiply by `factor`, bind the
checked product under `←` immediately (§4.3). -/
forkdef scaledSlot : StateTransition CLUint64 := do
  let s ← get
  let cur := sszGet s slot
  let product ← cur * factor
  pure product

end   -- closes the section opened by `state_section`

end BaseChecked

/-! ## The child fork -/

namespace ChildChecked

fork ChildChecked from BaseChecked

/-- The child's own preset stand-in, unrelated to the base's by construction,
as `ForkScoping` records. -/
class Preset where
  dummy : Nat := 0

/-- The child's config stand-in. -/
class Config where
  dummy : Nat := 0

@[reducible] def mini : Preset := {}

/-- The child's container: the same field, so the replayed read typechecks. -/
forkcontainer Toy where
  slot : CLUint64

state_preamble Toy

state_section

/-- The child's override of the factor. -/
forkdef factor : CLUint64 := 3

-- The inherited body, replayed into the child's section. The raw body's
-- `factor` and `slot` resolve here, to the child's declarations.
inherit scaledSlot

end   -- closes the section opened by `state_section`

end ChildChecked

/-! ## The pins -/

section Eval

open SizzLean.Cache
open SizzLean.Hasher

/-- The base's own body: slot 4 at factor 2 is 8. -/
example :
    (letI : BaseChecked.Preset := BaseChecked.mini
     letI : HasherTag := fastHasherTag
     let st0 : @BaseChecked.State BaseChecked.mini fastHasherTag :=
       ({ slot := 4 } : @BaseChecked.Toy BaseChecked.mini)
     let action : EStateM StateTransitionError
         (@BaseChecked.State BaseChecked.mini fastHasherTag) CLUint64 :=
       BaseChecked.scaledSlot
     match action.run st0 with
     | .ok v _   => v.toPlainNat
     | .error _ _ => 0)
      = 8 := by native_decide

/-- The replayed body in the child late-binds to the child's `factor`: slot 4
at factor 3 is 12, not the base's 8. -/
example :
    (letI : ChildChecked.Preset := ChildChecked.mini
     letI : HasherTag := fastHasherTag
     let st0 : @ChildChecked.State ChildChecked.mini fastHasherTag :=
       ({ slot := 4 } : @ChildChecked.Toy ChildChecked.mini)
     let action : EStateM StateTransitionError
         (@ChildChecked.State ChildChecked.mini fastHasherTag) CLUint64 :=
       ChildChecked.scaledSlot
     match action.run st0 with
     | .ok v _   => v.toPlainNat
     | .error _ _ => 0)
      = 12 := by native_decide

/-- The replayed body's checked multiply faults in the child too: slot `max`
at factor 3 passes 2^64, and the §4.4 lift surfaces it as the machine's
`.arithmetic` reject. A replay that dropped the checked bind (a raw wrapping
multiply) would answer `.ok` here and fail this pin. -/
example :
    (letI : ChildChecked.Preset := ChildChecked.mini
     letI : HasherTag := fastHasherTag
     let st0 : @ChildChecked.State ChildChecked.mini fastHasherTag :=
       ({ slot := 18446744073709551615 } : @ChildChecked.Toy ChildChecked.mini)
     let action : EStateM StateTransitionError
         (@ChildChecked.State ChildChecked.mini fastHasherTag) CLUint64 :=
       ChildChecked.scaledSlot
     match action.run st0 with
     | .ok _ _   => false
     | .error e _ => e == StateTransitionError.arithmetic "*")
      = true := by native_decide

end Eval

end EthCLLib.Tests.CLInheritChecked
