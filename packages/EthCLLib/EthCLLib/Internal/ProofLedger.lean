import Lean
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.Internal.ProofLedger`: the `characterizes` attribute

The proof-coverage report (`scripts/ProofCoverage.lean`) grades every spec
function in three tiers. Tier 0 is *executable*, and every spec function is
there by construction. Tier 1 is *touched*: some theorem statement under
`EthCLSpecs.Proofs` mentions the function, which the report computes on its own.
Tier 2 is *characterized*, and no machine can compute it, because "this theorem
states the function's main contract" is a claim a person makes. This module is
where a person makes it:

```lean
@[characterizes EthCLSpecs.Gloas.processOperations]
theorem processOperations_run_ok_iff : …
```

An attribute carries the claim, rather than a naming convention or a list in a
markdown file, because the attribute is checked where the proof is written. The
registration below rejects a tag whose target does not exist, whose target is no
`forkdef` (`isSpecFunction`, in `EthCLLib.Internal.Capture`), or whose target the
tagged theorem's own statement never mentions. So a rename of a spec function
breaks the build in the file that carries the proof, and the report never counts
a claim about a function the statement is silent on.

The pairs live in a `SimplePersistentEnvExtension`, the same storage
`captureExt` uses, so the tags reach the `.olean` and the report reads them back
out of an imported environment with no source scraping.

## Lean idioms annotated on first appearance

* `registerBuiltinAttribute`: registers an attribute whose `add` handler runs
  during elaboration. `registerTagAttribute` and `registerParametricAttribute`
  both call it; going direct is what lets the entries land in a
  `SimplePersistentEnvExtension`, whose `addImportedFn` merges every imported
  module's entries into one state. The parametric wrapper keeps only *local*
  entries in its state, so enumerating tags across imports would mean walking
  module indices by hand.
* `Lean.Parser.Attr.simple`: the fallback attribute parser, `ident` followed by
  an optional second `ident`. An attribute that takes one name argument needs no
  syntax declaration of its own; `stx[1]` is the argument's optional node.
* `applicationTime := .afterTypeChecking`: run `add` once the declaration is in
  the environment, so the handler can read the theorem's type.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.Internal

/-- Every `characterizes` tag, as `(theoremName, specFunction)` pairs.

An `Array` (not a map) keeps the merge across imports trivial, and one function
may carry several characterizations, so the storage must not be keyed by target.
The report scans the array once. -/
initialize characterizesExt :
    SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- The tag's target, resolved and validated against the tagged theorem.

Split out of the attribute registration so the two failure messages read as one
piece of prose, and so the registration stays a handful of lines. -/
private def validateCharacterizes (thm : Name) (targetStx : Syntax) :
    AttrM Name := do
  let target ← resolveGlobalConstNoOverload targetStx
  let env ← getEnv
  unless isSpecFunction env target do
    throwError "`characterizes` target `{target}` is no spec function: only a \
      constant some `forkdef` declared can be characterized. Containers, \
      abbrevs, instances, tiers, and plain `def`s inside a fork body stay \
      outside the coverage denominator."
  let some info := env.find? thm
    | throwError "`characterizes` cannot read `{thm}`'s statement."
  unless info.type.getUsedConstants.contains target do
    throwError "`{thm}`'s statement never mentions `{target}`, so the theorem \
      cannot characterize it. State the contract over `{target}` itself, or \
      drop the tag and let the theorem count as a touched-tier mention."
  return target

/-- `@[characterizes f]` on a theorem claims that the theorem states `f`'s main
contract. `f` must be a spec function, and the theorem's statement must mention
it. -/
initialize registerBuiltinAttribute {
  name            := `characterizes
  descr           := "this theorem states the named spec function's main contract"
  applicationTime := .afterTypeChecking
  add             := fun thm stx kind => do
    unless kind == AttributeKind.global do
      throwError "`characterizes` is a global attribute; `local` and `scoped` \
        would hide the claim from the coverage report."
    let some targetStx := stx[1].getOptional?
      | throwError "`characterizes` needs the spec function it characterizes, \
          for example `@[characterizes EthCLSpecs.Gloas.processOperations]`."
    let target ← validateCharacterizes thm targetStx
    modifyEnv fun env => characterizesExt.addEntry env (thm, target)
}

/-- Every `characterizes` tag in the environment. -/
def characterizations (env : Environment) : Array (Name × Name) :=
  characterizesExt.getState env

end EthCLLib.Internal
