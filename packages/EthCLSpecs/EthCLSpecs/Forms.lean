import EthCLLib.Spec

/-!
# `EthCLSpecs.Forms`: spec-local container shorthands

`signedwrapper SignedX wraps X` is the two-field `Signed*` envelope (`message : X`,
`signature : BLSSignature`) that recurs seven times across both forks, written once. It
expands to the framework `forkcontainer`, so the generated type is captured for inheritance
exactly as a hand-written one would be.

The shorthand is spec-owned, not a framework form: the framework's `forkcontainer` stays
domain-agnostic (arbitrary fields), while `signedwrapper` bakes in `BLSSignature`, a consensus
type. That field name is emitted unhygienically (`mkIdent`) so it resolves at the *use* site,
the fork namespace that defines `BLSSignature`, which is why this module imports only the
framework and never the spec types it names.
-/

set_option autoImplicit false

open Lean
open EthCLLib.Spec

namespace EthCLSpecs

/-- `signedwrapper SignedX wraps X`: declare the SSZ envelope `{ message : X, signature :
BLSSignature }` as a `forkcontainer`. The field order (`message` then `signature`) is the SSZ
hash-tree-root contract, so the shape is fixed and not author-configurable. It forwards
`declModifiers`, so the declaration's docstring rides through to the generated container, and
`BLSSignature` resolves at the expansion site. -/
scoped syntax (name := signedwrapperCmd) declModifiers
  "signedwrapper " ident " wraps " ident : command

macro_rules
  | `($mods:declModifiers signedwrapper $name:ident wraps $wrapped:ident) => do
      let blsSig := mkIdent `BLSSignature
      `($mods:declModifiers forkcontainer $name where
          message   : $wrapped
          signature : $blsSig)

end EthCLSpecs
