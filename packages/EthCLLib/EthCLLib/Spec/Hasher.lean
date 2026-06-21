import SizzLean

/-!
# `EthCLLib.Spec.Hasher`: the `HasherTag` selector class

SizzLean's `Hasher (H)` class stays untouched; the framework adds only a
*selector* that carries the chosen hasher tag as a field, so it threads by
instance resolution exactly like `[Preset]` (`FRAMEWORK_ARCHITECTURE.md` §8). A
free `{H}` type variable does not thread into caller steps (the metavariable
failure a value-implicit binder hits), so the tag rides a class field instead.

`HasherTag.H` is the hasher the boxed `State` uses. The fast configuration picks
`Sha256` (FFI, opaque); the pure configuration picks `Sha256Spec` (pure-Lean,
kernel-reducible). Both selectors are `@[reducible] def`s the runner/proofs
inject at the call boundary, kept unregistered (not global instances) so the two
coexist without clashing, the same discipline the preset tier uses.
-/

set_option autoImplicit false

open SizzLean
open SizzLean.Hasher

namespace EthCLLib.Spec

/-- The framework's hasher selector. Carries the chosen `Hasher` tag as the
field `H`, with its `Hasher H` instance as a plain field surfaced through the
reducible instance below (the instance must be reducible so instance search sees
through `HasherTag.H` to the concrete hasher). -/
class HasherTag where
  /-- The chosen hasher tag (`Sha256` or `Sha256Spec`). -/
  H : Type
  /-- The `Hasher` instance for `H`. -/
  hasher : Hasher H

/-- Surface a `[HasherTag]`'s carried `Hasher` instance for instance search.
Reducible so a goal `Hasher HasherTag.H` reduces through to the concrete
instance. -/
@[reducible] instance instHasherOfTag [t : HasherTag] : Hasher t.H := t.hasher

/-- The fast configuration's hasher selector: the FFI `Sha256`. `@[reducible]`
so `HasherTag.H` reduces to `Sha256` under `rfl` / `native_decide`. Injected by
the runner, not registered globally, so it never clashes with `pureHasherTag`. -/
@[reducible] def fastHasherTag : HasherTag := { H := Sha256, hasher := inferInstance }

/-- The pure configuration's hasher selector: the kernel-reducible `Sha256Spec`.
`@[reducible]` for the same reason. Injected by the theorems module. -/
@[reducible] def pureHasherTag : HasherTag := { H := Sha256Spec, hasher := inferInstance }

end EthCLLib.Spec
