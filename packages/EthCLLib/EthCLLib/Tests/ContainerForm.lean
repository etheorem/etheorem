import EthCLLib

/-!
# `EthCLLib.Tests.ContainerForm`: minimal `forkcontainer` self-test

Isolates the container front-end from the full spec: a local `Preset` stand-in
and two tiny containers (one flat, one symbolic-cap), confirming `forkcontainer`
parses the field block, derives `SSZRepr`, and reduces the shape at a concrete
preset.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Repr

namespace EthCLLib.Tests.ContainerForm

/-- Local preset stand-in with one cap. -/
class Preset where
  registryLimit : Nat

namespace Const
@[reducible] def registryLimit [Preset] : Nat := Preset.registryLimit
end Const

@[reducible] def mini : Preset := { registryLimit := 8 }

forkcontainer Flat where
  a : UInt64
  b : UInt64

forkcontainer WithCap where
  vals   : SSZList UInt64 Const.registryLimit
  marker : UInt64

/-- The flat container's shape reduces at the concrete preset. -/
example : (SizzLean.SSZRepr.shape (T := @Flat mini)) = .container [.uintN 64, .uintN 64] := rfl

/-- The symbolic-cap container's shape reduces at the concrete preset. -/
example : (SizzLean.SSZRepr.shape (T := @WithCap mini)) = .container [.list (.uintN 64) 8, .uintN 64] := rfl

end EthCLLib.Tests.ContainerForm
