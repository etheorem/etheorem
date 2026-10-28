import EthCLLib.Spec.Forms

/-!
# `EthCLLib.Tests.ReplayBase`: the base fork of the cross-module replay test

The companion of `EthCLLib.Tests.ReplayChild`. The two together confirm that the
capture extensions survive into the `.olean`, so a child fork in a *separate
module* can `inherit` a parent declared in an *imported* one, the real shape
Fulu (one module set) and Gloas (another) rely on. `InheritanceReplay` proves
late binding within a single file; this pair proves it across the module
boundary. The pair also carries a progressive container with a mask hole, whose
gap list must survive the same boundary.
-/

open EthCLLib.Spec

namespace EthCLLib.Tests.ReplayForks.Base

fork Base
forkdef callee : Nat := 1
forkdef caller : Nat := callee + 10

/-- A local `Preset` stand-in: `forkcontainer` binds `[Preset]`, and the name
resolves in the fork's own namespace. -/
class Preset where
  unused : Nat := 0

/-- A progressive container with one mask hole (EIP-7495 `active_fields=[1, 0, 1]`).
The child replays it, and the replay has to carry the hole across the module
boundary, as Heze's `BeaconState` does from the fork that declares it. -/
@[sizzlean_progressive, sizzlean_progressive_gaps 1]
forkcontainer Gapped where
  side  : UInt16
  color : UInt8

end EthCLLib.Tests.ReplayForks.Base
