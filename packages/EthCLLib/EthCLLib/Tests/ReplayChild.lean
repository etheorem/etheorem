import EthCLLib.Tests.ReplayBase

/-!
# `EthCLLib.Tests.ReplayChild`: the child fork of the cross-module replay test

Inherits `caller` from `EthCLLib.Tests.ReplayForks.Base` (an imported module) and
overrides its sibling `callee`. If the capture extensions persisted through the
`.olean`, the resolver finds Base's captured `caller`, replays it here, and it
late-binds to this fork's `callee` (= 2), so `Child.caller = 12`. A failure to
persist would surface as `inherit: no ancestor …` at build time. The replayed
`Gapped` container checks that a progressive mask hole persists the same way.
-/

open EthCLLib.Spec

namespace EthCLLib.Tests.ReplayForks.Child

fork Child from Base
forkdef callee : Nat := 2
inherit caller

/-- The child's `Preset` stand-in, for the replayed container's `[Preset]` binder. -/
class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

inherit Gapped

/-- The replayed container keeps the parent's mask hole: the capture recorded the
`@[sizzlean_progressive_gaps 1]` positions and the replay re-emitted them. A replay
that dropped them would derive the all-active `[true, true]` mask and fail `rfl`. -/
example : SizzLean.SSZRepr.shape (T := @Gapped mini) =
    .progressiveContainer [true, false, true] [.uintN 16, .uintN 8] := rfl

end EthCLLib.Tests.ReplayForks.Child

-- Cross-module late binding: the inherited caller resolves the sibling to
-- Child's override across the module boundary.
#guard EthCLLib.Tests.ReplayForks.Child.caller = 12
#guard EthCLLib.Tests.ReplayForks.Base.caller = 11
