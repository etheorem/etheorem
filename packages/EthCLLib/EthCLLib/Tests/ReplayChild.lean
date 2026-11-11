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
inherit firstAbove

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

-- The replay of a `partial_fixpoint` body keeps the clause. Without the clause, the replay
-- does not elaborate. The replay also binds `callee` late. Base adds 1 each step
-- (0, 1, …, 5). Child adds 2 (0, 2, 4, 6).
#guard EthCLLib.Tests.ReplayForks.Base.firstAbove 4 0 = 5
#guard EthCLLib.Tests.ReplayForks.Child.firstAbove 4 0 = 6
