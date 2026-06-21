import EthCLLib.Tests.ReplayBase

/-!
# `EthCLLib.Tests.ReplayChild`: the child fork of the cross-module replay test

Inherits `caller` from `EthCLLib.Tests.ReplayForks.Base` (an imported module) and
overrides its sibling `callee`. If the capture extensions persisted through the
`.olean`, the resolver finds Base's captured `caller`, replays it here, and it
late-binds to this fork's `callee` (= 2), so `Child.caller = 12`. A failure to
persist would surface as `inherit: no ancestor …` at build time.
-/

open EthCLLib.Spec

namespace EthCLLib.Tests.ReplayForks.Child

fork Child from Base
forkdef callee : Nat := 2
inherit caller

end EthCLLib.Tests.ReplayForks.Child

-- Cross-module late binding: the inherited caller resolves the sibling to
-- Child's override across the module boundary.
#guard EthCLLib.Tests.ReplayForks.Child.caller = 12
#guard EthCLLib.Tests.ReplayForks.Base.caller = 11
