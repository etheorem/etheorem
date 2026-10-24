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
inherit firstAbove

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
