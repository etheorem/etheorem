import EthCLLib.Spec.Forms

/-!
# `EthCLLib.Tests.ReplayBase`: the base fork of the cross-module replay test

The companion of `EthCLLib.Tests.ReplayChild`. The two together confirm that the
capture extensions survive into the `.olean`, so a child fork in a *separate
module* can `inherit` a parent declared in an *imported* one, the real shape
Fulu (one module set) and Gloas (another) rely on. `InheritanceReplay` proves
late binding within a single file; this pair proves it across the module
boundary.
-/

open EthCLLib.Spec

namespace EthCLLib.Tests.ReplayForks.Base

fork Base
forkdef callee : Nat := 1
forkdef caller : Nat := callee + 10

/-- Adds `callee` to `k` until `k` is greater than `n`. `callee` can be `0`, and then the loop
does not stop. So Lean cannot show termination, and the body is a `partial_fixpoint`. The
capture records the clause with the body. A child fork that replays the body gets the clause
too. -/
forkdef firstAbove (n k : Nat) : Nat :=
  if k > n then k else firstAbove n (k + callee)
partial_fixpoint

end EthCLLib.Tests.ReplayForks.Base
