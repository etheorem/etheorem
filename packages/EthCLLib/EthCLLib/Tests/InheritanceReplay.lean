import EthCLLib.Spec.Forms

/-!
# `EthCLLib.Tests.InheritanceReplay`: the inheritance-replay self-test

Graduates the Phase 0.2 spike into `EthCLLib` (`PLAN.md` §0.2, §1.1 acceptance).
It confirms the one load-bearing property of *the inheritance mechanism*: an
inherited caller late-binds to the **child's** override of a sibling, the
open-recursion case a symbol-level copy or alias gets wrong.

`Base.caller` calls sibling `callee` (= 1), so `Base.caller = 11`. `Child`
overrides `callee` (= 2) and `inherit`s `caller`. If `inherit` replayed the
raw body in the child namespace and late-bound, `Child.caller` reads
`Child.callee` and is `12`; if it early-bound (copy / alias), it would read
`Base.callee` and be `11`. The `#guard` pins `12`.
-/

open EthCLLib.Spec

namespace EthCLLib.Tests.InheritanceReplay

namespace Base
fork Base
forkdef callee : Nat := 1
forkdef caller : Nat := callee + 10
end Base

namespace Child
fork Child from Base
forkdef callee : Nat := 2          -- overrides Base's callee
inherit caller                      -- inherited; body re-elaborated in Child
end Child

-- Base's caller reads Base's callee.
#guard Base.caller = 11

-- The inherited caller in Child late-binds to Child's override (12), not Base's
-- callee (which would give 11). This is the property the design says a copy or
-- alias would get wrong.
#guard Child.caller = 12

end EthCLLib.Tests.InheritanceReplay
