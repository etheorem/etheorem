import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.SerializeCacheCoherence`: serialize coherence

The cached `serialize` operation must preserve the invariant

    box.serialize = SSZ.serialize box.view

for every `box : SSZ.Box H T` and every `TreeBacked H T`, across
mutations. `serialize` is a pure function of `view`, no
memoisation, no Box threading, so the invariant collapses to
"the cached arm's bytes equal the spec serialiser's bytes."

## Coverage

1. **Fresh tree**: `(TreeBacked.ofValue …).serialize` matches
   `SSZ.serialize` on the underlying value.
2. **Post-`sszUpdate`**: `(sszUpdate t with f := v).serialize`
   matches `SSZ.serialize` on the post-update view.
3. **`Box.serialize` parity**: `SSZ.FastBox v |>.serialize` and
   `SSZ.PureBox v |>.serialize` both match `SSZ.serialize v`. The
   uniform user-facing API delivers the same bytes regardless of
   flavour.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SizzLeanTests.SerializeCacheCoherence

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanTests.ExampleContainers

private def f0 : FlatExample :=
  { versionA := Vector.replicate 4 0x11
    versionB := Vector.replicate 4 0x22
    marker   := 7 }

/-! ### Case 1: fresh tree's `.serialize` matches the spec. -/

example :
    (TreeBacked.ofValue Sha256 f0).serialize = SSZ.serialize f0 := by
  native_decide

/-! ### Case 2: `sszUpdate` builds a fresh TreeBacked whose
post-update `.serialize` matches the spec on the new view. -/

example :
    let t  : TreeBacked Sha256 FlatExample := TreeBacked.ofValue Sha256 f0
    let tUpdated := sszUpdate t with marker := 99
    tUpdated.serialize
      = SSZ.serialize ({ f0 with marker := 99 } : FlatExample) := by
  native_decide

/-! ### Case 3: `Box.serialize` matches the spec on both arms. -/

example : (SSZ.FastBox f0).serialize = SSZ.serialize f0 := by native_decide
example : (SSZ.PureBox f0).serialize = SSZ.serialize f0 := by native_decide

end SizzLeanTests.SerializeCacheCoherence
