import EthCLLib.Spec.Forms

/-!
# `EthCLLib.Tests.LineageGapCheck`: the lineage cross-check on gap markers

`forkcontainer`'s elaborator diffs a progressive redeclaration's field block
against the nearest ancestor's captured block (`Forms.expectedGapsFromLineage`).
One fork per case, each redeclaring the base fork's `State5` under the same
name, the pattern a fork-level container diff really takes:

1. `Missing`: marker absent, fields deleted. A warning names the marker, the
   computed gaps drive the mask, and the holes land in the derived shape.
2. `Matched`: marker present and equal to the diff. Silent.
   `Gapped` / `GrandGapped`: hole accumulation over two generations, the
   grandchild's deletions mapped through the parent's mask.
   `SameBlock`: an unchanged block over a gapped parent is reminded of the
   inherited hole. `InheritedWrong`: a marker that drops the inherited hole
   fails against the accumulated list.
3. `Appended`: a pure append computes no gaps. Silent.
   `AppendedGapped`: an append over a gapped parent is reminded of the
   inherited hole.
4. `Swapped`: a replaced field is not expressible as gaps, so the diff bails.
   Silent. `SwappedGapped`: the same under a gapped parent.
5. `Wrong`: marker present and disagreeing with the diff. An error names both
   lists.
6. `Classic`: a classic redeclaration carries no mask, so the check does not
   run at all.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.LineageGapCheck.Base

fork Base

/-- A local `Preset` stand-in: `forkcontainer` binds `[Preset]`, and the name
resolves in the fork's own namespace. -/
class Preset where
  unused : Nat := 0

/-- The ancestor container: five fields, positions 0 through 4. -/
forkcontainer State5 where
  a : UInt64
  b : UInt8
  c : UInt64
  d : UInt8
  e : UInt64

end EthCLLib.Tests.LineageGapCheck.Base

/-! Case 1: no marker, fields `b` and `d` deleted. -/
namespace EthCLLib.Tests.LineageGapCheck.Missing

fork Missing from Base

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

/-- warning: 'EthCLLib.Tests.LineageGapCheck.Missing.State5' is progressive and writes no gap marker. The lineage diff against 'EthCLLib.Tests.LineageGapCheck.Base.State5' computes gaps #[1, 3]. Write @[sizzlean_progressive, sizzlean_progressive_gaps 1 3] so the mask is checked against the ancestor's field block. -/
#guard_msgs (warning) in
@[sizzlean_progressive]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  e : UInt64

/-- The adopted gaps land in the derived mask: holes at positions 1 and 3. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .progressiveContainer [true, false, true, false, true]
        [.uintN 64, .uintN 64, .uintN 64] := rfl

end EthCLLib.Tests.LineageGapCheck.Missing

/-! Case 2: the marker matches the diff, so the declaration is silent. -/
namespace EthCLLib.Tests.LineageGapCheck.Matched

fork Matched from Base

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

@[sizzlean_progressive, sizzlean_progressive_gaps 1 3]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  e : UInt64

/-- The written marker produces the same mask the diff computed. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .progressiveContainer [true, false, true, false, true]
        [.uintN 64, .uintN 64, .uintN 64] := rfl

end EthCLLib.Tests.LineageGapCheck.Matched

/-! Case 2b: gap accumulation. `Gapped` deletes field `b`, hole at mask
position 1. `GrandGapped` then deletes field `d` from `Gapped`'s block, so its
own hole sits at mask position 3, and it re-states the inherited hole at 1.
The warning names both; the adopted mask puts holes at 1 and 3. -/
namespace EthCLLib.Tests.LineageGapCheck.Gapped

fork Gapped from Base

class Preset where
  unused : Nat := 0

@[sizzlean_progressive, sizzlean_progressive_gaps 1]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  d : UInt8
  e : UInt64

end EthCLLib.Tests.LineageGapCheck.Gapped

namespace EthCLLib.Tests.LineageGapCheck.GrandGapped

fork GrandGapped from Gapped

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

/-- warning: 'EthCLLib.Tests.LineageGapCheck.GrandGapped.State5' is progressive and writes no gap marker. The lineage diff against 'EthCLLib.Tests.LineageGapCheck.Gapped.State5' computes gaps #[1, 3]. Write @[sizzlean_progressive, sizzlean_progressive_gaps 1 3] so the mask is checked against the ancestor's field block. -/
#guard_msgs (warning) in
@[sizzlean_progressive]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  e : UInt64

/-- The inherited hole at 1 and the new hole at 3 land in the derived mask. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .progressiveContainer [true, false, true, false, true]
        [.uintN 64, .uintN 64, .uintN 64] := rfl

end EthCLLib.Tests.LineageGapCheck.GrandGapped

/-! Case 2c: the grandchild redeclares `Gapped`'s block unchanged. The diff
computes no new holes, and the accumulated list is `Gapped`'s own, so a
marker-less declaration is reminded of the inherited hole. -/
namespace EthCLLib.Tests.LineageGapCheck.SameBlock

fork SameBlock from Gapped

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

/-- warning: 'EthCLLib.Tests.LineageGapCheck.SameBlock.State5' is progressive and writes no gap marker. The lineage diff against 'EthCLLib.Tests.LineageGapCheck.Gapped.State5' computes gaps #[1]. Write @[sizzlean_progressive, sizzlean_progressive_gaps 1] so the mask is checked against the ancestor's field block. -/
#guard_msgs (warning) in
@[sizzlean_progressive]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  d : UInt8
  e : UInt64

/-- The inherited hole survives the redeclaration. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .progressiveContainer [true, false, true, true, true]
        [.uintN 64, .uintN 64, .uintN 8, .uintN 64] := rfl

end EthCLLib.Tests.LineageGapCheck.SameBlock

/-! Case 2d: the grandchild deletes another field but writes only its own hole,
missing the inherited one. The error names the accumulated list. -/
namespace EthCLLib.Tests.LineageGapCheck.InheritedWrong

fork InheritedWrong from Gapped

class Preset where
  unused : Nat := 0

/-- error: 'EthCLLib.Tests.LineageGapCheck.InheritedWrong.State5' declares @[sizzlean_progressive, sizzlean_progressive_gaps 3], but the lineage diff against 'EthCLLib.Tests.LineageGapCheck.Gapped.State5' computes gaps #[1, 3]. Fix the marker or restate the field block so the two agree. -/
#guard_msgs (error) in
@[sizzlean_progressive, sizzlean_progressive_gaps 3]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  e : UInt64

end EthCLLib.Tests.LineageGapCheck.InheritedWrong

/-! Case 3: a pure append computes no gaps, so a marker-less declaration is
silent. -/
namespace EthCLLib.Tests.LineageGapCheck.Appended

fork Appended from Base

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

@[sizzlean_progressive]
forkcontainer State5 where
  a : UInt64
  b : UInt8
  c : UInt64
  d : UInt8
  e : UInt64
  f : UInt8

/-- The all-active mask covers the appended field too. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .progressiveContainer [true, true, true, true, true, true]
        [.uintN 64, .uintN 8, .uintN 64, .uintN 8, .uintN 64, .uintN 8] := rfl

end EthCLLib.Tests.LineageGapCheck.Appended

/-! Case 4: a replaced field is not expressible as gaps, so the diff bails and
the declaration is silent. -/
namespace EthCLLib.Tests.LineageGapCheck.Swapped

fork Swapped from Base

class Preset where
  unused : Nat := 0

@[sizzlean_progressive]
forkcontainer State5 where
  a : UInt64
  x : UInt8
  c : UInt64
  d : UInt8
  e : UInt64

end EthCLLib.Tests.LineageGapCheck.Swapped

/-! Case 5: the marker disagrees with the diff (it misses position 3), and the
declaration fails with both lists named. -/
namespace EthCLLib.Tests.LineageGapCheck.Wrong

fork Wrong from Base

class Preset where
  unused : Nat := 0

/-- error: 'EthCLLib.Tests.LineageGapCheck.Wrong.State5' declares @[sizzlean_progressive, sizzlean_progressive_gaps 1], but the lineage diff against 'EthCLLib.Tests.LineageGapCheck.Base.State5' computes gaps #[1, 3]. Fix the marker or restate the field block so the two agree. -/
#guard_msgs (error) in
@[sizzlean_progressive, sizzlean_progressive_gaps 1]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  e : UInt64

end EthCLLib.Tests.LineageGapCheck.Wrong

/-! Case 6: the redeclaration is classic, so no mask exists and the check does
not run, however the field block differs. The shape is a plain container. -/
namespace EthCLLib.Tests.LineageGapCheck.Classic

fork Classic from Base

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

forkcontainer State5 where
  a : UInt64
  c : UInt64
  e : UInt64

/-- No attribute, no mask: the classic container keeps its plain shape. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .container [.uintN 64, .uintN 64, .uintN 64] := rfl

end EthCLLib.Tests.LineageGapCheck.Classic

/-! Case 3b: an append over a gapped parent. The diff computes no new holes,
and the accumulated list is the parent's own, so the marker-less declaration is
reminded of the inherited hole. -/
namespace EthCLLib.Tests.LineageGapCheck.AppendedGapped

fork AppendedGapped from Gapped

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

/-- warning: 'EthCLLib.Tests.LineageGapCheck.AppendedGapped.State5' is progressive and writes no gap marker. The lineage diff against 'EthCLLib.Tests.LineageGapCheck.Gapped.State5' computes gaps #[1]. Write @[sizzlean_progressive, sizzlean_progressive_gaps 1] so the mask is checked against the ancestor's field block. -/
#guard_msgs (warning) in
@[sizzlean_progressive]
forkcontainer State5 where
  a : UInt64
  c : UInt64
  d : UInt8
  e : UInt64
  f : UInt8

/-- The appended field goes after the inherited hole. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .progressiveContainer [true, false, true, true, true, true]
        [.uintN 64, .uintN 64, .uintN 8, .uintN 64, .uintN 8] := rfl

end EthCLLib.Tests.LineageGapCheck.AppendedGapped

/-! Case 4b: a replaced field under a gapped parent bails the same way, and the
declaration is silent. -/
namespace EthCLLib.Tests.LineageGapCheck.SwappedGapped

fork SwappedGapped from Gapped

class Preset where
  unused : Nat := 0

@[reducible] def mini : Preset := {}

@[sizzlean_progressive]
forkcontainer State5 where
  a : UInt64
  x : UInt8
  d : UInt8
  e : UInt64

/-- The diff bailed, so no marker was adopted: all-active over the written
fields. -/
example : SizzLean.SSZRepr.shape (T := @State5 mini) =
    .progressiveContainer [true, true, true, true]
        [.uintN 64, .uintN 8, .uintN 8, .uintN 64] := rfl

end EthCLLib.Tests.LineageGapCheck.SwappedGapped
