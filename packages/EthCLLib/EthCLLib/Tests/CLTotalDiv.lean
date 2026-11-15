import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Tests.CLTotalDiv`: total division by a proof-carrying divisor

Division and modulo cannot leave the `uint64` range, so a checked divide raises on a zero
divisor alone (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §3.2). `PositiveDivisor` is the
mechanism that drops that raise once a divisor's positivity is known statically: a preset
constant such as `SLOTS_PER_EPOCH` wraps its positivity once, and `slot / d` then returns a
plain `CLUint64` with no bind, so `compute_epoch_at_slot` keeps its pure
`Slot → Epoch` shape across its ~50 call sites.

This module pins what matters: the value on a non-multiple, the totality (no `Checked` in the
result type), the closed route for a zero divisor, and the checked `/` route that keeps its
raise. Since task 4.4 moved `Slot` to `CLUint64`, the fork body's `computeEpochAtSlot`
reads `slot / Const.slotsPerEpochDiv` directly; the stand-in below pins the same route.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.CLTotalDiv

/-- A stand-in for the fork's wrapped preset constant, the plan's
`forkabbrev slotsPerEpochDiv : PositiveDivisor := ⟨Const.slotsPerEpoch, Const.slotsPerEpochPos⟩`.
`SLOTS_PER_EPOCH = Slot(32)` at mainnet (`phase0/mainnet.py:111`), and the positivity is
discharged once, here. -/
def slotsPerEpochDiv : PositiveDivisor := ⟨32, by decide⟩

/-- The shape `compute_epoch_at_slot` takes once `Slot` moves to `CLUint64`
(`fulu/mainnet.py:1364-1368`, `Epoch(slot // SLOTS_PER_EPOCH)`): a plain function, no bind,
no `Checked` in the type. -/
def computeEpochAtSlot (slot : CLUint64) : CLUint64 := slot / slotsPerEpochDiv

/-! ## Totality: the quotient is a plain `CLUint64` -/

-- The type ascription holds with no `Checked` and no bind.
example : CLUint64 := (33 : CLUint64) / slotsPerEpochDiv
example : CLUint64 := (33 : CLUint64) % slotsPerEpochDiv
example : CLUint64 := computeEpochAtSlot (CLUint64.trustedOfUInt64 33)

/-! ## The value on a non-multiple -/

-- The quotient floors as Python's `//` does on non-negative values.
example : computeEpochAtSlot (CLUint64.trustedOfUInt64 33) = CLUint64.trustedOfUInt64 1 := rfl
example : computeEpochAtSlot (CLUint64.trustedOfUInt64 31) = CLUint64.trustedOfUInt64 0 := rfl
-- The maximum dividend stays in range; the quotient is at most the dividend.
example : computeEpochAtSlot (CLUint64.trustedOfUInt64 0xffffffffffffffff) =
    CLUint64.trustedOfUInt64 576460752303423487 := rfl
example : ((33 : CLUint64) % slotsPerEpochDiv) = CLUint64.trustedOfUInt64 1 := rfl

-- The `amount - amount % INCREMENT` shape with a total `%`; the `-` keeps its own checked
-- test, so the expression stays `Checked CLUint64` and the bind stays.
example : ((33 : CLUint64) - (33 : CLUint64) % slotsPerEpochDiv : Checked CLUint64) =
    .ok (CLUint64.trustedOfUInt64 32) := rfl

/-! ## A zero divisor cannot enter the total route

`PositiveDivisor` has no route that skips the proof: the constructor demands `0 < val`, and
`0 < 0` is false. A `⟨0, rfl⟩` build fails to compile, and the exact failure is pinned. There
is no `OfNat` instance either, so a bare literal cannot stand in for a claimed-positive
divisor; the second block pins that the literal keeps the checked `/` route.
-/

/-- error: Application type mismatch: The argument
  rfl
has type
  ?m.4 = ?m.4
but is expected to have type
  0 < 0
in the application
  { val := 0, pos := ⋯ } -/
#guard_msgs in
example : PositiveDivisor := ⟨0, rfl⟩

-- The constructor route is closed, so the total `/` never sees a zero divisor. The checked
-- route keeps the raise for a genuinely partial divisor.
example : ((1 : CLUint64) / (0 : CLUint64) : Checked CLUint64) = .error (.zeroDivisor "//" 1) := rfl
example : ((1 : CLUint64) % (0 : CLUint64) : Checked CLUint64) = .error (.zeroDivisor "%" 1) := rfl

-- A bare literal divisor keeps the checked route, whose zero-divisor raise stays reachable.
example : ((33 : CLUint64) / 32 : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 1) := rfl
example : ((33 : CLUint64) / (0 : CLUint64) : Checked CLUint64) = .error (.zeroDivisor "//" 33) := rfl

end EthCLLib.Tests.CLTotalDiv
