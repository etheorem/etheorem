import LeanHazmatSha256
import SizzLean.Hasher.Sha256Batch
import LeanSha256.Core

/-!
# `SizzLeanTests.Sha256BatchEquivalence`: batched FFI ↔ pure-Lean

Mirrors the scalar equivalence test in `Sha256Equivalence.lean`.
The batched FFI primitive `sha256BatchCombine` must agree
pointwise with the pure-Lean `LeanSha256.combine` reference on
every input pair,
and on every array length (including the empty array, which is
the edge case the C shim's loop must handle correctly).

## Coverage

* **Empty input**: `sha256BatchCombine #[] #[] = #[]`.
* **Single pair**: degenerates to a scalar combine.
* **Two pairs**: covers the loop's increment path.
* **Eight pairs**: Merkle-tree depth-3 level worth.
* **Distinct vs. zero leaves**: separately exercises zero-byte
  inputs and the `Vector.replicate 32 k` populated-leaf shapes
  the SSZ Merkle code uses.

Each case is one `native_decide` byte-equality. A C-shim
divergence fails the build with the diverging input visible in
the error trace.

The full property "FFI ≡ spec on *every* input pair" is
asserted via the named axiom
`sha256BatchCombine_eq_spec` in `Hasher/Sha256Batch.lean`; this
file is the empirical evidence that backs that axiom.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SizzLeanTests.Sha256BatchEquivalence

-- `sha256BatchCombine` is the FFI primitive (in `LeanHazmatSha256`);
-- `sha256BatchCombineSpec` is the pure-Lean reference (kept in
-- `SizzLean.Hasher.Sha256Batch` next to the equivalence axiom).
open LeanHazmat.Sha256 SizzLean.Hasher

private def z32 : ByteArray := ByteArray.mk (Array.replicate 32 0)
private def one32 : ByteArray := ByteArray.mk (Array.replicate 32 1)
private def aa32 : ByteArray := ByteArray.mk (Array.replicate 32 0xaa)
private def bb32 : ByteArray := ByteArray.mk (Array.replicate 32 0xbb)
private def cc32 : ByteArray := ByteArray.mk (Array.replicate 32 0xcc)
private def dd32 : ByteArray := ByteArray.mk (Array.replicate 32 0xdd)
private def ee32 : ByteArray := ByteArray.mk (Array.replicate 32 0xee)
private def ff32 : ByteArray := ByteArray.mk (Array.replicate 32 0xff)

/-! ### Case 1: empty input -/

example : sha256BatchCombine #[] #[] = #[] := by native_decide

/-! ### Case 2: single pair, zero leaves -/

example :
    sha256BatchCombine #[z32] #[z32]
      = #[LeanSha256.combine z32 z32] := by native_decide

/-! ### Case 3: single pair, distinct leaves -/

example :
    sha256BatchCombine #[aa32] #[bb32]
      = #[LeanSha256.combine aa32 bb32] := by native_decide

/-! ### Case 4: two pairs (covers loop increment) -/

example :
    sha256BatchCombine #[aa32, bb32] #[cc32, dd32]
      = #[LeanSha256.combine aa32 cc32, LeanSha256.combine bb32 dd32] := by
  native_decide

/-! ### Case 5: eight pairs (Merkle depth-3 level worth) -/

example :
    sha256BatchCombine
        #[z32, aa32, bb32, cc32, dd32, ee32, ff32, one32]
        #[one32, bb32, aa32, dd32, cc32, ff32, ee32, z32]
      = #[ LeanSha256.combine z32 one32,
           LeanSha256.combine aa32 bb32,
           LeanSha256.combine bb32 aa32,
           LeanSha256.combine cc32 dd32,
           LeanSha256.combine dd32 cc32,
           LeanSha256.combine ee32 ff32,
           LeanSha256.combine ff32 ee32,
           LeanSha256.combine one32 z32 ] := by native_decide

/-! ### Case 6: order matters (left ↔ right swap produces different digest) -/

example :
    sha256BatchCombine #[aa32, bb32] #[bb32, aa32]
      ≠ sha256BatchCombine #[bb32, aa32] #[aa32, bb32] := by native_decide

/-! ### Case 7: pointwise equivalence with the spec function -/

example :
    sha256BatchCombine #[aa32, bb32, cc32] #[dd32, ee32, ff32]
      = sha256BatchCombineSpec #[aa32, bb32, cc32] #[dd32, ee32, ff32] := by
  native_decide

end SizzLeanTests.Sha256BatchEquivalence
