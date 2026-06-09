import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Fulu.Primitives`: Fulu / PeerDAS primitives

Fulu introduces *cell-based* blob commitments for PeerDAS sampling.
Constants (preset-invariant at v1.5.0):

* `BYTES_PER_FIELD_ELEMENT = 32`
* `FIELD_ELEMENTS_PER_CELL = 64`
* `BYTES_PER_CELL = BYTES_PER_FIELD_ELEMENT * FIELD_ELEMENTS_PER_CELL = 2048`
* `NUMBER_OF_COLUMNS = 128`
-/

set_option autoImplicit false

namespace LeanEthCS

open SizzLean

/-- Column index in the extended data-availability matrix. -/
abbrev ColumnIndex := UInt64

/-- Row index in the extended data-availability matrix. -/
abbrev RowIndex := UInt64

/-- One cell of blob data, `BYTES_PER_CELL = 2048` bytes
(`FIELD_ELEMENTS_PER_CELL = 64` elements × 32 bytes each). -/
abbrev Cell := Vector UInt8 2048

end LeanEthCS
