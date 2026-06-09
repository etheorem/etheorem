/-!
# `SizzLean.Spec.Constants`: wire-format constants

Numeric constants from the consensus-specs *§SSZ Types, Constants*
table (`simple-serialize.md`). One canonical home so encoders,
decoders, and Merkleization share a single source of truth (DRY);
changing a value here cascades through the build, which is what we
want.
-/

set_option autoImplicit false

namespace SizzLean.Spec

/-- *Bytes per Merkleization chunk.* Every leaf in an SSZ Merkle tree
is a 32-byte `chunk`, basic types are right-padded to this width and
composite types' contents are concatenated and split into chunks of
this size. Per consensus-specs *§Merkleization*. -/
def BYTES_PER_CHUNK : Nat := 32

/-- *Bytes per offset in the variable-size prefix.* Variable-size
fields in a container are written as a fixed-width `uint32` offset
followed (after all fixed-size fields) by the body. Per consensus-specs
*§Serialization, variable-size types*. -/
def BYTES_PER_LENGTH_OFFSET : Nat := 4

/-- *Maximum permitted SSZ object length.* Hard upper bound on the
total serialized byte length, matching `BYTES_PER_LENGTH_OFFSET = 4`
(an offset is a `uint32`). Per consensus-specs
*§Serialization, variable-size types*. -/
def MAX_LENGTH : Nat := 2 ^ 32

end SizzLean.Spec
