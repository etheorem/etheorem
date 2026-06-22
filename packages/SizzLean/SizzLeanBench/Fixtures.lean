import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving

/-!
# `SizzLeanBench.Fixtures`: shared bench fixtures

Four SSZ-shaped structures used as the workload payloads
across every scenario in the bench. All `deriving SSZRepr` so
the exact same user code goes through them. They form a
fixture-size ladder so a single scenario shape can be measured
at four points along the tree-depth / payload-size axis.

## `ValidatorShape`

Mirrors the consensus-spec `Validator` layout (no EthCLSpecs
dependency): 8 fixed-size fields, ~144 bytes serialised, depth
4. The smallest fixture, exercising the cache's per-operation
constant-cost path. Wrapper overhead is visible here; payback
from the cache is *not*.

## `ValidatorSet16`

Wraps a `Vector ValidatorShape 16`, 16 nested containers,
~2.3 KB serialised, depth 8. The small "wide" fixture. The
cache wins start to show because every operation walks more
nodes.

## `ValidatorSet256` *(large)*

Wraps a `Vector ValidatorShape 256`, 256 nested containers,
~36 KB serialised, depth 12. The intermediate-scale fixture
where the cache's spine-walking advantage starts to dominate;
each cold root pays ~4 K pair hashes, large enough for any
SIMD-batched SHA-256 path to amortise its overhead.

## `ValidatorSet4096` *(huge)*

Wraps a `Vector ValidatorShape 4096`, 4096 nested containers,
~580 KB serialised, depth 16. The mainnet-shape fixture (still
4× below 1M-validator mainnet, but at the same order of
magnitude). Used in the deepest cold-root row to confirm
scaling and to provide a hard upper bound on per-call costs.

## Salting

Every fixture takes a `UInt8` salt parameter; the salt bytes
flow into the fields so consecutive calls with different salts
produce structurally-distinct values. This defeats Lean's
constant-folding on top-level constant values, which would
otherwise make the bench timings meaningless (the runtime
would memoise the result of one call and return it for all
subsequent calls).
-/

set_option autoImplicit false

namespace SizzLeanBench.Fixtures

open SizzLean
open SizzLean.Repr

/-- Consensus-spec-shaped `Validator`: 8 fixed-size fields,
~144 bytes serialised, depth-4 SSZ tree. -/
structure ValidatorShape where
  pubkey                       : Vector UInt8 48
  withdrawalCredentials        : Vector UInt8 32
  effectiveBalance             : UInt64
  slashed                      : Bool
  activationEligibilityEpoch   : UInt64
  activationEpoch              : UInt64
  exitEpoch                    : UInt64
  withdrawableEpoch            : UInt64
deriving Inhabited, SSZRepr

/-- 16-validator vector, exercising a depth-8 SSZ tree. -/
structure ValidatorSet16 where
  validators : Vector ValidatorShape 16
deriving Inhabited, SSZRepr

/-- 256-validator vector, depth-12 SSZ tree, ~36 KB serialised.
The first "large" tier. The cache's spine-walking and Thunk
memoisation wins compound here because every operation either
walks ~12 tree levels (set/root-fill) or skips ~4 K already-
hashed pairs (cached root). -/
structure ValidatorSet256 where
  validators : Vector ValidatorShape 256
deriving Inhabited, SSZRepr

/-- 4096-validator vector, depth-16 SSZ tree, ~580 KB
serialised. The "huge" tier; used in the deepest cold-root
row to verify scaling. Cold root pays ~65 K pair hashes, the
fixture with the largest amortised batch on which a SIMD
SHA-256 path could act. -/
structure ValidatorSet4096 where
  validators : Vector ValidatorShape 4096
deriving Inhabited, SSZRepr

/-- Build a `ValidatorShape` whose bytes vary with `salt`. The
`pubkey` and `withdrawalCredentials` vectors are salt-stamped;
the `effectiveBalance` and epoch fields incorporate the salt as
a numeric delta. The result is distinct for every salt value,
defeating constant-folding in bench loops. -/
def mkValidator (salt : UInt8) : ValidatorShape :=
  { pubkey                     := Vector.replicate 48 (salt + 0xa0)
    withdrawalCredentials      := Vector.replicate 32 (salt + 0xc0)
    effectiveBalance           := 32000000000 + salt.toUInt64
    slashed                    := false
    activationEligibilityEpoch := 100 + salt.toUInt64
    activationEpoch            := 200 + salt.toUInt64
    exitEpoch                  := 18446744073709551615
    withdrawableEpoch          := 18446744073709551615 }

/-- Build a `ValidatorSet16` whose 16 validators are individually
salt-derived. -/
def mkValidatorSet (salt : UInt8) : ValidatorSet16 :=
  { validators := Vector.ofFn fun (i : Fin 16) =>
      mkValidator (salt + UInt8.ofNat i.val) }

/-- Build a `ValidatorSet256` whose 256 validators are individually
salt-derived. The `UInt8` wraps mod 256, so neighbouring slots
get neighbouring salt values, fine for our anti-constant-folding
purpose. -/
def mkValidatorSet256 (salt : UInt8) : ValidatorSet256 :=
  { validators := Vector.ofFn fun (i : Fin 256) =>
      mkValidator (salt + UInt8.ofNat i.val) }

/-- Build a `ValidatorSet4096`, same pattern; the `Fin 4096`
index wraps `UInt8` 16 times across the vector. Identical
validators across wrap boundaries don't matter for the bench
because the deriving-driven `SSZRepr` walks every element. -/
def mkValidatorSet4096 (salt : UInt8) : ValidatorSet4096 :=
  { validators := Vector.ofFn fun (i : Fin 4096) =>
      mkValidator (salt + UInt8.ofNat i.val) }

/-- Consume a `ByteArray` into a `Nat` sink. Used by every
bench shot to defeat dead-code elimination on the
computed digest / serialised bytes. The compiler can't elide
a chain of `IO.Ref.modify` calls that fold the bytes into a
running sum. -/
def consume (b : ByteArray) : Nat :=
  b.foldl (init := 0) fun acc x => acc + x.toNat

end SizzLeanBench.Fixtures
