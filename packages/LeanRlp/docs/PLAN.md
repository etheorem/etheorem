# LeanRlp: plan

Each stage ends with `lake build` green, no `sorry`, no `partial
def`. This file is the source of truth for the staging; the design
decisions the stages rest on live in
[ARCHITECTURE.md](ARCHITECTURE.md), cited by section.

## Status

Stage 1 is done: the item codec. `Spec.Scalar` (`minimalBE`,
`beNat`, `beDigits`, `lenOfLen`), `Spec.Item` (with `encodedSize`,
`Encodable`, and the hand-written `DecidableEq`), `Spec.Encode`,
`Spec.Error`, and `Spec.Decode` (`decodeHeader`, `decode`,
`decodePrefix`, and the fuel measure `fuelFor`). The decoder's fuel
and header theorems sit in `Proofs/Fuel.lean`, inside the axiom
gate's import set (ARCHITECTURE.md §5). The depth bound is in,
default 1024. The gates of `LeanRlpTests.Known` cover the RLP
specification's examples and the five item-layer non-canonical
inputs of ARCHITECTURE.md §7, each to its `DecodeError` constructor.

`termination_by structural fuel` forces the decoder's recursion
structural, and `beDigits` counts its digits on a structural step
bound: the well-founded forms do not reduce in the kernel, so
gates over them fail under `decide`. The element loop is
tail-recursive on an accumulator, so a long flat list costs no
stack frame per element. `LeanRlpTests.Known` gates that on a flat
list of 10^6 one-byte strings. `native_decide` evaluates the loop
in compiled form, and the gate fails if a toolchain change gives
the loop a frame per element.
The depth bound guards the only remaining decode stack exposure,
the nesting of `decodeItem`. The encoder keeps the spec form:
`encodedSizeList` and `encodeListOf` recurse once per element in a
non-tail position, and encoding the flat list of 10^6 elements
overflows the native stack. Stage 7 owns the rewrite and the
encode-side gate.

The gates run under `decide`. Six of them use `native_decide`:
the five whose kernel evaluation exceeds its heartbeat budget (the
1024-byte string gate, the 300-byte string gate, the
two-length-byte list header gate, and the two depth gates at the
default bound), and the tail-call gate, which exercises the loop
in compiled form. That is the documented fallback of
ARCHITECTURE.md §10. `LeanRlpTests.Known` names them.

The item-layer design decisions:

* `Item.Encodable` bounds list payloads as well as byte strings
  (ARCHITECTURE.md §2.1).
* The decoder carries a fuel measure with a sufficiency lemma, and
  the `outOfFuel` branch is dead for the public entry points. The
  decoder also carries a depth bound, default 1024,
  recorded as a discrepancy against the reference oracle
  (ARCHITECTURE.md §2.1).
* `RlpRepr` carries `wellFormed : shape.WellFormed` as a sixth,
  decidable field. Theorems 7 to 9 state their size and depth
  hypotheses.
* Theorem 6 is unconditional, so `Rlp.canonical` is unconditional.
* The hash entry point lives one layer up; LeanRlp requires no
  other Etheorem package (ARCHITECTURE.md §3).

## Stages

One dependency note before the stages: the shared `Hasher` class
moves from SizzLean into a new `EthCommon` package as consensus-side
work, on a branch in the main worktree because it edits merged
packages. That work gates no stage here. LeanRlp requires nothing
from it (ARCHITECTURE.md §3).

**Stage 0b. Bootstrap.** Done. Exit: `lake build LeanRlp` green.

**Stage 1. Items.** `Scalar`, `Item`, `encode`, `DecodeError`,
`decodeHeader`, `decode`, `decodePrefix`. The fuel measure and its
sufficiency lemma, the depth bound, and a hand-written
`DecidableEq Item`, which does not derive (ARCHITECTURE.md §2.1).
Known-answer gates under `decide`, with `native_decide` as the
fallback. Exit: the five item-layer inputs of ARCHITECTURE.md §7
fail with the right constructor. Done.

**Stage 2. Vectors.** The `rlp_vectors` runner in `Runner/` and the
fetch recipe for RLPTests. The differential script for items. The
random generator stays under the depth bound, or the oracle learns
the `tooDeep` outcome. For an input where an element crosses its
parent's payload, the runner compares accept and reject only: the
element decodes in full before the comparison and can name a reason
from inside itself instead of `listOverrun` (ARCHITECTURE.md §2.1).
Exit: RLPTests at zero failures, 10^5 random cases in agreement.

**Stage 3. Item proofs.** Theorems 1 to 4, theorem 1 under the
`Encodable` and depth hypotheses, plus the
lemma that every decoded item meets both. The scalar lemmas come
first, then the header lemma, then the mutual induction, and the
axiom gate takes each theorem as its proof lands. Exit:
`Proofs/Axioms.lean` gates theorems 1 to 4.

**Stage 4. Schema.** `RlpType` grows its `interp`, `WellFormed`,
`toItem`, `fromItem`, and `SchemaError`. `Decidable WellFormed`
needs a hand-written instance, because the `struct` arm nests
through `List`. Extend the differential script to the typed layer.
Theorem 5 under `WellFormed`, theorem 6 unconditional. The scalar
`leadingZero` gate (the schema row of ARCHITECTURE.md §7). Exit:
the oracle agrees on typed values, and both theorems build.

**Stage 5. User surface.** `RlpRepr` with its `wellFormed` field,
the library instances (the polymorphic ones take `wellFormed` from
their field proofs), the product instance, theorems 7 to 9 under
their size and depth hypotheses, and `deriving RlpRepr`. `example`
blocks show the derive on a withdrawal and a nested record. Exit: a
derived structure gets `Rlp.roundtrip` under its hypotheses, with
no hand-written proof.

**Stage 6. Real shapes, inside the package.** Two gates in
`LeanRlpTests`: fixture blocks decoded and re-encoded byte for
byte, and test structures with the Amsterdam field lists meeting
the Python oracle. Exit: every fixture block round-trips, and the
oracle agrees on the four records.

**Stage 7. Later, on measurement.** A one-buffer encoder with a
size pre-pass, tied to the spec encoder by a proved `@[csimp]`. The
flat-list gate pair closes here: the decode-side tail-call gate of
`LeanRlpTests.Known` gets an encode-side twin, a `native_decide`
gate over the same 10^6-element list. The rewrite covers the size
pre-pass too: `encodedSizeList` recurses once per element in a
non-tail position and overflows the native stack before
`encodeListOf` runs. The `Encoded` wrapper and `Rlp.decodeKeep`
(ARCHITECTURE.md §8). The mirror repository.

Stages 1 to 3 are one unit of work and give a verified item codec.
Stages 4 and 5 are the second unit. Stage 6 needs the fixture files
and nothing else.
