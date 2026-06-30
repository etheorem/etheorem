#!/usr/bin/env python3
"""Generate `LeanPoseidon/Poseidon2/Params.lean` — the Poseidon2 instances.

Transcription of Poseidon2's round constants is correctness-critical, so it
is mechanised here rather than hand-typed into the `.lean` file: this script
plus its sibling data files (`poseidon2_<field>.json`) are the single source
of truth, and `Params.lean` is *generated* from them
(`just poseidon-gen-params`). Re-running reproduces `Params.lean`
byte-identically. Any transcription error is caught downstream by the anchor
KATs in `Poseidon2/Permutation.lean` and the differential test in
`LeanPoseidonTests`.

## Instances

One `Params` value is emitted per entry of `INSTANCES` below — each reads a
committed data file (machine-extracted from the HorizenLabs `zkhash` crate
v0.2.0, the pinned reference) and is emitted over its Lean field type:

* `bn254Params : Params Bn254Fr` — from `poseidon2_bn256.json`
  (`POSEIDON2_BN256_PARAMS`, t = 3).
* `bls12Params : Params Bls12Fr` — from `poseidon2_bls12.json`
  (`POSEIDON2_BLS_3_PARAMS`, t = 3) — a *second field*, demonstrating the
  field abstraction (Phase 4): a new instance is new data, not new code.

Each data file's `_provenance` field records its exact origin. This mirrors
how `LeanSha256`'s `gen_sha256_cavp.py` reads committed NIST `.rsp` files;
the generator is hermetic and stdlib-only (no Rust toolchain, no network).

The umbrella `Justfile` wraps this as `just poseidon-gen-params`.
"""

import json
import sys
from pathlib import Path

# (Lean def name, Lean field type, data file) — order fixes emission order.
INSTANCES = [
    ("bn254Params", "Bn254Fr", "poseidon2_bn256.json"),
    ("bls12Params", "Bls12Fr", "poseidon2_bls12.json"),
]

SCRIPT_DIR = Path(__file__).resolve().parent


def load_data(fname):
    with (SCRIPT_DIR / fname).open() as f:
        return json.load(f)


def flatten_round_constants(rc, half_full, partial, t):
    """Flatten the per-round constants into the ARK array the permutation
    reads: beginning full rounds (all `t` entries), then partial rounds
    (entry `[0]` only), then end full rounds (all `t` entries). Length
    `rounds_f·t + rounds_p`."""
    flat = []
    for r in range(half_full):                       # beginning full
        flat += rc[r][:t]
    for r in range(half_full, half_full + partial):  # partial
        flat.append(rc[r][0])
    for r in range(half_full + partial, half_full + partial + half_full):  # end full
        flat += rc[r][:t]
    return flat


def canonical_hex(h, modulus):
    """Normalise a `0x…` constant and assert it is a canonical residue."""
    n = int(h, 16)
    assert 0 <= n < modulus, f"constant out of field range: {h}"
    return f"0x{n:064x}"


HEADER = '''import LeanPoseidon.Field

/-!
# `LeanPoseidon.Poseidon2.Params` — instance data + the pinned constants

**This file is generated** by `scripts/gen_poseidon_params.py` from the
pinned `scripts/poseidon2_*.json` data files (HorizenLabs `zkhash` v0.2.0);
do not edit by hand. Run `just poseidon-gen-params` to regenerate. The
generator header documents the sources and the flattening layout.

## What a Poseidon2 instance is (for the Lean-fluent reader)

A Poseidon2 *permutation* mixes a *state* of `t` field elements through a
sequence of rounds. A *full round* applies the non-linear S-box `x ↦ xᵈ` to
all `t` elements; a *partial round* applies it to one element only (cheaper
— most rounds are partial). *Round constants* (ARK = "add round key") are
added before each S-box layer; between S-box layers a *linear layer* (a
matrix multiply — see `Poseidon2/LinearLayers.lean`) diffuses the state.
Capturing all of this as *data* (rather than hardcoding) follows CLAUDE.md's
"configure, don't integrate" and makes a new instance — even over a new
*field* — new data, not new code (Open/Closed).
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

/-- A Poseidon2 instance captured as data, generic over the coefficient type
`R`. The shipped layers/permutation specialise the *width* to `t = 3`
(`Vector R 3`); the *field* is whatever `R` the instance is built over (the
field abstraction, ARCHITECTURE.md §3). -/
structure Params (R : Type) where
  /-- State width (number of field elements). -/
  t : Nat
  /-- `R_f`: total full rounds, split half before / half after the partial
  rounds. -/
  fullRounds : Nat
  /-- `R_p`: partial rounds (S-box on element 0 only). -/
  partialRounds : Nat
  /-- S-box exponent `d` (= 5 for the shipped instances). -/
  sboxDegree : Nat
  /-- Flattened ARK ("add round key") constants: beginning full rounds (all
  `t` entries each), partial rounds (entry 0 only), end full rounds (all `t`
  entries). For `t = 3` that is `8·3 + 56 = 80`. `Poseidon2/Permutation.lean`
  indexes it with exactly this layout. -/
  roundConstants : Array R
  /-- The internal linear layer's matrix diagonal, length `t`. For the t=3
  instances it is `[2,2,3]`; the dense internal matrix is
  `J + diag(intDiagᵢ − 1)`. See `Poseidon2/LinearLayers.lean`. -/
  intDiag : Array R

'''

FOOTER = '''end LeanPoseidon.Poseidon2
'''


def emit_instance(name, field, data):
    modulus = int(data["modulus"])
    t = data["t"]
    rounds_f = data["rounds_f"]
    rounds_p = data["rounds_p"]
    half = rounds_f // 2
    rc = data[f"rc{t}"]
    diag_m1 = data[f"mat_diag{t}_m_1"]

    assert len(rc) == rounds_f + rounds_p, f"{name}: rc round count mismatch"
    assert len(diag_m1) == t, f"{name}: diagonal length mismatch"
    flat = flatten_round_constants(rc, half, rounds_p, t)
    assert len(flat) == rounds_f * t + rounds_p, f"{name}: flattened length"

    out = []
    out.append(
        f"/-- Pinned BN254/BLS-style Poseidon2 instance `{name}` over `{field}`,\n"
        f"generated from `zkhash` v0.2.0 (see the generator header). `{field}.ofNat`\n"
        f"reduces each literal mod the modulus; every constant is already canonical. -/\n")
    out.append(f"def {name} : Params {field} where\n")
    out.append(f"  t := {t}\n")
    out.append(f"  fullRounds := {rounds_f}\n")
    out.append(f"  partialRounds := {rounds_p}\n")
    out.append(f"  sboxDegree := {data['sbox_degree']}\n")
    out.append("  roundConstants := #[\n")
    out.append(f"    -- beginning full rounds 0..{half-1} ({t} entries each)\n")
    for r in range(half):
        for c in range(t):
            out.append(f"    {field}.ofNat {canonical_hex(rc[r][c], modulus)},\n")
    out.append("    -- partial rounds (entry 0 only)\n")
    for r in range(half, half + rounds_p):
        out.append(f"    {field}.ofNat {canonical_hex(rc[r][0], modulus)},\n")
    out.append(f"    -- end full rounds ({t} entries each)\n")
    end = half + rounds_p
    last = end + half - 1
    for r in range(end, end + half):
        for c in range(t):
            sep = "" if (r == last and c == t - 1) else ","
            out.append(f"    {field}.ofNat {canonical_hex(rc[r][c], modulus)}{sep}\n")
    out.append("  ]\n")
    diag = ", ".join(f"{field}.ofNat {int(d, 16) + 1}" for d in diag_m1)
    out.append(f"  intDiag := #[{diag}]\n\n")

    # Shape gates.
    out.append("/-! ## Shape gates -/\n")
    out.append(f"#guard {name}.t = {t}\n")
    out.append(f"#guard {name}.fullRounds = {rounds_f}\n")
    out.append(f"#guard {name}.partialRounds = {rounds_p}\n")
    out.append(f"#guard {name}.roundConstants.size = {rounds_f * t + rounds_p}\n")
    out.append(f"#guard {name}.intDiag.size = {t}\n\n")
    return "".join(out)


def main():
    out_path = SCRIPT_DIR.parent / "LeanPoseidon" / "Poseidon2" / "Params.lean"
    lines = [HEADER]
    for name, field, fname in INSTANCES:
        lines.append(emit_instance(name, field, load_data(fname)))
    lines.append(FOOTER)
    out_path.write_text("".join(lines))
    print(f"wrote {out_path} ({len(INSTANCES)} instances)", file=sys.stderr)


if __name__ == "__main__":
    main()
