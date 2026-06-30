#!/usr/bin/env python3
"""Generate a Lean conformance file from NIST CAVP SHA-256 .rsp vectors.

Reads `cavp/SHA256ShortMsg.rsp` + `cavp/SHA256LongMsg.rsp` (CAVS 11.0
byte-oriented test files, sibling-of-this-script under the
`LeanSha256` package root) and emits `LeanSha256Tests/Nist.lean` —
one `native_decide` example per (Len, Msg, MD) triple, asserting
`LeanSha256.hash msg = md`. The file lives next to the spec it
validates, in the `LeanSha256` library.

FFI conformance to NIST is *not* tested here directly — it follows
by transitivity from:
* this file (spec ≡ NIST on 129 vectors);
* `packages/SizzLean/SizzLeanTests/Sha256Equivalence.lean`
  (FFI ≡ spec on 185 random inputs + 5 NIST §B vectors).

Special case: when `Len = 0`, the `Msg = 00` placeholder is *not*
hashed — the input is the empty `ByteArray`. NIST's file format
always lists a Msg line for grammatical regularity; the Len field
authoritatively determines the input.

Paths resolve relative to this script's location inside the
`LeanSha256` package, so it runs from anywhere:

    python3 packages/LeanSha256/scripts/gen_sha256_cavp.py

The umbrella `Justfile` wraps the invocation as `just leansha256-gen-cavp`.
Regenerate when NIST publishes a refreshed vector set; the output
is otherwise stable and is checked in.
"""

import sys
import re
from pathlib import Path


def parse_rsp(path: Path):
    """Yield (len_bits, msg_hex, md_hex) triples from a NIST CAVP .rsp file."""
    cur = {}
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or line.startswith("["):
                continue
            m = re.match(r"^(\w+)\s*=\s*(.*)$", line)
            if not m:
                continue
            key, val = m.group(1), m.group(2)
            cur[key] = val
            if key == "MD":
                yield (int(cur["Len"]), cur["Msg"], cur["MD"])
                cur = {}


def lean_bytearray_literal(hex_msg: str, len_bits: int) -> str:
    """Render a hex string as a Lean `ByteArray.mk #[ ... ]` literal."""
    if len_bits == 0:
        return "ByteArray.empty"
    # Take exactly len_bits/8 bytes (the .rsp file pads to byte alignment but
    # the Len field is authoritative).
    byte_count = len_bits // 8
    bytes_hex = hex_msg[: byte_count * 2]
    elems = ", ".join(f"0x{bytes_hex[i:i+2]}" for i in range(0, len(bytes_hex), 2))
    return f"ByteArray.mk #[{elems}]"


def lean_md_literal(md_hex: str) -> str:
    """Render the expected 32-byte digest as a Lean `ByteArray.mk #[ ... ]`."""
    assert len(md_hex) == 64, f"expected 32-byte MD, got {len(md_hex)//2}"
    elems = ", ".join(f"0x{md_hex[i:i+2]}" for i in range(0, len(md_hex), 2))
    return f"ByteArray.mk #[{elems}]"


HEADER = """\
import LeanSha256.Core

/-!
# `LeanSha256Tests.Nist` — NIST CAVP byte-oriented SHA-256 vectors

Auto-generated from `cavp/SHA256ShortMsg.rsp` +
`cavp/SHA256LongMsg.rsp` (CAVS 11.0 byte-oriented test files
distributed by NIST's Cryptographic Algorithm Validation Program).
The shabytetestvectors archive lives on csrc.nist.gov; the .rsp
files are committed to this package under `cavp/` and regenerated
via the sibling `scripts/gen_sha256_cavp.py` (umbrella shortcut:
`just leansha256-gen-cavp`).

This file lives in the `LeanSha256` library — it validates the
SHA-256 *spec* directly against NIST's published vectors,
independently of any FFI / SSZ machinery. Each (Len, Msg, MD)
triple emits one `native_decide` example:

* `LeanSha256.hash <msg> = <MD>` — locks the pure-Lean spec
  against NIST's expected output for that input length.

FFI ≡ NIST follows by transitivity from:

* this file (spec ≡ NIST on 129 vectors);
* `packages/SizzLean/SizzLeanTests/Sha256Equivalence.lean`
  (FFI ≡ spec on randomised inputs + the 5 NIST §B vectors via
  `Sha256Vectors.lean`).

The cross-implementation gate is empirical — a deliberate
single-byte bug in either implementation surfaces in one of the
two files immediately. No FFI-side CAVP file is needed.

This file is checked into the repository to keep CI hermetic
(no network fetch at build time). Regenerate when NIST publishes
a refreshed vector set.

## Out of scope here

Monte Carlo test (`SHA256Monte.rsp`) — the chained 100×1000-hash
test — is *not* included. Native_decide on that workload runs in
roughly 100 × 1000 = 100,000 sequential SHA-256 evaluations at
compile time, which dominates the conformance build cost without
adding qualitatively new coverage. A standalone `lake exe` driver
would be the right vehicle if Monte Carlo coverage becomes
required.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536  -- LongMsg vectors run up to 6400 bytes

namespace LeanSha256Tests.Nist

"""

FOOTER = """

end LeanSha256Tests.Nist
"""


def emit_examples(out_lines: list[str], path: Path, suite_name: str):
    out_lines.append(f"\n/-! ### {suite_name} — from `{path.name}` -/\n")
    count = 0
    for len_bits, msg_hex, md_hex in parse_rsp(path):
        msg_lit = lean_bytearray_literal(msg_hex, len_bits)
        md_lit = lean_md_literal(md_hex)
        # Pull out the literals into `let`s so the asserts read naturally.
        out_lines.append(
            f"\nexample :\n"
            f"  let msg := {msg_lit}\n"
            f"  let md  := {md_lit}\n"
            f"  LeanSha256.hash msg = md := by native_decide\n"
        )
        count += 1
    print(f"  {suite_name}: {count} vectors → emitted.", file=sys.stderr)


def main():
    # `__file__` lives at `packages/LeanSha256/scripts/gen_sha256_cavp.py`,
    # so `parent.parent` is the `LeanSha256` package root.
    pkg = Path(__file__).resolve().parent.parent
    short_path = pkg / "cavp" / "SHA256ShortMsg.rsp"
    long_path = pkg / "cavp" / "SHA256LongMsg.rsp"
    out_path = pkg / "LeanSha256Tests" / "Nist.lean"

    for p in (short_path, long_path):
        if not p.is_file():
            print(f"missing: {p}", file=sys.stderr)
            sys.exit(1)

    out_lines = [HEADER]
    emit_examples(out_lines, short_path, "ShortMsg test (Len 0..512 bits)")
    emit_examples(out_lines, long_path, "LongMsg test (Len 520..51200 bits)")
    out_lines.append(FOOTER)

    out_path.write_text("".join(out_lines))
    print(f"wrote {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
