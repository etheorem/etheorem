#!/usr/bin/env python3
"""Generate the FFI CAVP conformance file from NIST SHA-256 .rsp vectors.

Reads `cavp/SHA256ShortMsg.rsp` + `cavp/SHA256LongMsg.rsp` (CAVS 11.0
byte-oriented test files, sibling-of-this-script under the
`LeanHazmatSha256` package root) and emits
`LeanHazmatSha256Tests/Cavp.lean` — one `native_decide` example per
(Len, Msg, MD) triple, asserting `LeanHazmat.Sha256.sha256Hash msg = md`.

This is the FFI counterpart to `LeanSha256`'s
`scripts/gen_sha256_cavp.py`: that script validates the pure-Lean
*spec* against NIST; this one validates the OpenSSL-backed *FFI shim*
against the very same vectors. The two are deliberately independent
so each package carries its own complete, standalone KAT — the
property (hazmat-docs/ARCHITECTURE.md §3.3 / §11) that lets
`LeanHazmatSha256` split to a mirror repo and validate on its own,
without `LeanSha256` or `SizzLean` in the build.

Special case: when `Len = 0`, the `Msg = 00` placeholder is *not*
hashed — the input is the empty `ByteArray`. NIST's file format
always lists a Msg line for grammatical regularity; the Len field
authoritatively determines the input.

Paths resolve relative to this script's location inside the
`LeanHazmatSha256` package, so it runs from anywhere:

    python3 packages/LeanHazmatSha256/scripts/gen_cavp.py

The umbrella `Justfile` wraps the invocation as `just hazmat-sha256-gen-cavp`.
Regenerate when NIST publishes a refreshed vector set; the output is
otherwise stable and is checked in.
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
import LeanHazmatSha256

/-!
# `LeanHazmatSha256Tests.Cavp` — NIST CAVP byte-oriented SHA-256 vectors (FFI)

Auto-generated from `cavp/SHA256ShortMsg.rsp` +
`cavp/SHA256LongMsg.rsp` (CAVS 11.0 byte-oriented test files
distributed by NIST's Cryptographic Algorithm Validation Program).
The shabytetestvectors archive lives on csrc.nist.gov; the .rsp
files are committed to this package under `cavp/` and regenerated
via the sibling `scripts/gen_cavp.py` (umbrella shortcut:
`just hazmat-sha256-gen-cavp`).

This is the **FFI** CAVP gate: each (Len, Msg, MD) triple emits one
`native_decide` example

* `LeanHazmat.Sha256.sha256Hash <msg> = <MD>`

locking the OpenSSL-backed shim against NIST's expected output for
that input length. It is the empirical evidence behind the trust
assumption in `LeanHazmatSha256/Ffi.lean` — *that the linked OpenSSL
implements NIST FIPS 180-4 SHA-256*. A deliberate single-byte bug in
the shim (truncation, byte order, padding) surfaces here immediately.

It is the FFI sibling of `LeanSha256`'s `LeanSha256Tests.Nist` (which
runs the same vectors against the pure-Lean spec). Keeping a full
copy here — rather than relying on `LeanSha256` transitively — is
what makes this package self-contained and independently
mirror-publishable (hazmat-docs/ARCHITECTURE.md §3.3 / §11).

`native_decide` runs the *compiled FFI call* at proof-check time
(adding one `Lean.ofReduceBool` axiom per case); because the shim is
native code rather than kernel-reduced, this suite is markedly faster
than the pure-Lean spec's equivalent.

This file is checked into the repository to keep CI hermetic (no
network fetch at build time). Regenerate when NIST publishes a
refreshed vector set.

## Out of scope here

Monte Carlo test (`SHA256Monte.rsp`) — the chained 100x1000-hash
test — is *not* included; it adds no qualitatively new coverage over
the byte-oriented vectors. The two-input `sha256Combine` and the
batched `sha256BatchCombine` are covered by the hand-written anchors
in `LeanHazmatSha256Tests/Vectors.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536  -- LongMsg vectors run up to 6400 bytes

namespace LeanHazmatSha256Tests.Cavp

open LeanHazmat.Sha256

"""

FOOTER = """

end LeanHazmatSha256Tests.Cavp
"""


def emit_examples(out_lines: list[str], path: Path, suite_name: str):
    out_lines.append(f"\n/-! ### {suite_name} — from `{path.name}` -/\n")
    count = 0
    for len_bits, msg_hex, md_hex in parse_rsp(path):
        msg_lit = lean_bytearray_literal(msg_hex, len_bits)
        md_lit = lean_md_literal(md_hex)
        out_lines.append(
            f"\nexample :\n"
            f"  let msg := {msg_lit}\n"
            f"  let md  := {md_lit}\n"
            f"  sha256Hash msg = md := by native_decide\n"
        )
        count += 1
    print(f"  {suite_name}: {count} vectors -> emitted.", file=sys.stderr)


def main():
    # `__file__` lives at
    # `packages/LeanHazmatSha256/scripts/gen_cavp.py`, so `parent.parent`
    # is the `LeanHazmatSha256` package root.
    pkg = Path(__file__).resolve().parent.parent
    short_path = pkg / "cavp" / "SHA256ShortMsg.rsp"
    long_path = pkg / "cavp" / "SHA256LongMsg.rsp"
    out_path = pkg / "LeanHazmatSha256Tests" / "Cavp.lean"

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
