"""Decompress one upstream pyspec vector's SSZ blobs for `specs_profile`.

The consensus-spec-tests archives ship every blob snappy-framed
(`*.ssz_snappy`). The Lean profile driver reads raw SSZ, so this script
removes the framing and prints the resulting paths in the order the
driver expects: the pre-state first, then the blocks.

Usage:

    python scripts/prepare_profile_vector.py <case-dir> <out-dir>

`<case-dir>` is an extracted vector directory, e.g.
`~/.cache/sizzlean/v1.7.0-alpha.11-mainnet/tests/mainnet/gloas/sanity/blocks/pyspec_tests/full_random_operations_0`.
Needs `cramjam`, which the pyspec harness venv already carries.
"""

from __future__ import annotations

import sys
from pathlib import Path

import cramjam


def decompress(src: Path, dst_dir: Path) -> Path:
    raw = bytes(cramjam.snappy.decompress_raw(src.read_bytes()))
    dst = dst_dir / src.name.replace(".ssz_snappy", ".ssz")
    dst.write_bytes(raw)
    return dst


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    case_dir, out_dir = Path(argv[1]), Path(argv[2])
    out_dir.mkdir(parents=True, exist_ok=True)

    pre = case_dir / "pre.ssz_snappy"
    if not pre.is_file():
        print(f"no pre.ssz_snappy in {case_dir}", file=sys.stderr)
        return 1

    paths = [decompress(pre, out_dir)]
    # `blocks_0`, `blocks_1`, … in index order: the driver folds them in the
    # order it receives them, and a sorted glob would mis-order a tenth block.
    index = 0
    while (blk := case_dir / f"blocks_{index}.ssz_snappy").is_file():
        paths.append(decompress(blk, out_dir))
        index += 1

    print(" ".join(str(p) for p in paths))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
