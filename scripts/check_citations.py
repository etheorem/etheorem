#!/usr/bin/env python3
"""Check the `File.lean:start-end` citations that point into the spec bodies.

Two documents cite spec declarations by line span: the ledger tables in
`packages/EthCLSpecs/docs/PROOF_LEDGER.md`, and the module
docstrings under `packages/EthCLSpecs/EthCLSpecs/Proofs/`. Nothing checked
them, so they rotted whenever a cited file grew above the declaration. An audit
of the 37 rows in the table once found 16 stale, the worst landing a reader 187
lines from the declaration it named.

Per-PR upkeep does not hold: a proof PR refreshes the rows it touches and
leaves the rest, which mixes fresh and stale spans and removes any rule of
thumb for how much to trust a citation. This checks all of them at once.

The span convention, which the accurate rows already follow: start at the
declaration's own line (`forkdef` / `def` / `abbrev` / `inherit` / ...), end at
the last non-blank line before the next top-level construct. A citation with no
end (`File.lean:458`) pins the start line only.

Usage:
    python3 scripts/check_citations.py           # report, exit 1 on mismatch
    python3 scripts/check_citations.py --fix     # rewrite spans in place
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SPEC_ROOT = REPO / "packages" / "EthCLSpecs" / "EthCLSpecs"
LEDGER = REPO / "packages" / "EthCLSpecs" / "docs" / "PROOF_LEDGER.md"
PROOFS_DIR = SPEC_ROOT / "Proofs"

# A citation: a backticked `Fork/File.lean:12` or `Fork/File.lean:12-34`.
CITATION = re.compile(r"`(?P<path>[A-Za-z0-9_/]+\.lean):(?P<start>\d+)(?:-(?P<end>\d+))?`")

# A backticked identifier, possibly namespace-qualified. Used to recover which
# declaration a citation is about, from the text around it.
IDENTIFIER = re.compile(r"`([A-Za-z_][A-Za-z0-9_.]*)`")

# The keywords that open a top-level construct. A declaration's span ends at the
# last non-blank line before the next one of these. `inherit` is in the list
# because a child fork's replay of a parent declaration is a cited target in its
# own right (`Heze/Operations.lean:46`).
DECL_KEYWORDS = (
    "forkdef", "forkstruct", "forkcontainer", "def", "abbrev", "structure",
    "instance", "theorem", "inherit", "class", "example", "namespace", "end",
    "section", "open", "variable", "import", "deriving", "macro", "syntax",
)
MODIFIERS = ("private", "protected", "partial", "unsafe", "noncomputable", "scoped")

_MOD = r"(?:(?:" + "|".join(MODIFIERS) + r")\s+)*"
_KW = r"(?:" + "|".join(DECL_KEYWORDS) + r")"
DECL_LINE = re.compile(r"^" + _MOD + _KW + r"\b")
# The declaration we are looking for, by name, on its own opening line.
def decl_pattern(name: str) -> re.Pattern[str]:
    return re.compile(r"^" + _MOD + _KW + r"\s+(?:\{[^}]*\}\s*)*" + re.escape(name) + r"\b")


def is_boundary(line: str) -> bool:
    """Whether `line` opens a new top-level construct, ending the span above it."""
    if line.startswith(("/--", "/-!", "@[", "-- ")):
        return True
    return bool(DECL_LINE.match(line))


def actual_span(path: Path, name: str) -> tuple[int, int] | None:
    """The 1-indexed (start, end) of `name`'s declaration in `path`, or None."""
    lines = path.read_text().splitlines()
    pattern = decl_pattern(name)
    start = next((i for i, ln in enumerate(lines) if pattern.match(ln)), None)
    if start is None:
        return None
    end = len(lines) - 1
    for i in range(start + 1, len(lines)):
        if is_boundary(lines[i]):
            end = i - 1
            break
    while end > start and not lines[end].strip():
        end -= 1
    return start + 1, end + 1


class Citation:
    """One `File.lean:span` occurrence, with the declaration name it is about."""

    def __init__(self, source: Path, line_no: int, name: str, match: re.Match[str]):
        self.source = source
        self.line_no = line_no
        self.name = name
        self.path = match.group("path")
        self.start = int(match.group("start"))
        self.end = int(match.group("end")) if match.group("end") else None
        self.text = match.group(0)

    @property
    def target(self) -> Path:
        return SPEC_ROOT / self.path

    def replacement(self, start: int, end: int) -> str:
        span = f"{start}" if self.end is None else f"{start}-{end}"
        return f"`{self.path}:{span}`"


def collect_from_ledger() -> list[Citation]:
    """Citations in the ledger tables. The row's first cell names the function."""
    found = []
    for n, line in enumerate(LEDGER.read_text().splitlines(), start=1):
        if not line.lstrip().startswith("|"):
            continue
        cells = line.split("|")
        names = IDENTIFIER.findall(cells[1]) if len(cells) > 1 else []
        if not names:
            continue
        for m in CITATION.finditer(line):
            found.append(Citation(LEDGER, n, names[0], m))
    return found


def collect_from_proofs() -> list[Citation]:
    """Citations in the `Proofs/` module docstrings.

    The name is the last backticked identifier before the citation on the same
    line, or on the line above when the citation opens a line. A qualified name
    (`EthCLSpecs.Gloas.getPtc`) is reduced to its final component, which is what
    appears on the declaration line.
    """
    found = []
    for path in sorted(PROOFS_DIR.rglob("*.lean")):
        lines = path.read_text().splitlines()
        for n, line in enumerate(lines, start=1):
            for m in CITATION.finditer(line):
                before = line[: m.start()]
                names = IDENTIFIER.findall(before)
                if not names and n > 1:
                    names = IDENTIFIER.findall(lines[n - 2])
                if not names:
                    continue
                found.append(Citation(path, n, names[-1].split(".")[-1], m))
    return found


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fix", action="store_true",
                    help="rewrite stale spans in place instead of only reporting")
    args = ap.parse_args()

    citations = collect_from_ledger() + collect_from_proofs()
    stale: list[tuple[Citation, tuple[int, int]]] = []
    unresolved: list[Citation] = []

    for c in citations:
        if not c.target.exists():
            unresolved.append(c)
            continue
        span = actual_span(c.target, c.name)
        if span is None:
            unresolved.append(c)
            continue
        start, end = span
        if c.start != start or (c.end is not None and c.end != end):
            stale.append((c, span))

    print(f"checked {len(citations)} citations in "
          f"{len({c.source for c in citations})} files")

    for c in unresolved:
        rel = c.source.relative_to(REPO)
        print(f"  UNRESOLVED {rel}:{c.line_no}: no declaration `{c.name}` "
              f"in {c.path}", file=sys.stderr)

    for c, (start, end) in stale:
        rel = c.source.relative_to(REPO)
        cited = c.text.strip("`")
        actual = f"{c.path}:{start}" if c.end is None else f"{c.path}:{start}-{end}"
        print(f"  STALE {rel}:{c.line_no}: `{c.name}` cited {cited}, actual {actual}",
              file=sys.stderr)

    if args.fix and stale:
        # Rewrite per source file, one line at a time. Markdown table alignment
        # is cosmetic and `just lint` does not check it, so a widened span is
        # left as-is rather than re-padding the whole table around it.
        by_source: dict[Path, list[tuple[Citation, tuple[int, int]]]] = {}
        for c, span in stale:
            by_source.setdefault(c.source, []).append((c, span))
        for source, items in by_source.items():
            lines = source.read_text().splitlines(keepends=True)
            for c, (start, end) in items:
                idx = c.line_no - 1
                lines[idx] = lines[idx].replace(c.text, c.replacement(start, end), 1)
            source.write_text("".join(lines))
            print(f"  fixed {len(items)} citation(s) in {source.relative_to(REPO)}")
        return 1 if unresolved else 0

    if stale or unresolved:
        print(f"\n{len(stale)} stale, {len(unresolved)} unresolved. "
              f"Re-run with --fix to rewrite the stale spans.", file=sys.stderr)
        return 1

    print("all citations resolve to their declaration's span")
    return 0


if __name__ == "__main__":
    sys.exit(main())
