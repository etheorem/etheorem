#!/usr/bin/env python3
"""Check the `File.lean:start-end` citations that point into the spec bodies.

Two packages cite spec declarations by line span: the ledger tables and the
`Proofs/` module docstrings under `packages/EthCLSpecs/`, and the same pair
under `packages/SizzLean/`. Nothing checked them, so they rotted whenever a
cited file grew above the declaration. An audit of the 37 fork-ledger rows
once found 16 stale, the worst landing a reader 187 lines from the
declaration it named.

Per-PR upkeep does not hold: a proof PR refreshes the rows it touches and
leaves the rest, which mixes fresh and stale spans and removes any rule of
thumb for how much to trust a citation. This checks all of them at once.

The span convention, which the accurate rows already follow: start at the
declaration's own line (`forkdef` / `def` / `inductive` / `axiom` / ...), end
at the last non-blank line before the next top-level construct. A citation
with no end (`File.lean:458`) pins the start line only. A citation resolves
when the declaration it names opens at the cited start line and the cited end
matches that declaration's computed end. The identifier immediately before
the citation names the declaration, in the ledger's cells and in the `Proofs/`
docstrings alike: the name drives the lookup, not only the error message. A
citation with no identifier before it falls back to the start-line check,
which is all the script can do for it.

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

# One target per package: (spec root the cited paths are relative to, the
# package's ledger, the proofs directory whose module docstrings are scanned).
TARGETS = [
    (REPO / "packages/EthCLSpecs/EthCLSpecs",
     REPO / "packages/EthCLSpecs/docs/PROOF_LEDGER.md",
     REPO / "packages/EthCLSpecs/EthCLSpecs/Proofs"),
    (REPO / "packages/SizzLean/SizzLean",
     REPO / "packages/SizzLean/docs/PROOF_LEDGER.md",
     REPO / "packages/SizzLean/SizzLean/Proofs"),
]

# A citation: a backticked `Fork/File.lean:12` or `Fork/File.lean:12-34`.
CITATION = re.compile(r"`(?P<path>[A-Za-z0-9_/]+\.lean):(?P<start>\d+)(?:-(?P<end>\d+))?`")

# A backticked identifier, possibly namespace-qualified. The identifier before
# a citation names the declaration it is about and drives the lookup, in the
# ledger cells and in the `Proofs/` docstrings alike (`Citation.name`), so
# the lookup never rests on the error message alone.
IDENTIFIER = re.compile(r"`([A-Za-z_][A-Za-z0-9_.]*)`")

# The keywords that open a top-level construct. A declaration's span ends at the
# last non-blank line before the next one of these. `inherit` is in the list
# because a child fork's replay of a parent declaration is a cited target in its
# own right (`Heze/Operations.lean:46`). `inductive` and `axiom` are here
# because four SizzLean ledger rows cite them (`SSZType.BasicSupported`,
# `sha256Hash_eq_spec`, ...). `mutual` stays out: a `mutual` line is not a
# declaration, and the checker must find the `inductive` or `theorem` line
# inside the block, which it does.
DECL_KEYWORDS = (
    "forkdef", "forkstruct", "forkcontainer", "def", "abbrev", "structure",
    "instance", "theorem", "inherit", "class", "example", "namespace", "end",
    "section", "open", "variable", "import", "deriving", "macro", "syntax",
    "inductive", "axiom",
)
MODIFIERS = ("private", "protected", "partial", "unsafe", "noncomputable", "scoped")

_MOD = r"(?:(?:" + "|".join(MODIFIERS) + r")\s+)*"
_KW = r"(?:" + "|".join(DECL_KEYWORDS) + r")"
DECL_LINE = re.compile(r"^" + _MOD + _KW + r"\b")


def is_boundary(line: str) -> bool:
    """Whether `line` opens a new top-level construct, ending the span above it."""
    if line.startswith(("/--", "/-!", "@[", "-- ")):
        return True
    return bool(DECL_LINE.match(line))


def decl_pattern(name: str) -> re.Pattern[str]:
    """A declaration line that declares `name`, qualified or not."""
    return re.compile(r"^" + _MOD + _KW + r"\s+(?:.*?\.)?" + re.escape(name) + r"\b")


def actual_span(path: Path, start: int, name: str | None = None,
                ) -> tuple[int, int] | None:
    """The 1-indexed (start, end) of the declaration the citation points at.

    With no `name`, the declaration opening at line `start`; `None` when the
    line is out of range or opens no declaration, the UNRESOLVED case.

    With a `name` (`None` or `"?"` means none was found), the line at `start` must
    declare that name. When it declares something else, the file is searched
    for the first line that does declare it, and that declaration's span comes
    back: the caller sees a start different from the citation's and reports
    STALE. `None` when neither the line at `start` nor the named declaration
    is found.
    """
    lines = path.read_text().splitlines()
    if not 1 <= start <= len(lines):
        return None
    if not name or name == "?":
        # Hint-less citation: the start-line check is all the script can do.
        if not DECL_LINE.match(lines[start - 1]):
            return None
    elif not decl_pattern(name).match(lines[start - 1]):
        # The cited line does not open the named declaration (it may open
        # another one, or nothing at all when the declaration moved past
        # filler). Search the file; None when the name is nowhere.
        hits = [i for i, line in enumerate(lines) if decl_pattern(name).match(line)]
        if not hits:
            return None
        start = hits[0] + 1
    i0 = start - 1
    end = len(lines) - 1
    for i in range(i0 + 1, len(lines)):
        if is_boundary(lines[i]):
            end = i - 1
            break
    while end > i0 and not lines[end].strip():
        end -= 1
    return i0 + 1, end + 1


class Citation:
    """One `File.lean:span` occurrence."""

    def __init__(self, source: Path, root: Path, line_no: int, name: str | None,
                 hint: str, match: re.Match[str]):
        self.source = source
        self.root = root
        self.line_no = line_no
        # The identifier the citation is about, when the surrounding text
        # names one: it drives the lookup. The message falls back to `hint`
        # (the row's cell name) when no identifier sits before the citation.
        # The identifier the citation is about; `None` means hint-less and
        # holds only the start-line check. An empty string must never reach
        # `decl_pattern`, where it would match every declaration line.
        self.name = (name or hint) if (name or hint) and (name or hint) != "?" else None
        self.hint = hint
        self.path = match.group("path")
        self.start = int(match.group("start"))
        self.end = int(match.group("end")) if match.group("end") else None
        self.text = match.group(0)

    @property
    def target(self) -> Path:
        return self.root / self.path

    def replacement(self, start: int, end: int) -> str:
        span = f"{start}" if self.end is None else f"{start}-{end}"
        return f"`{self.path}:{span}`"


def name_before(text: str, pos: int, fallback: str | None) -> str | None:
    """The last backticked identifier before `text[:pos]`, else `fallback`."""
    names = IDENTIFIER.findall(text[:pos])
    return names[-1].split(".")[-1] if names else fallback


def collect_from_ledger(ledger: Path, root: Path) -> list[Citation]:
    """Citations in a package's ledger, table rows and prose alike.

    A markdown row cites its declaration twice over: the Location cell holds
    the span the row is about, and the Property cell can cite further
    supporting spans. The identifier immediately before a citation names it
    when the cell supplies one; a citation that opens its cell is the row's
    own span, and the row's first cell names it. A citation in a prose
    paragraph resolves the same way `collect_from_proofs` resolves one: the
    last backticked identifier before it. Scanning prose keeps the
    supporting-span citations honest; stale ones hide in prose
    exactly when prose goes unscanned.
    """
    all_lines = ledger.read_text().splitlines()
    found = []
    for n, line in enumerate(all_lines, start=1):
        if not line.lstrip().startswith("|"):
            for m in CITATION.finditer(line):
                names = IDENTIFIER.findall(line[: m.start()])
                if not names and n > 1:
                    # the identifier may sit on the line above, the same
                    # fallback the `Proofs/` docstring scan uses
                    names = IDENTIFIER.findall(all_lines[n - 2])
                name = names[-1].split(".")[-1] if names else None
                hint = name if name else "?"
                found.append(Citation(ledger, root, n, name, hint, m))
            continue
        cells = line.split("|")
        # The row's own name, from its first cell (`decode_encode` for a
        # matrix row, `cache` for a slug-first row). `None` when the slug
        # carries no identifier, so the fallback can never produce an
        # empty pattern that matches every declaration line.
        row_name = None
        if len(cells) > 1:
            names = IDENTIFIER.findall(cells[1])
            if names:
                row_name = names[0].split(".")[-1]
        for m in CITATION.finditer(line):
            cell_start = line.rfind("|", 0, m.start())
            cell_text = line[cell_start:m.start()]
            names = IDENTIFIER.findall(cell_text)
            name = names[-1].split(".")[-1] if names else None
            hint = name if name else (row_name or "?")
            found.append(Citation(ledger, root, n, name, hint, m))
    return found


def collect_from_proofs(proofs_dir: Path, root: Path) -> list[Citation]:
    """Citations in a package's `Proofs/` module docstrings.

    The name is the last backticked identifier before the citation on the same
    line, or on the line above when the citation opens a line. A qualified
    name (`EthCLSpecs.Gloas.getPtc`) is reduced to its final component, which
    is what appears on the declaration line.
    """
    found = []
    for path in sorted(proofs_dir.rglob("*.lean")):
        lines = path.read_text().splitlines()
        for n, line in enumerate(lines, start=1):
            for m in CITATION.finditer(line):
                before = line[: m.start()]
                names = IDENTIFIER.findall(before)
                if not names and n > 1:
                    names = IDENTIFIER.findall(lines[n - 2])
                name = names[-1].split(".")[-1] if names else None
                hint = name if name else "?"
                found.append(Citation(path, root, n, name, hint, m))
    return found


def collect_all() -> list[Citation]:
    found = []
    for root, ledger, proofs_dir in TARGETS:
        if ledger.exists():
            found += collect_from_ledger(ledger, root)
        if proofs_dir.exists():
            found += collect_from_proofs(proofs_dir, root)
    return found


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fix", action="store_true",
                    help="rewrite stale spans in place instead of only reporting")
    args = ap.parse_args()

    citations = collect_all()
    stale: list[tuple[Citation, tuple[int, int]]] = []
    unresolved: list[Citation] = []

    for c in citations:
        if not c.target.exists():
            unresolved.append(c)
            continue
        span = actual_span(c.target, c.start, c.name)
        if span is None:
            unresolved.append(c)
            continue
        start, end = span
        if start != c.start or (c.end is not None and c.end != end):
            stale.append((c, span))

    print(f"checked {len(citations)} citations in "
          f"{len({c.source for c in citations})} files")

    for c in unresolved:
        rel = c.source.relative_to(REPO)
        print(f"  UNRESOLVED {rel}:{c.line_no}: {c.path}:{c.start} opens no "
              f"declaration (`{c.name}`)", file=sys.stderr)

    for c, (start, end) in stale:
        rel = c.source.relative_to(REPO)
        cited = c.text.strip("`")
        actual = f"{c.path}:{start}-{end}"
        print(f"  STALE {rel}:{c.line_no}: `{c.hint}` cited {cited}, actual {actual}",
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
