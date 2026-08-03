"""SizzLean ssz_generic pyspec harness: archive acquisition, case walking,
shape extraction, and the per-worker `ssz_generic_runner` client.

`ssz_generic` is the fork-agnostic half of the upstream `consensus-specs`
SSZ suite: primitive wire-format vectors (uints, basic vectors, bitvectors,
bitlists, bools, and a fixed set of test-only containers). It addresses shapes by
string identifier, not by any consensus container, so it exercises SizzLean's
`SSZType` universe directly. The runner and this harness therefore live in
SizzLean, not in a fork's spec library.

The Lean side (`ssz_generic_runner`) owns decode / round-trip / root / classify;
this module owns acquisition, the case → shape-prefix mapping, and the
`meta.yaml` root parse. The wire protocol matches `EthCLSpecs.PySpecTests`: one
tab-separated request line per case, one result line back.
"""

from __future__ import annotations

import re
import subprocess
import tarfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, Optional
from urllib.request import urlopen

import cramjam
import yaml

# The pinned release (matches EthCLSpecs.Fulu.Interface.pyspecPinnedVersion and
# the EthCLSpecs harness). `ssz_generic` ships in the `general` archive.
PINNED_VERSION = "v1.7.0-alpha.11"
CACHE_DIR = Path.home() / ".cache" / "sizzlean"
REPO_ROOT = Path(__file__).resolve().parents[3]

# The handlers the runner models. The progressive / stable / compatible forms
# (`basic_progressive_list`, `progressive_bitlist`, `progressive_containers`,
# EIP-7495 / 7916 / 8016) are outside SizzLean's `SSZType` universe and are not
# collected; see `SizzLean/Spec/Type.lean`'s module docstring.
SUPPORTED_HANDLERS = {
    "uints", "basic_vector", "bitvector", "bitlist", "boolean", "containers",
}

# Positive shape-prefix patterns: match the prefix of the case name, the rest is
# a variant suffix (`_zero`, `_random_3`, `_max_one_byte_less`). Prefix matching
# is robust to upstream variant churn. A case that matches nothing (the
# out-of-scope progressive/stable test structs) has shape `None` and xfails.
_SHAPE_PATTERNS = [
    re.compile(r"^(uint_\d+)"),
    re.compile(r"^(bitvec_\d+)"),
    re.compile(r"^(bitlist_\d+)"),
    re.compile(r"^(vec_(?:bool|uint\d+)_\d+)"),
    re.compile(r"^(SingleFieldTestStruct|SmallTestStruct|FixedTestStruct|"
               r"VarTestStruct|ComplexTestStruct|BitsStruct)"),
]


def shape_spec_for_generic(handler: str, case_name: str) -> Optional[str]:
    """Map a `(handler, case_name)` to the shape-prefix string the Lean runner's
    `parseShape` accepts, or `None` when the shape is out of SizzLean's universe."""
    if handler == "boolean":
        # Every boolean case (`true`, `false`, `byte_0x80`, `byte_2`) checks `bool`.
        return "bool"
    if handler == "bitlist" and case_name.startswith("bitlist_no_delimiter"):
        # These invalid cases omit the cap; any cap satisfies "decode must fail".
        return "bitlist_256"
    for pat in _SHAPE_PATTERNS:
        m = pat.match(case_name)
        if m:
            return m.group(1)
    return None


def archive_url(tag: str) -> str:
    return (
        f"https://github.com/ethereum/consensus-specs/releases/"
        f"download/{tag}/general.tar.gz"
    )


def ensure_archive(tag: str) -> Path:
    """Download + extract `general.tar.gz` for `tag` (idempotent). Returns the
    extracted root (the dir holding `tests/`)."""
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    extract_dir = CACHE_DIR / f"{tag}-general"
    if (extract_dir / "tests").is_dir():
        return extract_dir
    tarball = CACHE_DIR / f"{tag}-general.tar.gz"
    if not tarball.exists():
        url = archive_url(tag)
        print(f"  downloading {url} ...", flush=True)
        with urlopen(url) as resp, open(tarball, "wb") as out:
            out.write(resp.read())
    extract_dir.mkdir(parents=True, exist_ok=True)
    with tarfile.open(tarball) as tf:
        tf.extractall(extract_dir)
    return extract_dir


@dataclass
class Case:
    """One `ssz_generic` case located on disk. `shape` is the runner shape-prefix
    (or `None` ⇒ out of SizzLean's universe, xfailed)."""
    fork: str
    handler: str
    kind: str  # "valid" / "invalid"
    case_name: str
    shape: Optional[str]
    path: Path

    @property
    def case_id(self) -> str:
        return f"general/ssz_generic/{self.handler}/{self.kind}/{self.case_name}"


def walk_cases(extract_root: Path, limit: Optional[int] = None) -> Iterator[Case]:
    """Yield each supported-handler `ssz_generic` case under
    `tests/general/<fork>/ssz_generic/<handler>/<valid|invalid>/<case>/`. The same
    primitive case is duplicated across fork dirs, so cases are de-duplicated by
    `(handler, kind, case_name)`, the first fork that provides one wins. With
    `limit`, cap the count per `(handler, kind)` for a fast subset."""
    general = extract_root / "tests" / "general"
    if not general.is_dir():
        return
    seen: set[tuple] = set()
    counts: dict[tuple, int] = {}
    for fork_dir in sorted(p for p in general.iterdir() if p.is_dir()):
        ssz_generic = fork_dir / "ssz_generic"
        if not ssz_generic.is_dir():
            continue
        for handler_dir in sorted(p for p in ssz_generic.iterdir() if p.is_dir()):
            handler = handler_dir.name
            if handler not in SUPPORTED_HANDLERS:
                continue
            for kind in ("valid", "invalid"):
                kind_dir = handler_dir / kind
                if not kind_dir.is_dir():
                    continue
                for case_dir in sorted(p for p in kind_dir.iterdir() if p.is_dir()):
                    dedup = (handler, kind, case_dir.name)
                    if dedup in seen:
                        continue
                    seen.add(dedup)
                    key = (handler, kind)
                    if limit is not None and counts.get(key, 0) >= limit:
                        continue
                    counts[key] = counts.get(key, 0) + 1
                    yield Case(fork_dir.name, handler, kind, case_dir.name,
                               shape_spec_for_generic(handler, case_dir.name), case_dir)


def _decompress_to(tmpdir: Path, src: Path) -> Path:
    """Snappy-decompress an `.ssz_snappy` blob to a temp file; return its path."""
    out = bytes(cramjam.snappy.decompress_raw(src.read_bytes()))
    dst = tmpdir / (src.stem + ".ssz")
    dst.write_bytes(out)
    return dst


def build_request(case: Case, tmpdir: Path) -> str:
    """Decompress the case's SSZ blob and encode the request line. A `valid` case
    sends its expected root (from `meta.yaml`); an `invalid` case sends none. The
    caller only builds a request once the shape is known (a `None`-shape case
    xfails before reaching here)."""
    assert case.shape is not None
    serialized = _decompress_to(tmpdir, case.path / "serialized.ssz_snappy")
    if case.kind == "valid":
        meta = yaml.safe_load((case.path / "meta.yaml").read_text()) or {}
        return "\t".join(["check", case.shape, str(serialized), meta["root"]])
    return "\t".join(["invalid", case.shape, str(serialized)])


@dataclass
class Result:
    passed: bool
    bucket: str
    detail: str


class ServerClient:
    """A long-lived `ssz_generic_runner` subprocess, re-spawned on death. One per
    xdist worker (held by a session-scoped fixture)."""

    def __init__(self, repo_root: Path = REPO_ROOT):
        self.repo_root = repo_root
        self.proc: Optional[subprocess.Popen] = None
        self._spawn()

    def _spawn(self) -> None:
        # Spawn from the umbrella root: its lake-manifest resolves every package
        # (SizzLean's own subpackage manifest is minimal and omits the LeanHazmat
        # FFI deps the runner links transitively).
        self.proc = subprocess.Popen(
            ["lake", "exe", "ssz_generic_runner"],
            cwd=str(self.repo_root),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            text=True, bufsize=1,
        )

    def submit(self, request_line: str) -> Result:
        """Send a request; return the parsed result. Drains any non-protocol
        startup noise before the `pass`/`fail` line, and retries once on a dead or
        desynced server (re-spawning)."""
        for _ in range(2):
            try:
                if self.proc is None or self.proc.poll() is not None:
                    self._spawn()
                assert self.proc is not None and self.proc.stdin is not None and self.proc.stdout is not None
                self.proc.stdin.write(request_line + "\n")
                self.proc.stdin.flush()
                while True:
                    line = self.proc.stdout.readline()
                    if not line:
                        raise BrokenPipeError("server closed stdout")
                    parts = line.rstrip("\n").split("\t")
                    if parts and parts[0] in ("pass", "fail"):
                        return Result(parts[0] == "pass",
                                      parts[1] if len(parts) > 1 else "?",
                                      parts[2] if len(parts) > 2 else "")
                    # Otherwise startup / lake noise on stdout; skip it.
            except (BrokenPipeError, ValueError, OSError):
                self._spawn()
        return Result(False, "bug", "server died; re-spawned and retried, case still failed")

    def close(self) -> None:
        if self.proc and self.proc.stdin:
            try:
                self.proc.stdin.close()
                self.proc.wait(timeout=30)
            except Exception:
                self.proc.kill()
