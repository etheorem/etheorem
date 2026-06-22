#!/usr/bin/env python3
"""SizzLean conformance harness — drives the Lean `eth_ssz_vector_runner` CLI against
the `ethereum/consensus-spec-tests` upstream archives.

Usage:
    scripts/run_conformance.py [options]

Default behavior (no flags) runs a SMALL SUBSET (`--limit 5` per suite)
of the per-fork `ssz_static` tests against the dispatch table in
`packages/LeanEthCS/LeanEthCS/Cli/Main.lean`. The full suite is gated behind `--all` —
running it is slow (hundreds of vectors × Lean CLI invocation each)
and not needed for plumbing validation in CI's default path. Per
project memory: "small subset during implementation, full suite on
demand".

Pipeline:
    1. Download the requested `consensus-spec-tests` release tarballs
       (cached under `~/.cache/sizzlean/`).
    2. Extract them into a temp dir (kept across runs for cache hits).
    3. Walk the per-test-case directories. Each case is a directory with
       `value.yaml` (optional), `serialized.ssz_snappy` (the SSZ blob),
       and `roots.yaml` (expected hash_tree_root).
    4. Decompress the snappy blob in memory.
    5. Invoke `lake exe eth_ssz_vector_runner check <fork>:<type> <tempfile>
       <expected_root>` per case. Aggregate pass/fail.
    6. Print a summary; exit non-zero if any case failed.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from dataclasses import dataclass
from fnmatch import fnmatch
from pathlib import Path
from typing import Iterator, List, Optional, Tuple
from urllib.request import urlopen

from tqdm import tqdm

# --- Constants --------------------------------------------------------------

DEFAULT_TAG = "v1.7.0-alpha.10"
DEFAULT_LIMIT = 5
CACHE_DIR = Path.home() / ".cache" / "sizzlean"
REPO_ROOT = Path(__file__).resolve().parent.parent

# `ssz_static` per-fork type identifiers the CLI dispatches today.
# Anything not in this set is reported as `skipped`. Extend the CLI's
# `dispatchRoot`/`dispatchCheck` in `packages/LeanEthCS/LeanEthCS/Cli/Main.lean` to grow
# this list.
# Per-fork dispatch tables. Anything not listed here is reported as
# `skipped` (no Lean type currently wired in). Extend the CLI's
# `dispatchRoot`/`dispatchCheck` in `packages/LeanEthCS/LeanEthCS/Cli/Main.lean` *and* the
# matching entry here to grow the coverage.
_PHASE0_TYPES = {
    "BeaconBlockHeader", "SignedBeaconBlockHeader", "Validator",
    "Fork", "ForkData", "Checkpoint", "Eth1Data", "Eth1Block",
    "SigningData", "AttestationData", "IndexedAttestation",
    "PendingAttestation", "Attestation", "AttesterSlashing",
    "ProposerSlashing", "Deposit", "DepositMessage", "DepositData",
    "VoluntaryExit", "SignedVoluntaryExit", "AggregateAndProof",
    "SignedAggregateAndProof", "BeaconBlockBody", "BeaconBlock",
    "SignedBeaconBlock", "HistoricalBatch", "BeaconState",
}

_ALTAIR_TYPES = _PHASE0_TYPES | {
    # New in Altair
    "SyncAggregate", "SyncCommittee", "SyncCommitteeMessage",
    "SyncCommitteeContribution", "ContributionAndProof",
    "SignedContributionAndProof", "SyncAggregatorSelectionData",
    "LightClientHeader", "LightClientBootstrap", "LightClientUpdate",
    "LightClientFinalityUpdate", "LightClientOptimisticUpdate",
}

_BELLATRIX_TYPES = _ALTAIR_TYPES | {
    # New in Bellatrix (execution-layer merge)
    "ExecutionPayload", "ExecutionPayloadHeader", "PowBlock",
}

_CAPELLA_TYPES = _BELLATRIX_TYPES | {
    # New in Capella (withdrawals + historical summaries)
    "Withdrawal", "BLSToExecutionChange", "SignedBLSToExecutionChange",
    "HistoricalSummary",
}

_DENEB_TYPES = _CAPELLA_TYPES | {
    # New in Deneb (blob-carrying transactions + KZG commitments)
    "BlobIdentifier", "BlobSidecar",
}

_ELECTRA_TYPES = _DENEB_TYPES | {
    # New in Electra (EIP-6110/7002/7251 — pending operations and EL requests)
    "PendingDeposit", "PendingPartialWithdrawal", "PendingConsolidation",
    "DepositRequest", "WithdrawalRequest", "ConsolidationRequest",
    "ExecutionRequests", "SingleAttestation",
}

_FULU_TYPES = _ELECTRA_TYPES | {
    # New in Fulu (PeerDAS data-column sidecars)
    "DataColumnSidecar", "MatrixEntry", "DataColumnsByRootIdentifier",
}

SSZ_STATIC_TYPES_BY_FORK = {
    "phase0":    _PHASE0_TYPES,
    "altair":    _ALTAIR_TYPES,
    "bellatrix": _BELLATRIX_TYPES,
    "capella":   _CAPELLA_TYPES,
    "deneb":     _DENEB_TYPES,
    "electra":   _ELECTRA_TYPES,
    "fulu":      _FULU_TYPES,
}

# Back-compat: the union, used where the per-fork distinction doesn't
# matter (mostly for sanity/logging).
SSZ_STATIC_TYPES = set().union(*SSZ_STATIC_TYPES_BY_FORK.values())

# `ssz_generic` handler identifiers the CLI supports. Each handler
# expects a `<shape_spec>` string parsed by `parseShape` in the CLI.
SSZ_GENERIC_HANDLERS = {
    "uints",
    "basic_vector",
    "bitvector",
    "bitlist",
    "boolean",
    "containers",  # test-only structs — shapes hardcoded in the CLI
}

FORKS = ["phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu"]

# --- Snappy decompression ---------------------------------------------------


def _ensure_snappy():
    """Import `cramjam` or `snappy`; install instruction if neither is
    available. We try `cramjam` first because it ships pure-wheel binaries
    on PyPI and works without a system snappy install."""
    try:
        import cramjam  # noqa: F401
        return ("cramjam", cramjam)
    except ImportError:
        pass
    try:
        import snappy  # noqa: F401
        return ("python-snappy", snappy)
    except ImportError:
        sys.exit(
            "error: need either `cramjam` or `python-snappy` for "
            "`.ssz_snappy` decompression.\n"
            "       pip install cramjam"
        )


def decompress_snappy(blob: bytes, backend) -> bytes:
    """Decompress an `.ssz_snappy` blob. The consensus-spec-tests format
    is *raw* snappy (block format), not the framing format. Both backends
    handle this."""
    name, mod = backend
    if name == "cramjam":
        return bytes(mod.snappy.decompress_raw(blob))
    else:  # python-snappy
        return mod.decompress(blob)


# --- Archive download / extraction ------------------------------------------


def archive_url(tag: str, archive: str) -> str:
    return (
        f"https://github.com/ethereum/consensus-spec-tests/releases/"
        f"download/{tag}/{archive}.tar.gz"
    )


def ensure_archive(tag: str, archive: str, cache_dir: Path) -> Path:
    """Download and extract `<archive>.tar.gz` from the given tag. Returns
    the path to the extracted directory. Idempotent across runs."""
    cache_dir.mkdir(parents=True, exist_ok=True)
    tarball = cache_dir / f"{tag}-{archive}.tar.gz"
    extract_dir = cache_dir / f"{tag}-{archive}"
    if not extract_dir.exists():
        if not tarball.exists():
            url = archive_url(tag, archive)
            print(f"  downloading {url} ...", flush=True)
            with urlopen(url) as resp, open(tarball, "wb") as out:
                shutil.copyfileobj(resp, out)
        print(f"  extracting {tarball.name} ...", flush=True)
        extract_dir.mkdir(parents=True)
        with tarfile.open(tarball, "r:gz") as tf:
            tf.extractall(extract_dir)
    return extract_dir


# --- Test-case walking ------------------------------------------------------


@dataclass
class StaticCase:
    """A single `ssz_static/<type>/<suite>/<case>` test directory."""
    fork: str
    type_name: str
    case_path: Path

    @property
    def label(self) -> str:
        return f"static:{self.fork}:{self.type_name}/{self.case_path.parent.name}/{self.case_path.name}"


@dataclass
class GenericCase:
    """A single `ssz_generic/<handler>/<valid|invalid>/<case>` test directory."""
    handler: str
    is_valid: bool
    case_name: str  # e.g. `uint_64_zero`, `vec_bool_16_max`
    case_path: Path

    @property
    def label(self) -> str:
        kind = "valid" if self.is_valid else "invalid"
        return f"generic:{self.handler}/{kind}/{self.case_name}"


def parse_root_field(path: Path) -> Optional[str]:
    """Extract the `root: '0x...'` value from a `meta.yaml` (ssz_generic)
    or `roots.yaml` (ssz_static). Both use the same one-line YAML shape
    for the root, so a single parser handles both."""
    if not path.exists():
        return None
    for line in path.read_text().splitlines():
        line = line.strip()
        if line.startswith("root:"):
            value = line.split(":", 1)[1].strip()
            value = value.strip("\"'")
            if value.startswith("0x"):
                value = value[2:]
            return value
    return None


def walk_static_cases(extract_root: Path, config: str,
                      fork: str) -> Iterator[StaticCase]:
    """Yield each ssz_static case under `<extract_root>/tests/<config>/<fork>/ssz_static/...`."""
    fork_dir = extract_root / "tests" / config / fork / "ssz_static"
    if not fork_dir.is_dir():
        return
    for type_dir in sorted(fork_dir.iterdir()):
        if not type_dir.is_dir():
            continue
        for suite_dir in sorted(type_dir.iterdir()):
            if not suite_dir.is_dir():
                continue
            for case_dir in sorted(suite_dir.iterdir()):
                if case_dir.is_dir():
                    yield StaticCase(fork=fork, type_name=type_dir.name,
                                     case_path=case_dir)


def walk_generic_cases(extract_root: Path,
                       fork: str) -> Iterator[GenericCase]:
    """Yield each ssz_generic case under
    `<extract_root>/tests/general/<fork>/ssz_generic/<handler>/<valid|invalid>/<case>/`."""
    handler_root = extract_root / "tests" / "general" / fork / "ssz_generic"
    if not handler_root.is_dir():
        return
    for handler_dir in sorted(handler_root.iterdir()):
        if not handler_dir.is_dir():
            continue
        for kind_dir in sorted(handler_dir.iterdir()):
            if kind_dir.name not in ("valid", "invalid"):
                continue
            is_valid = (kind_dir.name == "valid")
            for case_dir in sorted(kind_dir.iterdir()):
                if case_dir.is_dir():
                    yield GenericCase(
                        handler=handler_dir.name,
                        is_valid=is_valid,
                        case_name=case_dir.name,
                        case_path=case_dir,
                    )


# --- ssz_generic case-name → shape-spec parsing ------------------------------

# Container-case prefixes for SSZ forms `SizzLean/Spec/Type.lean` deliberately
# omits — EIP-7495 `ProgressiveContainer` / `StableContainer`, EIP-7916
# `ProgressiveList` / `ProgressiveBitlist`, EIP-8016 `CompatibleUnion`. See
# that file's module docstring for why (no Phase 0 → Gloas consensus type
# uses them). Upstream `consensus-spec-tests` v1.7.0-alpha.10 added test
# vectors for several of these; we classify them as *out of library scope*
# rather than failures so the conformance run stays green when upstream
# extends the corpus beyond what SizzLean's universe covers.
_OUT_OF_SCOPE_CASE_PREFIXES: Tuple[str, ...] = (
    "ProgressiveTestStruct",
    "ProgressiveBitsStruct",
    # `StableContainer` / `ProgressiveList` / `CompatibleUnion` cases would
    # plug in here too if upstream ships them under `ssz_generic/containers`.
)

# Positive shape-prefix patterns. We match the *prefix* of the case name —
# anything after is variant suffix (e.g. `_zero`, `_random_3`,
# `_max_one_byte_less`, `_but_2`). Trying to enumerate variant suffixes
# is fragile (the `consensus-spec-tests` repo regularly adds new ones);
# positive prefix matching is robust to variant churn.
_SHAPE_PATTERNS = [
    re.compile(r"^(uint_\d+)"),
    re.compile(r"^(bitvec_\d+)"),
    re.compile(r"^(bitlist_\d+)"),
    # `vec_<elem>_<size>` where elem is `bool` or `uint<W>`.
    re.compile(r"^(vec_(?:bool|uint\d+)_\d+)"),
    # Test-only container types (consensus-spec-tests
    # `formats/ssz_generic/containers.md`).
    re.compile(r"^(SingleFieldTestStruct|SmallTestStruct|FixedTestStruct|"
               r"VarTestStruct|ComplexTestStruct|BitsStruct)"),
]


def shape_spec_for_generic(handler: str, case_name: str) -> Optional[str]:
    """Map a `ssz_generic` (handler, case_name) pair to the shape spec
    string the Lean CLI's `parseShape` accepts.
    """
    if handler == "boolean":
        # All boolean cases (`true`, `false`, `byte_0x80`, `byte_2`)
        # check the same `bool` shape.
        return "bool"
    # A few invalid-bitlist cases (`bitlist_no_delimiter_empty`,
    # `bitlist_no_delimiter_zero_byte`, `bitlist_no_delimiter_zeroes`)
    # omit the cap from the case name — they test the trailing-delimiter
    # invariant regardless of cap. Pick a representative cap; the
    # invalid-case contract is "deserialize must fail", which a
    # delimiter-less buffer satisfies at any cap.
    if handler == "bitlist" and case_name.startswith("bitlist_no_delimiter"):
        return "bitlist_256"
    for pat in _SHAPE_PATTERNS:
        m = pat.match(case_name)
        if m:
            return m.group(1)
    return None


# --- Dispatch and reporting -------------------------------------------------


@dataclass
class Stats:
    passed: int = 0
    failed: int = 0
    skipped: int = 0
    out_of_scope: int = 0


def _decompressed_tempfile(case_path: Path, snappy_backend) -> Optional[str]:
    """Decompress `serialized.ssz_snappy` from the case dir to a tempfile,
    returning the tempfile path. Returns `None` if the snappy file is
    missing."""
    ssz_path = case_path / "serialized.ssz_snappy"
    if not ssz_path.exists():
        return None
    raw = decompress_snappy(ssz_path.read_bytes(), snappy_backend)
    with tempfile.NamedTemporaryFile(suffix=".ssz", delete=False) as tmp:
        tmp.write(raw)
        return tmp.name


# ---------- Batch protocol ----------------------------------------------
#
# Spawning `eth_ssz_vector_runner` once per case dominated wall-clock time on
# the big sweeps (~100 ms of Lean-runtime startup × tens of thousands of
# cases). The CLI now exposes a `batch` subcommand that reads
# tab-separated requests from stdin, writes one tab-separated response
# per request to stdout, and stays alive until EOF — see the
# protocol description in `Cli/Main.lean`. The harness spawns the
# CLI once for the whole sweep and pumps requests through it, so
# the per-case cost drops to inter-process write + read.


def _prepare_static(tc: StaticCase, config: str, snappy_backend
                    ) -> Tuple[Optional[str], Optional[str]]:
    """Return `(request_line, tmpfile_or_None)` for the case, or
    `(None, error_message)` if the case can't be set up. The tmpfile (when
    present) must be unlinked by the caller after the response is read."""
    expected = parse_root_field(tc.case_path / "roots.yaml")
    if expected is None:
        return (None, "missing or unparseable roots.yaml")
    tmp_path = _decompressed_tempfile(tc.case_path, snappy_backend)
    if tmp_path is None:
        return (None, "missing serialized.ssz_snappy")
    type_id = f"{config}/{tc.fork}:{tc.type_name}"
    return (f"check\t{type_id}\t{tmp_path}\t{expected}", tmp_path)


def _prepare_generic(tc: GenericCase, snappy_backend
                     ) -> Tuple[Optional[str], Optional[str]]:
    shape = shape_spec_for_generic(tc.handler, tc.case_name)
    if shape is None:
        return (None,
                f"shape spec not extractable for {tc.handler}/{tc.case_name}")
    tmp_path = _decompressed_tempfile(tc.case_path, snappy_backend)
    if tmp_path is None:
        return (None, "missing serialized.ssz_snappy")
    if tc.is_valid:
        expected = parse_root_field(tc.case_path / "meta.yaml")
        if expected is None:
            os.unlink(tmp_path)
            return (None, "missing or unparseable meta.yaml")
        line = f"ssz_generic_check\t{shape}\t{tmp_path}\t{expected}"
    else:
        line = f"ssz_generic_invalid\t{shape}\t{tmp_path}"
    return (line, tmp_path)


def _parse_response(resp: str) -> Tuple[bool, str]:
    """Parse a single response line from the CLI. Returns `(ok, message)`.
    The CLI guarantees responses contain no embedded `\\t`/`\\n`/`\\r`,
    so a plain `split('\\t', 1)` recovers the status + payload."""
    if not resp:
        return (False, "empty response (CLI may have crashed)")
    parts = resp.split("\t", 1)
    status = parts[0]
    payload = parts[1] if len(parts) == 2 else ""
    if status == "ok":
        return (True, payload or "ok")
    return (False, payload or "fail (no message)")


class BatchRunner:
    """One long-lived `eth_ssz_vector_runner batch` subprocess. Each
    `submit()` call writes one request line and reads one response,
    so calls remain synchronous from the caller's perspective and a
    `tqdm` bar can advance per case."""

    def __init__(self, repo_root: Path):
        self.proc = subprocess.Popen(
            ["lake", "exe", "eth_ssz_vector_runner", "batch"],
            cwd=repo_root,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, bufsize=1,  # line-buffered
        )

    def submit(self, request_line: str) -> Tuple[bool, str]:
        assert self.proc.stdin is not None and self.proc.stdout is not None
        self.proc.stdin.write(request_line + "\n")
        self.proc.stdin.flush()
        resp = self.proc.stdout.readline()
        if not resp:
            # Process died mid-batch — surface its stderr if any.
            err = ""
            if self.proc.stderr is not None:
                try:
                    err = self.proc.stderr.read() or ""
                except Exception:
                    pass
            raise RuntimeError(
                f"eth_ssz_vector_runner batch process died unexpectedly. "
                f"stderr: {err.strip()!r}"
            )
        return _parse_response(resp.rstrip("\n"))

    def close(self) -> None:
        if self.proc.stdin is not None:
            try:
                self.proc.stdin.close()
            except BrokenPipeError:
                pass
        self.proc.wait(timeout=30)

    def __enter__(self) -> "BatchRunner":
        return self

    def __exit__(self, *_exc) -> None:
        self.close()


def match_include(label: str, patterns: Optional[List[str]]) -> bool:
    if not patterns:
        return True
    return any(fnmatch(label, pat) for pat in patterns)


# --- Case gathering (filter + per-key limit, then realise into a list so the
# total is known up-front and we can drive a progress bar over it) ----------


def gather_generic_cases(
    extract_dir: Path,
    limit: Optional[int],
    include_patterns: Optional[List[str]],
    stats: "Stats",
) -> List[GenericCase]:
    """Walk every ssz_generic case, apply include-filter + handler-supported
    check + per-(handler, valid/invalid) limit, and return the resulting
    list. `stats.skipped` is incremented for cases dropped because the
    handler isn't in `SSZ_GENERIC_HANDLERS` (i.e. the CLI has no
    dispatch for them). `stats.out_of_scope` is incremented for container
    cases whose case-name starts with an `_OUT_OF_SCOPE_CASE_PREFIXES`
    entry — SSZ forms `SizzLean/Spec/Type.lean` deliberately excludes
    (progressive / stable containers, progressive lists, compatible
    unions). Limit-truncated cases are silently dropped since they're
    not really "skipped", just trimmed."""
    out: List[GenericCase] = []
    for fork in FORKS:
        seen: dict[Tuple[str, str], int] = {}
        for tc in walk_generic_cases(extract_dir, fork):
            if not match_include(tc.label, include_patterns):
                continue
            if tc.handler not in SSZ_GENERIC_HANDLERS:
                stats.skipped += 1
                continue
            if tc.case_name.startswith(_OUT_OF_SCOPE_CASE_PREFIXES):
                stats.out_of_scope += 1
                continue
            key = (tc.handler, "valid" if tc.is_valid else "invalid")
            if limit is not None and seen.get(key, 0) >= limit:
                continue
            seen[key] = seen.get(key, 0) + 1
            out.append(tc)
    return out


def gather_static_cases(
    extract_dir: Path,
    config: str,
    limit: Optional[int],
    include_patterns: Optional[List[str]],
    stats: "Stats",
) -> List[StaticCase]:
    """Walk every ssz_static case for the given preset config, applying the
    same filter/limit dance as `gather_generic_cases`. `stats.skipped`
    counts cases whose `type_name` isn't in the fork's dispatch set."""
    out: List[StaticCase] = []
    for fork in FORKS:
        seen: dict[Tuple[str, str], int] = {}
        for tc in walk_static_cases(extract_dir, config, fork):
            if not match_include(tc.label, include_patterns):
                continue
            fork_types = SSZ_STATIC_TYPES_BY_FORK.get(tc.fork, set())
            if tc.type_name not in fork_types:
                stats.skipped += 1
                continue
            key = (tc.type_name, tc.case_path.parent.name)
            if limit is not None and seen.get(key, 0) >= limit:
                continue
            seen[key] = seen.get(key, 0) + 1
            out.append(tc)
    return out


def progress_iter(items, desc: str, verbose: bool):
    """Wrap `items` in a tqdm progress bar (written to stderr so stdout
    redirection stays clean). When `--verbose` is in effect, per-case
    lines would interleave noisily with the bar, so we just yield
    plainly and let those lines provide their own running narrative.

    On a TTY we update at tqdm's default ~10× per second (the bar repaints
    in place via `\\r`); on a non-TTY destination (CI logs, file
    redirection) we slow the updates to one every 30 s so the captured
    output stays scrollable."""
    if verbose or not items:
        yield from items
        return
    is_tty = sys.stderr.isatty()
    kwargs = {
        "desc": desc,
        "unit": "case",
        "file": sys.stderr,
        "dynamic_ncols": True,
        "leave": True,
    }
    if not is_tty:
        kwargs["mininterval"] = 30.0
    yield from tqdm(items, **kwargs)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tag", default=DEFAULT_TAG,
                    help=f"consensus-spec-tests release tag (default: {DEFAULT_TAG})")
    ap.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                    help=f"max cases per <handler>/<suite> (default: {DEFAULT_LIMIT}); "
                         "use --all to disable")
    ap.add_argument("--all", action="store_true",
                    help="disable subset limits; run every vector. Slow.")
    ap.add_argument("--include", default=None,
                    help="comma-separated glob filter on the test label "
                         "(e.g. 'generic:uints/*' or 'static:phase0:BeaconBlockHeader')")
    ap.add_argument("--suite", choices=("generic", "static", "all"),
                    default="generic",
                    help="which suite to run (default: generic)")
    ap.add_argument("--config", default="mainnet", choices=("mainnet", "minimal"),
                    help="ssz_static config (default: mainnet); ignored for generic")
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args()

    limit = None if args.all else args.limit
    include_patterns = args.include.split(",") if args.include else None
    snappy_backend = _ensure_snappy()

    print(f"SizzLean conformance: tag={args.tag} suite={args.suite} "
          f"limit={'all' if limit is None else limit} "
          f"include={include_patterns or 'all'}", flush=True)

    # Build the Lean CLI once up front so we don't pay the cost per case.
    print("building Lean CLI ...", flush=True)
    build = subprocess.run(["lake", "build", "eth_ssz_vector_runner"], cwd=REPO_ROOT)
    if build.returncode != 0:
        print("error: lake build failed", file=sys.stderr)
        return build.returncode

    stats = Stats()
    failed: List[Tuple[str, str]] = []

    with BatchRunner(REPO_ROOT) as runner:

        def run_one(label: str, prep) -> None:
            """Submit one prepared (line, tmp_path) pair to the runner and
            record the outcome. Cleans up the tempfile regardless."""
            req_line, tmp_or_err = prep
            if req_line is None:
                # Setup error — no CLI call needed; tmp_or_err is the message.
                stats.failed += 1
                failed.append((label, tmp_or_err or "setup error"))
                return
            try:
                ok, msg = runner.submit(req_line)
            finally:
                if tmp_or_err is not None:
                    try:
                        os.unlink(tmp_or_err)
                    except FileNotFoundError:
                        pass
            if args.verbose:
                status = "ok" if ok else "FAIL"
                print(f"  [{status}] {label}: {msg}", flush=True)
            if ok:
                stats.passed += 1
            else:
                stats.failed += 1
                failed.append((label, msg))

        # --- ssz_generic ----------------------------------------------------
        if args.suite in ("generic", "all"):
            extract_dir = ensure_archive(args.tag, "general", CACHE_DIR)
            cases_generic = gather_generic_cases(
                extract_dir, limit, include_patterns, stats)
            for tc in progress_iter(cases_generic, "ssz_generic", args.verbose):
                run_one(tc.label, _prepare_generic(tc, snappy_backend))

        # --- ssz_static -----------------------------------------------------
        if args.suite in ("static", "all"):
            extract_dir = ensure_archive(args.tag, args.config, CACHE_DIR)
            cases_static = gather_static_cases(
                extract_dir, args.config, limit, include_patterns, stats)
            label = f"ssz_static/{args.config}"
            for tc in progress_iter(cases_static, label, args.verbose):
                run_one(tc.label, _prepare_static(tc, args.config,
                                                  snappy_backend))

    # Summary
    print()
    print(f"Result: {stats.passed} passed, {stats.failed} failed, "
          f"{stats.skipped} skipped (not in CLI dispatch), "
          f"{stats.out_of_scope} skipped (out of library scope)")
    if failed:
        print("\nFailures (first 15):")
        for label, msg in failed[:15]:
            print(f"  {label}: {msg}")
    return 0 if stats.failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
