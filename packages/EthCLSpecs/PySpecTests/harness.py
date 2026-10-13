"""EthCLSpecs pyspec harness: archive acquisition, case walking, the
per-worker Lean server client, and request encoding.

The Lean side (`pyspec_server`) owns decode / run / compare / classify; this
module owns acquisition and the `meta.yaml` parse (`FRAMEWORK_ARCHITECTURE.md`
§13.1, §13.3). The wire protocol is the one `EthCLSpecs.PySpecTests.Server` documents:
one tab-separated request line per case, one result line back.

A worker holds one long-lived server (`ServerClient`) and re-spawns it if it
dies, so the in-flight case reports failed rather than hanging the worker.

Blob reads resolve `.ssz_snappy` first and fall back to the raw `.ssz` beside
it, so the theorem-vector generator's rendered tree (raw `.ssz`, no snappy)
runs through the same code path as the upstream archive.
"""

from __future__ import annotations

import os
import subprocess
import tarfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, Optional
from urllib.request import urlopen

import cramjam
import yaml

# The pinned release: the latest consensus-specs release, confirmed to
# carry the Fulu, Gloas, and Heze minimal vectors (matches
# EthCLSpecs.Fulu.Interface.pyspecPinnedVersion).
PINNED_VERSION = "v1.7.0-alpha.11"
CACHE_DIR = Path.home() / ".cache" / "sizzlean"
REPO_ROOT = Path(__file__).resolve().parents[3]

# In-scope (runner, handler-is-path-segment) formats for Fulu, Gloas, and Heze.
# `ssz_static` runs the per-fork consensus-container vectors (decode →
# hash-tree-root → round-trip) against the container types EthCLSpecs declares;
# the fork-agnostic `ssz_generic` primitive vectors live in SizzLean instead.
# `bls`, `kzg`, `light_client`, `merkle_proof`, `networking`, `sync` are out of
# scope (they exercise primitives a dependency owns). `fast_confirmation` (the
# confirmation-rule fork-choice format, minimal-only) is a runner we have not
# implemented yet: deliberately uncollected, a named future work item rather
# than a silent omission.
IN_SCOPE_RUNNERS = {
    "sanity", "finality", "random", "epoch_processing", "operations",
    "rewards", "genesis", "fork", "transition", "fork_choice", "ssz_static",
}

# The `checks` keys `_build_fork_choice_request` recognizes. Most are modeled by
# its emitter chain; `should_override_forkchoice_update` is recognized but
# deliberately emitted as `unsupported` (the case lands todo/xfail).
# KNOWN_CHECK_SUBKEYS below lists, for the nested check objects, the subkeys
# each emitter reads. Keep both sets in lockstep with the emitter chain: a key
# the chain handles but this set omits emits a spurious `unsupported <key>`
# line and silently demotes a fully-checked case to the todo/xfail bucket.
KNOWN_CHECK_KEYS = {
    "get_proposer_head", "should_override_forkchoice_update", "head",
    "payload_timeliness_vote", "payload_data_availability_vote",
    "justified_checkpoint", "finalized_checkpoint", "proposer_boost_root",
    "time", "genesis_time",
}
KNOWN_CHECK_SUBKEYS = {
    "head": {"root", "slot", "payload_status"},
    "payload_timeliness_vote": {"block_root", "votes"},
    "payload_data_availability_vote": {"block_root", "votes"},
    "justified_checkpoint": {"epoch", "root"},
    "finalized_checkpoint": {"epoch", "root"},
}


def archive_url(tag: str, archive: str) -> str:
    return (
        f"https://github.com/ethereum/consensus-specs/releases/"
        f"download/{tag}/{archive}.tar.gz"
    )


def ensure_archive(tag: str, preset: str) -> Path:
    """Download + extract `<preset>.tar.gz` for `tag` (idempotent). Returns the
    extracted root (the dir holding `tests/`)."""
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    extract_dir = CACHE_DIR / f"{tag}-{preset}"
    if (extract_dir / "tests").is_dir():
        return extract_dir
    tarball = CACHE_DIR / f"{tag}-{preset}.tar.gz"
    if not tarball.exists():
        url = archive_url(tag, preset)
        print(f"  downloading {url} ...", flush=True)
        with urlopen(url) as resp, open(tarball, "wb") as out:
            out.write(resp.read())
    extract_dir.mkdir(parents=True, exist_ok=True)
    with tarfile.open(tarball) as tf:
        tf.extractall(extract_dir)
    return extract_dir


@dataclass
class Case:
    """One pyspec case located on disk."""
    preset: str
    fork: str
    runner: str
    handler: str
    suite: str
    name: str
    path: Path

    @property
    def case_id(self) -> str:
        return f"{self.preset}/{self.fork}/{self.runner}/{self.handler}/{self.suite}/{self.name}"


def walk_cases(extract_root: Path, preset: str, fork: str,
               limit_per_handler: Optional[int] = None) -> Iterator[Case]:
    """Yield in-scope cases under `tests/<preset>/<fork>/`. With
    `limit_per_handler`, cap the count per (runner, handler) for a fast subset
    (the small-subset-during-development convention)."""
    fork_dir = extract_root / "tests" / preset / fork
    if not fork_dir.is_dir():
        return
    counts: dict[tuple, int] = {}
    for runner_dir in sorted(p for p in fork_dir.iterdir() if p.is_dir()):
        runner = runner_dir.name
        if runner not in IN_SCOPE_RUNNERS:
            continue
        # Fulu `fork` (Electra->Fulu upgrade) and `transition` (Electra->Fulu
        # boundary) require a full Electra parent fork the library never builds, so
        # they are permanently out of scope: not collected, not counted, not even as
        # xfail. (The Gloas `fork` / `transition` are Fulu->Gloas and the Heze ones
        # Gloas->Heze, both fully in scope.)
        if fork == "fulu" and runner in ("fork", "transition"):
            continue
        for handler_dir in sorted(p for p in runner_dir.iterdir() if p.is_dir()):
            handler = handler_dir.name
            for suite_dir in sorted(p for p in handler_dir.iterdir() if p.is_dir()):
                for case_dir in sorted(p for p in suite_dir.iterdir() if p.is_dir()):
                    key = (runner, handler)
                    if limit_per_handler is not None and counts.get(key, 0) >= limit_per_handler:
                        continue
                    counts[key] = counts.get(key, 0) + 1
                    yield Case(preset, fork, runner, handler, suite_dir.name,
                               case_dir.name, case_dir)


def walk_vector_cases(root: Path, preset: Optional[str] = None,
                      fork: Optional[str] = None) -> Iterator[Case]:
    """Yield cases under the theorem-vector generator's rendered
    `formats/pyspec` tree, laid out as
    `<root>/<fork>/<preset>/<runner>/<handler>/pyspec_tests/<case>/`.

    The rendered tree is already curated: the generator only writes cases in
    scope, so there is no `limit_per_handler` cap and no `IN_SCOPE_RUNNERS`
    filter here. `preset` / `fork`, when given, drop the other forks or
    presets from the walk. The order is fork, preset, runner, handler, then
    sorted case names, all deterministic.
    """
    if not root.is_dir():
        raise FileNotFoundError(f"--vectors root not found: {root}")
    for fork_dir in sorted(p for p in root.iterdir() if p.is_dir()):
        if fork is not None and fork_dir.name != fork:
            continue
        for preset_dir in sorted(p for p in fork_dir.iterdir() if p.is_dir()):
            if preset is not None and preset_dir.name != preset:
                continue
            for runner_dir in sorted(p for p in preset_dir.iterdir() if p.is_dir()):
                for handler_dir in sorted(p for p in runner_dir.iterdir() if p.is_dir()):
                    suite_dir = handler_dir / "pyspec_tests"
                    if not suite_dir.is_dir():
                        continue
                    for case_dir in sorted(p for p in suite_dir.iterdir() if p.is_dir()):
                        yield Case(preset_dir.name, fork_dir.name, runner_dir.name,
                                   handler_dir.name, "pyspec_tests",
                                   case_dir.name, case_dir)


def _decompress_to(tmpdir: Path, src: Path) -> Path:
    """Snappy-decompress an `.ssz_snappy` blob to a temp file; return its path."""
    raw = src.read_bytes()
    out = bytes(cramjam.snappy.decompress_raw(raw))
    dst = tmpdir / (src.stem + ".ssz")
    dst.write_bytes(out)
    return dst


def _resolve_blob(case_dir: Path, name: str) -> Optional[Path]:
    """Locate an SSZ blob by its suffix-less name: `.ssz_snappy` when present,
    otherwise the raw `.ssz` beside it. `None` when neither suffix exists."""
    snappy = case_dir / f"{name}.ssz_snappy"
    if snappy.exists():
        return snappy
    raw = case_dir / f"{name}.ssz"
    if raw.exists():
        return raw
    return None


def _load_blob(tmpdir: Path, src: Path) -> Path:
    """Return a path the Lean server can read the blob's bytes from. The
    helper decompresses an `.ssz_snappy` source to a temp file and passes a
    raw `.ssz` source through (the server reads the bytes from the path
    either way). The passthrough is absolute, so the path survives the
    server's own working directory."""
    if src.suffix == ".ssz_snappy":
        return _decompress_to(tmpdir, src)
    return src.resolve()


def _load_case_blob(tmpdir: Path, case_dir: Path, name: str) -> Path:
    """`_resolve_blob` + `_load_blob` for a required blob; raise when neither
    suffix exists."""
    src = _resolve_blob(case_dir, name)
    if src is None:
        raise FileNotFoundError(
            f"no {name}.ssz_snappy or {name}.ssz under {case_dir}")
    return _load_blob(tmpdir, src)


def parse_meta(case: Case) -> dict:
    meta_path = case.path / "meta.yaml"
    if meta_path.exists():
        return yaml.safe_load(meta_path.read_text()) or {}
    return {}


def _build_fork_choice_request(case: Case, tmpdir: Path) -> str:
    """Encode a `fork_choice` request: the anchor state in `pre`, and an
    `inputs` pair `anchorBlockPath,scriptPath`. The script is one line per
    `steps.yaml` entry, with `block` / `attestation` / `attester_slashing` steps
    referencing resolved SSZ files by path, and `checks` split into one line
    per key. `get_proposer_head` emits a dedicated `get_proposer_head <root>`
    step; `should_override_forkchoice_update` emits `unsupported
    should_override_forkchoice_update`, so that case reports `todo` (an xfail).
    Sibling keys in the same checks entry still emit their own lines. Any key or
    nested subkey we don't model becomes `unsupported <key>`, keeping the xfail
    reason accurate instead of silently dropping the check."""
    anchor_state = _load_case_blob(tmpdir, case.path, "anchor_state")
    anchor_block = _load_case_blob(tmpdir, case.path, "anchor_block")
    steps = yaml.safe_load((case.path / "steps.yaml").read_text())

    def resolve(name: str) -> Path:
        return _load_case_blob(tmpdir, case.path, name)

    lines: list[str] = []
    for s in steps:
        if "tick" in s:
            lines.append(f"tick {int(s['tick'])}")
        elif "block" in s:
            # PeerDAS data-availability columns (EIP-7594): resolve the listed
            # DataColumnSidecar files and pass them as a comma-separated 4th token
            # (`-` when none). The Lean runner verifies them via is_data_available.
            cols = [str(resolve(name)) for name in s.get("columns", [])]
            col_field = ",".join(cols) if cols else "-"
            lines.append(f"block {resolve(s['block'])} {1 if s.get('valid', True) else 0} {col_field}")
        elif "attestation" in s:
            lines.append(f"attestation {resolve(s['attestation'])} {1 if s.get('valid', True) else 0}")
        elif "attester_slashing" in s:
            lines.append(f"attester_slashing {resolve(s['attester_slashing'])} {1 if s.get('valid', True) else 0}")
        elif "execution_payload" in s:
            # Gloas (EIP-7732): a SignedExecutionPayloadEnvelope for on_execution_payload_envelope.
            lines.append(f"execution_payload {resolve(s['execution_payload'])} {1 if s.get('valid', True) else 0}")
        elif "payload_attestation_message" in s:
            lines.append(
                f"payload_attestation_message {resolve(s['payload_attestation_message'])} "
                f"{1 if s.get('valid', True) else 0}")
        elif "checks" in s:
            c = s["checks"]
            if "get_proposer_head" in c:
                lines.append(f"get_proposer_head {c['get_proposer_head']}")
            if "should_override_forkchoice_update" in c:
                lines.append("unsupported should_override_forkchoice_update")
            if "head" in c:
                lines.append(f"head {c['head']['root']} {int(c['head']['slot'])}")
                if "payload_status" in c["head"]:
                    lines.append(f"head_payload_status {int(c['head']['payload_status'])}")
            if "payload_timeliness_vote" in c:
                v = c["payload_timeliness_vote"]
                votes = ",".join("t" if x is True else "f" if x is False else "n" for x in v["votes"])
                lines.append(f"payload_timeliness_vote {v['block_root']} {votes}")
            if "payload_data_availability_vote" in c:
                v = c["payload_data_availability_vote"]
                votes = ",".join("t" if x is True else "f" if x is False else "n" for x in v["votes"])
                lines.append(f"payload_data_availability_vote {v['block_root']} {votes}")
            if "justified_checkpoint" in c:
                lines.append(f"justified {int(c['justified_checkpoint']['epoch'])} {c['justified_checkpoint']['root']}")
            if "finalized_checkpoint" in c:
                lines.append(f"finalized {int(c['finalized_checkpoint']['epoch'])} {c['finalized_checkpoint']['root']}")
            if "proposer_boost_root" in c:
                lines.append(f"boost {c['proposer_boost_root']}")
            if "time" in c:
                lines.append(f"time {int(c['time'])}")
            if "genesis_time" in c:
                lines.append(f"genesis_time {int(c['genesis_time'])}")
            # A check key we don't model (e.g. a future inclusion_list_satisfied) reports as
            # `unsupported <key>`, so the case lands in the `todo`/xfail bucket rather than
            # passing with the check silently dropped. The same guard runs one level down: an
            # unmodeled subkey of a nested check object (e.g. a new field on `head` past
            # root/slot/payload_status) surfaces as `unsupported <key>.<subkey>`, so the
            # unmodeled-key promise covers nested shapes as well as top-level keys. `str(k)`
            # keeps the join total if YAML 1.1 ever parses an unquoted key as a non-string.
            # No alpha.11 vector hits either path.
            unknown = [str(k) for k in c if k not in KNOWN_CHECK_KEYS]
            for parent, known_sub in KNOWN_CHECK_SUBKEYS.items():
                sub = c.get(parent)
                if isinstance(sub, dict):
                    unknown += [f"{parent}.{k}" for k in sub if k not in known_sub]
            if unknown:
                lines.append(f"unsupported {'/'.join(sorted(unknown))}")
        else:
            # An unrecognized step key (e.g. a future on_inclusion_list fork-choice step) reports
            # as `unsupported <key>`, so the case lands `todo`/xfail with an accurate reason rather
            # than silently dropping the step. Drop the auxiliary flags (valid / columns) and sort,
            # so the reason names the step rather than its flags. No alpha.11 vector hits this.
            keys = sorted(str(k) for k in s if k not in ("valid", "columns"))
            lines.append(f"unsupported {'/'.join(keys) or 'unknown-step'}")
    script_path = tmpdir / "fc_script.txt"
    script_path.write_text("\n".join(lines))
    return "\t".join(["fork_choice", case.handler, str(anchor_state), "-", "1", "0", "-",
                      f"{anchor_block},{script_path}"])


def _build_ssz_static_request(case: Case, tmpdir: Path) -> str:
    """Encode an `ssz_static` request: the container type name (the handler path
    segment), the resolved `serialized.ssz` path, and the expected
    hash-tree-root from `roots.yaml`. The Lean server decodes the bytes as that
    fork's container, compares the root, and checks the round-trip re-serialization."""
    serialized = _load_case_blob(tmpdir, case.path, "serialized")
    roots = yaml.safe_load((case.path / "roots.yaml").read_text())
    return "\t".join(["ssz_static", case.handler, str(serialized), roots["root"]])


def build_request(case: Case, tmpdir: Path) -> str:
    """Resolve the case's SSZ blobs (`.ssz_snappy` preferred, the raw `.ssz`
    beside it otherwise) and encode the tab-separated request line the Lean
    server reads. `post` is `-` when the case has no `post` (an invalid
    vector); `inputs` are the `blocks_N` (or the single operation) in order."""
    if case.runner == "fork_choice":
        return _build_fork_choice_request(case, tmpdir)
    if case.runner == "ssz_static":
        return _build_ssz_static_request(case, tmpdir)
    meta = parse_meta(case)
    pre_src = _resolve_blob(case.path, "pre")
    pre = _load_blob(tmpdir, pre_src) if pre_src is not None else None
    post_src = _resolve_blob(case.path, "post")
    post = _load_blob(tmpdir, post_src) if post_src is not None else None

    # Format-specific inputs.
    inputs: list[Path] = []
    # The `blocks_N` blobs, in index order. Both suffixes feed one name set, so
    # a blob present under both resolves through the `.ssz_snappy` preference.
    # The union assumes the stems match: `.ssz_snappy` holds no interior dot,
    # so `Path.stem` strips it whole and the stem equals the `.ssz` file's stem.
    block_names = sorted(
        {p.stem for p in case.path.glob("blocks_*.ssz_snappy")}
        | {p.stem for p in case.path.glob("blocks_*.ssz")},
        key=lambda name: int(name.split("_")[1].split(".")[0]))
    for name in block_names:
        inputs.append(_load_case_blob(tmpdir, case.path, name))
    # operations/* carry a single named operand file (e.g. attestation.ssz);
    # pick each blob that is not pre/post/blocks, preferring `.ssz_snappy`
    # when both suffixes exist.
    if case.runner == "operations":
        operands: dict[str, Path] = {}
        for f in sorted(case.path.glob("*.ssz_snappy")) + sorted(case.path.glob("*.ssz")):
            operands.setdefault(f.stem, f)
        for stem in sorted(operands):
            if stem in ("pre", "post") or stem.startswith("blocks_"):
                continue
            inputs.append(_load_blob(tmpdir, operands[stem]))
    # sanity/slots: `slots.yaml` holds a plain integer slot count. Pass it as
    # big-endian bytes (the driver decodes inputs[0] big-endian into the count).
    if case.runner == "sanity" and case.handler == "slots":
        slots_yaml = case.path / "slots.yaml"
        if slots_yaml.exists():
            n = int(yaml.safe_load(slots_yaml.read_text()))
            count_path = tmpdir / "slots_count.bin"
            count_path.write_bytes(n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big"))
            inputs.append(count_path)
    # rewards/* compare four `Deltas` blobs; pass the expected files in the fixed
    # order the runner returns them: source, target, head, inactivity-penalty.
    if case.runner == "rewards":
        for name in ("source_deltas", "target_deltas", "head_deltas", "inactivity_penalty_deltas"):
            src = _resolve_blob(case.path, name)
            if src is not None:
                inputs.append(_load_blob(tmpdir, src))

    bls_setting = int(meta.get("bls_setting", 1))
    blocks_count = int(meta.get("blocks_count", len(block_names)))
    fork_epoch = meta.get("fork_epoch", None)
    fork_block = meta.get("fork_block", None)
    # operations/execution_payload carries the execution-engine answer in execution.yaml.
    execution_valid = 1
    if case.runner == "operations" and case.handler == "execution_payload":
        ev_path = case.path / "execution.yaml"
        if ev_path.exists():
            ev = yaml.safe_load(ev_path.read_text()) or {}
            execution_valid = 1 if ev.get("execution_valid", True) else 0

    fields = [
        case.runner,
        case.handler,
        str(pre) if pre else "-",
        str(post) if post else "-",
        str(bls_setting),
        str(blocks_count),
        str(fork_epoch) if fork_epoch is not None else "-",
        ",".join(str(p) for p in inputs),
        str(fork_block) if fork_block is not None else "-",
        str(execution_valid),
    ]
    return "\t".join(fields)


@dataclass
class Result:
    passed: bool
    bucket: str
    detail: str


class ServerClient:
    """A long-lived `pyspec_server` subprocess, re-spawned on death. One per
    xdist worker (held by a session-scoped fixture)."""

    def __init__(self, fork: str = "fulu", preset: str = "minimal",
                 repo_root: Path = REPO_ROOT, no_crypto_cache: bool = False):
        self.repo_root = repo_root
        self.fork = fork
        self.preset = preset
        self.no_crypto_cache = no_crypto_cache
        self.proc: Optional[subprocess.Popen] = None
        self._spawn()

    def _spawn(self) -> None:
        # `pyspec_server <fork> <preset>`: selects the fork interface + preset.
        cmd = ["lake", "exe", "pyspec_server", self.fork, self.preset]
        # The server reads ETHCL_DISABLE_CRYPTO_CACHE once at startup; set it to turn
        # the BLS-verify memo off (the plain FFI backend) for cache-on vs cache-off runs.
        # Spawn from the repository root, where Lake and the just recipes run
        # (the root manifest carries the workspace's full require set; the
        # SizzLean harness spawns the same way).
        env = os.environ.copy()
        if self.no_crypto_cache:
            env["ETHCL_DISABLE_CRYPTO_CACHE"] = "1"
        self.proc = subprocess.Popen(
            cmd,
            cwd=str(self.repo_root),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            text=True, bufsize=1, env=env,
        )

    def submit(self, request_line: str) -> Result:
        """Send a request; return the parsed result. Drains any non-protocol startup
        noise (a `lake exe` trace / Lean line) before the tab-separated `pass`/`fail`
        response, and retries once on a dead or desynced server (re-spawning) so a
        transient first-request hiccup under xdist is not a spurious failure."""
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
                    # Otherwise this is startup / lake noise on stdout; skip it.
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
