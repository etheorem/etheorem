#!/usr/bin/env python3
"""Run the SizzLean comparative benchmark and write the results as markdown.

One command does everything: it builds SizzLean's harness, downloads and
compiles the two comparables at pinned revisions, emits the shared fixture,
runs the three harnesses, checks that they agree on the roots, and renders
the report.

    just sizzlean-comp-benchmark
    python3 scripts/comparative_benchmark.py --reps 5 --output report.md

## What is compared

| Harness | Library | Configuration |
|---|---|---|
| `sizzlean-fast` | `packages/SizzLean` | `SSZ.FastBox`, the cached path, FFI SHA-256 |
| `sizzlean-pure` | `packages/SizzLean` | `SSZ.PureBox`, no cache, FFI SHA-256 |
| `libssz` | `lambdaclass/libssz` | `--release` with thin LTO, no cache |
| `ssz-specs` | `ethereum/ssz-specs` | CPython, root memo on |

## What is measured

One `BeaconState` of about 2.9 MB, in five phases: deserialize the wire
bytes, wrap the value (SizzLean only), root it, write to it, root it again.
The first three make one cold path from bytes to a root, reported in its own
table so that an implementation which hashes during decode is not credited
with a cheap root. The last two make the warm path, and the two scenarios
differ only in the write count, one field against a thousand.
`scripts/compbench/README.md` states the fixture and the scenarios in full.

## The control

All three harnesses print the two roots they computed. The driver refuses to
render a report unless every harness agrees on both, which is the evidence
that the three container declarations describe the same value.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import statistics
import subprocess
import sys
import time
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

# ── Pins ─────────────────────────────────────────────────────────────────
#
# Both comparables are fetched at an exact revision, so two runs a month
# apart measure the same code. `LIBSSZ_REV` is repeated in
# `scripts/compbench/libssz-harness/Cargo.toml`; cargo reads it from there,
# and the check below refuses to run when the two drift apart.

LIBSSZ_REPO = "https://github.com/lambdaclass/libssz"
LIBSSZ_REV = "36802dd1d3e3a83d95d2ac552647539cbe3f7fd7"

SSZ_SPECS_REPO = "https://github.com/ethereum/ssz-specs"
SSZ_SPECS_REV = "2600c0e75a3f296ef2fa4d2d60ea3a69ddc0923e"

# ── Layout ───────────────────────────────────────────────────────────────

REPO_ROOT = Path(__file__).resolve().parent.parent
COMPBENCH_DIR = REPO_ROOT / "scripts" / "compbench"
RUST_HARNESS_DIR = COMPBENCH_DIR / "libssz-harness"
PYTHON_HARNESS = COMPBENCH_DIR / "ssz_specs_harness.py"
LEAN_EXE = REPO_ROOT / "packages" / "SizzLean" / ".lake" / "build" / "bin" / "ssz_compbench"

DEFAULT_WORK_DIR = Path.home() / ".cache" / "sizzlean" / "compbench"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "packages" / "SizzLean" / "bench"

#: The order rows appear in every table.
IMPLS = ["sizzlean-fast", "sizzlean-pure", "libssz", "ssz-specs"]

#: How each row is labelled, and what the library does on a second root.
IMPL_LABELS = {
    "sizzlean-fast": ("SizzLean, Fast", "cached, FFI SHA-256"),
    "sizzlean-pure": ("SizzLean, Pure", "no cache, FFI SHA-256"),
    "libssz": ("libssz", "no cache"),
    "ssz-specs": ("ssz-specs", "root memo, CPython"),
}

SCENARIOS = ["update1", "update1000"]

SCENARIO_TITLES = {
    "update1": "Scenario 1: one write",
    "update1000": "Scenario 2: a thousand writes",
}

SCENARIO_BLURBS = {
    "update1": "Bump `slot` by one, then root again.",
    "update1000": (
        "Write 1000 fields, then root again. The writes are spread over four "
        "shapes: 250 validator records, 250 packed balances, 250 "
        "`block_roots` entries, and 250 `randao_mixes` entries. Spreading "
        "them matters, because a thousand writes into one list would share "
        "most of their Merkle path."
    ),
}

#: The cold path: bytes to a first root. These phases do not depend on the
#: scenario, so their samples are pooled across both.
COLD_PHASES = ["deser_ns", "wrap_ns", "root1_ns"]

#: The warm path: what a slot costs once the value is resident.
WARM_PHASES = ["update_ns", "root2_ns"]

ALL_PHASES = COLD_PHASES + WARM_PHASES


# ── Running things ───────────────────────────────────────────────────────


class BenchmarkError(RuntimeError):
    """A step failed in a way that makes the report meaningless."""


def announce(message: str) -> None:
    """Progress goes to stderr, so a redirected stdout stays clean."""
    print(f"[compbench] {message}", file=sys.stderr, flush=True)


def run(
    cmd: Sequence[str | Path | int],
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> str:
    """Run a command, echo its stderr, and return its stdout.

    A non-zero exit ends the run: every step here produces an input the
    report depends on, so there is nothing useful to carry on with.
    """
    announce("$ " + " ".join(str(part) for part in cmd))
    result = subprocess.run(
        [str(part) for part in cmd],
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
    )
    if result.stderr:
        print(result.stderr, file=sys.stderr, end="", flush=True)
    if result.returncode != 0:
        raise BenchmarkError(f"command failed with code {result.returncode}: {cmd[0]}")
    return result.stdout


def require_tool(name: str, hint: str) -> str:
    """Resolve a build tool, or say which one is missing and how to get it."""
    found = shutil.which(name)
    if found is None:
        raise BenchmarkError(f"{name} is not on PATH. {hint}")
    return found


def check_cargo_pin() -> None:
    """Refuse to run when the Cargo pin and `LIBSSZ_REV` disagree.

    Cargo reads the revision from its own manifest, so a stale constant here
    would put the wrong revision in the report while measuring another.
    """
    manifest = (RUST_HARNESS_DIR / "Cargo.toml").read_text()
    if LIBSSZ_REV not in manifest:
        raise BenchmarkError(
            f"LIBSSZ_REV ({LIBSSZ_REV[:12]}) does not appear in "
            f"{RUST_HARNESS_DIR / 'Cargo.toml'}. Bump both together."
        )


# ── Build steps ──────────────────────────────────────────────────────────


def build_sizzlean() -> None:
    """Compile the Lean harness."""
    require_tool("lake", "Install the Lean toolchain with elan.")
    run(["lake", "build", "ssz_compbench"], cwd=REPO_ROOT)
    if not LEAN_EXE.exists():
        raise BenchmarkError(f"lake reported success but {LEAN_EXE} is missing")


def build_libssz() -> None:
    """Download and compile libssz at the pinned revision, with the harness.

    Cargo does the download: the harness manifest names the repository and
    the revision, so `cargo build` fetches, pins, and compiles in one step.
    """
    require_tool("cargo", "Install Rust with rustup.")
    check_cargo_pin()
    run(["cargo", "build", "--release"], cwd=RUST_HARNESS_DIR)


def build_ssz_specs(work_dir: Path) -> Path:
    """Install ssz-specs at the pinned revision into a private venv.

    Returns the interpreter that has it. `uv` is used when present because
    it resolves and installs in about a second; `python3 -m venv` plus pip is
    the fallback, and installs the same pinned revision.
    """
    venv = work_dir / "ssz-specs-venv"
    interpreter = venv / "bin" / "python"
    requirement = f"eth-ssz-specs @ git+{SSZ_SPECS_REPO}@{SSZ_SPECS_REV}"

    uv = shutil.which("uv")
    if uv is not None:
        run([uv, "venv", venv])
        env = dict(os.environ, VIRTUAL_ENV=str(venv))
        run([uv, "pip", "install", requirement], env=env)
    else:
        run([sys.executable, "-m", "venv", str(venv)])
        run([str(interpreter), "-m", "pip", "install", "--quiet", "--upgrade", "pip"])
        run([str(interpreter), "-m", "pip", "install", "--quiet", requirement])

    if not interpreter.exists():
        raise BenchmarkError(f"the venv build produced no interpreter at {interpreter}")
    return interpreter


# ── The fixture ──────────────────────────────────────────────────────────


@dataclass
class Fixture:
    """The shared state, and what the Lean side said about it."""

    path: Path
    size: int
    root: str


def emit_fixture(work_dir: Path) -> Fixture:
    """Have the Lean harness write the shared `BeaconState`.

    One side has to own the bytes, and SizzLean is the side with a fixture
    builder. The other two decode what it writes, which is what makes the
    root comparison meaningful.
    """
    path = work_dir / "beacon_state.ssz"
    result = subprocess.run(
        [str(LEAN_EXE), "emit", str(path)],
        capture_output=True,
        text=True,
    )
    print(result.stderr, file=sys.stderr, end="", flush=True)
    if result.returncode != 0:
        raise BenchmarkError("the Lean harness could not emit the fixture")

    root = ""
    for line in result.stderr.splitlines():
        if line.startswith("fixture root:"):
            root = line.split(":", 1)[1].strip()
    return Fixture(path=path, size=path.stat().st_size, root=root)


# ── Measurement ──────────────────────────────────────────────────────────


def parse_lines(stdout: str) -> list[dict]:
    """Read a harness's JSON lines, ignoring anything that is not one."""
    rows = []
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        rows.append(json.loads(line))
    return rows


def measure(fixture: Fixture, reps: int, python_reps: int, interpreter: Path) -> list[dict]:
    """Run the three harnesses and collect every sample."""
    rows: list[dict] = []

    announce(f"running the SizzLean harness, {reps} repetitions")
    rows += parse_lines(run([LEAN_EXE, "run", fixture.path, reps]))

    announce(f"running the libssz harness, {reps} repetitions")
    rust_exe = RUST_HARNESS_DIR / "target" / "release" / "libssz-compbench"
    rows += parse_lines(run([rust_exe, fixture.path, reps]))

    announce(f"running the ssz-specs harness, {python_reps} repetitions")
    rows += parse_lines(run([interpreter, PYTHON_HARNESS, fixture.path, python_reps]))

    return rows


def medians(rows: list[dict]) -> dict[tuple[str, str], dict[str, float]]:
    """Median nanoseconds per implementation, scenario, and phase.

    The median rather than the mean: one repetition can catch a page fault
    or a scheduler slice, and the median ignores it without discarding the
    sample.
    """
    grouped: dict[tuple[str, str], dict[str, float]] = {}
    for impl in IMPLS:
        for scenario in SCENARIOS:
            samples = [r for r in rows if r["impl"] == impl and r["scenario"] == scenario]
            if not samples:
                continue
            grouped[(impl, scenario)] = {
                key: statistics.median(float(s[key]) for s in samples)
                for key in ALL_PHASES
            }
    return grouped


def check_roots(rows: list[dict], fixture: Fixture) -> dict[str, str]:
    """Check that every harness produced the same two roots.

    A report over three libraries that rooted three different values would
    compare nothing, so a mismatch ends the run rather than landing in the
    markdown as a footnote.
    """
    for scenario in SCENARIOS:
        for key in ("root1", "root2"):
            seen = {r["impl"]: r[key] for r in rows if r["scenario"] == scenario}
            distinct = set(seen.values())
            if len(distinct) > 1:
                detail = ", ".join(f"{impl}={root}" for impl, root in sorted(seen.items()))
                raise BenchmarkError(
                    f"the harnesses disagree on {scenario}/{key}: {detail}"
                )

    roots = {}
    for scenario in SCENARIOS:
        for key in ("root1", "root2"):
            for row in rows:
                if row["scenario"] == scenario:
                    roots[f"{scenario}/{key}"] = row[key]
                    break

    first_root = roots.get("update1/root1")
    if fixture.root and first_root and fixture.root != first_root:
        raise BenchmarkError(
            f"the emitted fixture roots to {fixture.root} but the harnesses "
            f"report {first_root}"
        )
    return roots


# ── Rendering ────────────────────────────────────────────────────────────


def show_ns(value: float | None) -> str:
    """One duration, in the unit that reads without counting zeros."""
    if value is None:
        return "n/a"
    if value < 1_000:
        return f"{value:.0f} ns"
    if value < 1_000_000:
        return f"{value / 1_000:.1f} µs"
    if value < 1_000_000_000:
        return f"{value / 1_000_000:.1f} ms"
    return f"{value / 1_000_000_000:.2f} s"


def show_ratio(value: float, baseline: float) -> str:
    """How `value` compares with the baseline, as a multiple."""
    if baseline <= 0:
        return "n/a"
    ratio = value / baseline
    if ratio >= 100:
        return f"{ratio:.0f}×"
    if ratio >= 10:
        return f"{ratio:.1f}×"
    return f"{ratio:.2f}×"


def machine_description() -> str:
    """One line naming the machine, so two reports can be told apart."""
    cpu = platform.processor() or platform.machine()
    try:
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                cpu = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    cores = os.cpu_count() or 0
    return f"{cpu}, {cores} threads, {platform.system()} {platform.release()}"


def toolchain_versions(interpreter: Path) -> dict[str, str]:
    """The compilers the numbers came out of."""
    def first_line(cmd: Sequence[str]) -> str:
        try:
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            return out.stdout.strip().splitlines()[0] if out.stdout.strip() else "unknown"
        except (OSError, subprocess.SubprocessError, IndexError):
            return "unknown"

    return {
        "Lean": (REPO_ROOT / "lean-toolchain").read_text().strip(),
        "Rust": first_line(["rustc", "--version"]),
        "Python": first_line([str(interpreter), "--version"]),
    }


def render_scenario_table(
    scenario: str, data: dict[tuple[str, str], dict[str, float]]
) -> list[str]:
    """Every phase of one scenario, with both totals.

    **Bytes to first root** sums the three cold phases. It settles a question
    the first-root column alone would hide: an implementation that hashed
    while it decoded would carry the cost in `Deserialize` and show a cheap
    `First root`, and the sum prices the whole path either way.

    **Writes + second root** sums the two warm phases. It is what a slot
    costs once the value is resident, and the ratio column compares it
    against SizzLean's cached path.
    """
    lines = [
        "| Implementation | Configuration | Deserialize | Wrap | First root |"
        " Bytes to first root | Writes | Second root | Writes + second root |"
        " vs SizzLean Fast |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    baseline = None
    key = ("sizzlean-fast", scenario)
    if key in data:
        baseline = data[key]["update_ns"] + data[key]["root2_ns"]

    for impl in IMPLS:
        row = data.get((impl, scenario))
        if row is None:
            continue
        label, configuration = IMPL_LABELS[impl]
        cold = sum(row[phase] for phase in COLD_PHASES)
        warm = row["update_ns"] + row["root2_ns"]
        # A zero wrap means the library has no wrapping step at all, which a
        # dash says better than "0 ns" does.
        wrap = show_ns(row["wrap_ns"]) if row["wrap_ns"] > 0 else "—"
        ratio = show_ratio(warm, baseline) if baseline else "n/a"
        lines.append(
            f"| {label} | {configuration} | {show_ns(row['deser_ns'])} | {wrap} |"
            f" {show_ns(row['root1_ns'])} | **{show_ns(cold)}** |"
            f" {show_ns(row['update_ns'])} | {show_ns(row['root2_ns'])} |"
            f" **{show_ns(warm)}** | {ratio} |"
        )
    return lines


def render(
    data: dict[tuple[str, str], dict[str, float]],
    roots: dict[str, str],
    fixture: Fixture,
    reps: int,
    python_reps: int,
    versions: dict[str, str],
) -> str:
    """The whole report."""
    lines: list[str] = []
    lines.append("# SizzLean comparative benchmark")
    lines.append("")
    lines.append(
        f"*Generated {time.strftime('%Y-%m-%d %H:%M:%S %Z')} on "
        f"{machine_description()}. Median of {reps} repetitions "
        f"({python_reps} for ssz-specs).*"
    )
    lines.append("")

    lines.append("## What ran")
    lines.append("")
    lines.append("| Library | Revision | Role |")
    lines.append("|---|---|---|")
    lines.append(
        "| `packages/SizzLean` | this checkout | the library under test, in two "
        "configurations |"
    )
    lines.append(
        f"| [`lambdaclass/libssz`]({LIBSSZ_REPO}) | `{LIBSSZ_REV[:12]}` | "
        "Rust, no Merkle cache |"
    )
    lines.append(
        f"| [`ethereum/ssz-specs`]({SSZ_SPECS_REPO}) | `{SSZ_SPECS_REV[:12]}` | "
        "the Python reference implementation, root memo on |"
    )
    lines.append("")
    lines.append("| Toolchain | Version |")
    lines.append("|---|---|")
    for name, version in versions.items():
        lines.append(f"| {name} | `{version}` |")
    lines.append("")

    lines.append("## The fixture")
    lines.append("")
    lines.append(
        f"A Fulu `BeaconState` at the mainnet preset, 37 fields, 1024 validators, "
        f"**{fixture.size:,} bytes** on the wire. Every collection carries distinct "
        "values, so no implementation gains from a repeated subtree. The Lean "
        "harness emits the bytes; the other two decode them."
    )
    lines.append("")
    lines.append("Each run has five phases:")
    lines.append("")
    lines.append("1. **Deserialize**: wire bytes to a plain value.")
    lines.append(
        "2. **Wrap**: that value to whatever the library roots. Only SizzLean "
        "has this step; the other two root the decoded value directly."
    )
    lines.append("3. **First root**: merkleize, from cold.")
    lines.append("4. **Writes**: the scenario's field writes.")
    lines.append("5. **Second root**: merkleize again.")
    lines.append("")
    lines.append(
        "Every repetition decodes the buffer again, so no cache survives from "
        "one repetition into the next."
    )
    lines.append("")
    lines.append(
        "The two scenarios below differ only in the writes. Every other phase "
        "is the same work, so the two tables report it twice and the numbers "
        "should agree to within the run's noise."
    )
    lines.append("")

    lines.append("## The control: the roots agree")
    lines.append("")
    lines.append(
        "All four harnesses produced the same root at every point. That is the "
        "evidence they rooted the same value, so the timings compare like with "
        "like."
    )
    lines.append("")
    lines.append("| Point | Root |")
    lines.append("|---|---|")
    lines.append(f"| The fixture, before any write | `{roots.get('update1/root1', '')}` |")
    lines.append(f"| After the one write | `{roots.get('update1/root2', '')}` |")
    lines.append(f"| After the thousand writes | `{roots.get('update1000/root2', '')}` |")
    lines.append("")

    for scenario in SCENARIOS:
        if not any((impl, scenario) in data for impl in IMPLS):
            continue
        lines.append(f"## {SCENARIO_TITLES[scenario]}")
        lines.append("")
        lines.append(SCENARIO_BLURBS[scenario])
        lines.append("")
        lines += render_scenario_table(scenario, data)
        lines.append("")

    lines.append(
        "Splitting the decode out answers a question the first-root column "
        "alone would hide. An implementation is free to hash while it decodes, "
        "and one that did would show a heavy **Deserialize** and a cheap "
        "**First root**. **Bytes to first root** prices the whole path, so it "
        "holds wherever each library chooses to do the work."
    )
    lines.append("")
    lines.append(
        "**Second root** is where a Merkle cache shows up. A library that keeps "
        "no tree pays the first root's price again; one that keeps a tree "
        "rehashes only the paths the writes changed. Read it with **Writes** "
        "beside it: a cache that makes the second root cheap has to earn back "
        "whatever its writes cost."
    )
    lines.append("")

    lines.append("## Reading the numbers")
    lines.append("")
    lines.append(
        "Two totals carry the report. **Bytes to first root** is what a cold "
        "start costs, from a buffer on disk to a root. **Writes + second root** "
        "is what a slot costs once the value is resident, which is the number a "
        "consensus client reads most often. The phase columns say where each "
        "total comes from."
    )
    lines.append("")
    lines.append(
        "The SizzLean pair isolates the cache and nothing else. Both rows run "
        "the same code through the same FFI SHA-256; only the constructor "
        "differs, `SSZ.FastBox` against `SSZ.PureBox`."
    )
    lines.append("")
    lines.append(
        "libssz has no Merkle cache, so its second root costs what its first "
        "one did. That is its design, and the number should be read as the "
        "price of recomputation rather than as a shortfall."
    )
    lines.append("")
    lines.append(
        "ssz-specs is the specification, written to say what the format is. It "
        "does carry a root memo, so an unchanged subtree is not rehashed."
    )
    lines.append("")
    lines.append(
        "Reproduce with `just sizzlean-comp-benchmark`. "
        "`scripts/compbench/README.md` states the method in full."
    )
    lines.append("")
    return "\n".join(lines)


# ── Entry point ──────────────────────────────────────────────────────────


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run the SizzLean comparative benchmark and write the "
        "results as markdown."
    )
    parser.add_argument(
        "--reps", type=int, default=5, help="repetitions per compiled harness (default 5)"
    )
    parser.add_argument(
        "--python-reps",
        type=int,
        default=3,
        help="repetitions for the ssz-specs harness (default 3)",
    )
    parser.add_argument(
        "--work-dir",
        type=Path,
        default=DEFAULT_WORK_DIR,
        help=f"where the fixture and the venv live (default {DEFAULT_WORK_DIR})",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="where to write the report (default packages/SizzLean/bench/"
        "comparative-<timestamp>.md)",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="reuse what is already built, for a re-measurement",
    )
    args = parser.parse_args()

    args.work_dir.mkdir(parents=True, exist_ok=True)

    try:
        if args.skip_build:
            announce("skipping the build steps")
            interpreter = args.work_dir / "ssz-specs-venv" / "bin" / "python"
            if not interpreter.exists():
                raise BenchmarkError(
                    f"--skip-build needs an existing venv at {interpreter}"
                )
        else:
            announce("building the SizzLean harness")
            build_sizzlean()
            announce(f"building libssz at {LIBSSZ_REV[:12]}")
            build_libssz()
            announce(f"installing ssz-specs at {SSZ_SPECS_REV[:12]}")
            interpreter = build_ssz_specs(args.work_dir)

        announce("emitting the fixture")
        fixture = emit_fixture(args.work_dir)

        rows = measure(fixture, args.reps, args.python_reps, interpreter)
        roots = check_roots(rows, fixture)
        report = render(
            medians(rows),
            roots,
            fixture,
            args.reps,
            args.python_reps,
            toolchain_versions(interpreter),
        )
    except BenchmarkError as error:
        print(f"comparative_benchmark: {error}", file=sys.stderr)
        return 1

    output = args.output
    if output is None:
        DEFAULT_OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
        stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
        output = DEFAULT_OUTPUT_DIR / f"comparative-{stamp}.md"
    output.write_text(report)
    announce(f"wrote {output}")

    print(report)
    return 0


if __name__ == "__main__":
    sys.exit(main())
