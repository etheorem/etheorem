#!/usr/bin/env python3
"""Check each spec constant's tier and owning fork against the pinned specs.

Two facts about a constant have to match upstream, and neither is visible from
the Lean source alone:

* **Its tier.** A value under `presets/*.yaml` belongs on the fork's `Preset`
  class, a value under `configs/*.yaml` on its `Config` class, and a value the
  spec lists in a constants table stays a flat literal. Getting this wrong on
  the preset side is a correctness bug rather than an untidiness: a preset value
  can shape an SSZ cap, a flat literal stays right only while the two preset
  files agree, and the day one of them moves it produces a wrong cap, a wrong
  Merkle root, and a green build.
* **Its owning fork.** A constant belongs to the fork that introduces it. Fulu
  is the accumulated base here, so anything from phase 0 through Fulu lives in
  the Fulu tier; a Gloas constant belongs to Gloas and a Heze constant to Heze.

Neither survives a re-pin on its own. Upstream moves a value between tiers, or a
later fork takes over a constant an earlier one owned, and nothing in the build
notices. This is the same class of rot `check_citations.py` covers.

## How the ground truth is built

`--refresh` downloads the pinned specs and rewrites `constant_tiers.json`:

* Every fork's spec markdown, walking headers at *any* depth. The beacon-chain
  documents write `## Constants` and `## Preset`; the fork-choice documents
  write `### Constant`, singular, one level deeper. Matching only the
  beacon-chain shape silently drops every fork-choice constant, which is how an
  earlier pass over this data came back clean while ten entries were misfiled.
* The preset YAMLs, whose file name gives the introducing fork directly.
* The config YAML, for the values no table lists (the fork versions, the slot
  timing parameters). Its `# <Fork>` comments annotate the block that follows,
  and a `# ------` divider ends their reach. A comment that names no fork leaves
  the current attribution alone, so a value under a topical header comes out
  unattributed rather than wrongly attributed to whichever fork was named last.

Attribution from a table always wins over attribution from a YAML. A value with
no fork attribution is still checked for its tier; only the fork check is
skipped, and the summary counts it.

The pinned tag comes from the pyspec harness, so one edit re-pins both.

Usage:
    python3 scripts/check_constant_tiers.py            # check (exit 1 on drift)
    python3 scripts/check_constant_tiers.py --refresh  # re-download, rewrite JSON
"""

import json
import re
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPECS = ROOT / "packages" / "EthCLSpecs" / "EthCLSpecs"
GROUND_TRUTH = Path(__file__).resolve().parent / "constant_tiers.json"
HARNESS = SPECS.parent / "PySpecTests" / "harness.py"

FORKS = ["phase0", "altair", "bellatrix", "capella", "deneb", "electra",
         "fulu", "gloas", "heze"]
# Our Fulu is the accumulated base: it carries phase 0 through Fulu.
ACCUMULATED = set(FORKS[:FORKS.index("fulu") + 1])
OUR_FORKS = ["Fulu", "Gloas", "Heze"]

# Section heading -> the tier a name defined under it belongs to. `Constant` is
# the fork-choice documents' singular spelling.
TIERS = {"constant": "flat", "constants": "flat",
         "preset": "Preset", "configuration": "Config"}

# The documents each fork contributes constants through.
DOCS = ["beacon-chain", "fork-choice", "das-core"]

# Constants upstream defines outside any table, so the attribution method cannot
# place them. Each is placed by reading the spec text, and each is an ordinary
# flat `Const` entry; the reason is recorded so a re-pin can re-check it.
UNTABLED = {
    "G2_POINT_AT_INFINITY":
        "defined in the BLS document, not in a constants table",
    "MAX_RANDOM_VALUE":
        "a local inside Electra's `compute_balance_weighted_selection`",
}


def pinned_version() -> str:
    """The consensus-specs tag, read from the pyspec harness so there is one pin."""
    m = re.search(r'^PINNED_VERSION\s*=\s*"([^"]+)"', HARNESS.read_text(), re.M)
    if not m:
        sys.exit(f"could not read PINNED_VERSION from {HARNESS}")
    return m.group(1)


# --------------------------------------------------------------------------
# Ground truth
# --------------------------------------------------------------------------

def fetch(tag: str, path: str) -> str | None:
    url = f"https://raw.githubusercontent.com/ethereum/consensus-specs/{tag}/{path}"
    try:
        with urllib.request.urlopen(url, timeout=60) as r:
            return r.read().decode()
    except Exception:
        return None


def scan_markdown(text: str, fork: str, source: str, out: dict) -> None:
    """Record every `| \\`NAME\\` |` row under a tier heading, at any depth."""
    tier, depth = None, 0
    for line in text.splitlines():
        h = re.match(r"^(#+)\s+(.+?)\s*$", line)
        if h:
            level, title = len(h.group(1)), h.group(2).strip().lower()
            if title in TIERS:
                tier, depth = TIERS[title], level
            elif tier and level <= depth:
                tier = None          # a sibling or shallower heading ends the section
            continue
        if not tier:
            continue
        m = re.match(r"^\|\s*`([A-Z][A-Z0-9_]*)`\s*\|", line)
        if m:
            out.setdefault(m.group(1), [fork, tier, source])


def refresh() -> None:
    tag = pinned_version()
    print(f"refreshing ground truth from consensus-specs {tag}")
    truth: dict[str, list[str]] = {}

    for fork in FORKS:
        for doc in DOCS:
            text = fetch(tag, f"specs/{fork}/{doc}.md")
            if text:
                scan_markdown(text, fork, f"{fork}/{doc}.md", truth)

    for fork in FORKS:
        text = fetch(tag, f"presets/minimal/{fork}.yaml")
        if not text:
            continue
        for line in text.splitlines():
            m = re.match(r"^([A-Z0-9_]+):", line.split("#")[0].strip())
            if m:
                truth.setdefault(m.group(1), [fork, "Preset", f"presets/{fork}.yaml"])

    # The config YAML annotates blocks with `# <Fork>`; a `# ----` divider ends
    # the annotation's reach, and any other comment leaves it alone.
    text = fetch(tag, "configs/mainnet.yaml") or ""
    cur = None
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("#"):
            body = s.lstrip("#").strip()
            if body.lower() in FORKS:
                cur = body.lower()
            elif set(body) == {"-"}:
                cur = None
            continue
        m = re.match(r"^([A-Z0-9_]+):", s)
        if m:
            truth.setdefault(m.group(1), [cur or "?", "Config", "configs/mainnet.yaml"])

    GROUND_TRUTH.write_text(json.dumps(dict(sorted(truth.items())), indent=1) + "\n")
    print(f"wrote {GROUND_TRUTH.relative_to(ROOT)}: {len(truth)} names")


# --------------------------------------------------------------------------
# Our side
# --------------------------------------------------------------------------

def snake(name: str) -> str:
    """camelCase -> SCREAMING_SNAKE, splitting only before an uppercase letter."""
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).upper()


def upstream_key(name: str, truth: dict) -> str:
    """Our name -> its upstream key, trying the `…G` Gwei-twin spelling too."""
    cands = [snake(name[:-1]), snake(name)] if name.endswith("G") else [snake(name)]
    return next((c for c in cands if c in truth), cands[-1])


def our_constants(fork: str) -> dict[str, str]:
    """Each `Const` entry this fork declares, mapped to the tier its body says.

    The body classifies: a `Preset.x` projection carries `[Preset]`, a `Config.x`
    projection carries `[Config]`, and a literal carries neither. Entries the
    fork inherits are not its own and are checked where they are declared.
    """
    src = (SPECS / fork / "Constants.lean").read_text()
    body = src.split("namespace Const", 1)[1].split("\nend Const", 1)[0]
    tiers = {}
    for m in re.finditer(r"^forkabbrev ([A-Za-z0-9_]+)\s*:.*?:=\s*(.*)$", body, re.M):
        name, rhs = m.group(1), m.group(2)
        if re.search(r"(Pos|Lt)$", name):
            continue                                  # our well-formedness premises
        tiers[name] = ("Preset" if rhs.startswith("Preset.")
                       else "Config" if rhs.startswith("Config.")
                       else "flat")
    return tiers


def check() -> int:
    if not GROUND_TRUTH.exists():
        sys.exit(f"{GROUND_TRUTH.relative_to(ROOT)} is missing; run with --refresh")
    truth = {k: tuple(v) for k, v in json.loads(GROUND_TRUTH.read_text()).items()}

    tier_drift, fork_drift, untabled, unattributed, total = [], [], [], 0, 0
    for fork in OUR_FORKS:
        for name, ours in sorted(our_constants(fork).items()):
            total += 1
            key = upstream_key(name, truth)
            if key in UNTABLED:
                untabled.append((fork, name, key))
                continue
            if key not in truth:
                tier_drift.append(f"  {fork}.{name}: no upstream definition of `{key}`")
                continue
            up_fork, up_tier, source = truth[key]
            if up_tier != ours:
                tier_drift.append(
                    f"  {fork}.{name}: tier is {ours}, `{key}` is defined under "
                    f"{up_tier} in {source}")
            if up_fork == "?":
                unattributed += 1
            else:
                want = "Fulu" if up_fork in ACCUMULATED else up_fork.capitalize()
                if want != fork:
                    fork_drift.append(
                        f"  {fork}.{name}: declared in {fork}, `{key}` is introduced "
                        f"by {up_fork} ({source})")

    if tier_drift:
        print("TIER DRIFT")
        print("\n".join(tier_drift))
    if fork_drift:
        print("\nFORK DRIFT")
        print("\n".join(fork_drift))

    print(f"\nchecked {total} constants against {len(truth)} upstream names")
    print(f"  {len(untabled)} untabled upstream (placed by reading the spec text): "
          + ", ".join(n for _, n, _ in untabled))
    print(f"  {unattributed} carry a tier but no fork attribution; tier checked only")
    if tier_drift or fork_drift:
        print(f"\n{len(tier_drift)} tier and {len(fork_drift)} fork mismatches")
        return 1
    print("  every constant's tier and owning fork match the pinned specs")
    return 0


if __name__ == "__main__":
    if "--refresh" in sys.argv:
        refresh()
    sys.exit(check())
