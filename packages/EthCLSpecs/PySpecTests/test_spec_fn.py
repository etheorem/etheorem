"""The differential test of the shuffle and selection functions against the pinned pyspec.

`spec_fn_cases.py` writes the cases with the pyspec's own answers. This test sends each case
to the worker's Lean server as a `spec_fn` request. The server runs the fork body on the
same inputs and compares its answer with the pyspec's. The test collects nothing unless
`--spec-fn-cases` names a case directory for the selected `--fork` and `--preset`:

    pytest test_spec_fn.py --fork=gloas --preset=minimal --spec-fn-cases=DIR

A `skip` or `todo` answer fails the case here. Every function the generator writes for a
fork exists in that fork's pyspec, so the body has to model it.
"""

import json
from pathlib import Path

import pytest


def _load(cases_dir: Path) -> list[dict]:
    with open(cases_dir / "cases.jsonl") as f:
        return [json.loads(line) for line in f]


def pytest_generate_tests(metafunc):
    if "spec_fn_case" in metafunc.fixturenames:
        cases_dir = metafunc.config.getoption("--spec-fn-cases")
        cases = _load(Path(cases_dir)) if cases_dir else []
        for c in cases:
            c["dir"] = cases_dir
        metafunc.parametrize("spec_fn_case", cases,
                             ids=[f"{i:04d}-{c['fn']}" for i, c in enumerate(cases)])


def request_line(case: dict) -> str:
    """Encode one case as the server's tab-separated `spec_fn` request."""
    state = str(Path(case["dir"]) / case["state"]) if case["state"] else "-"
    cfg = case["cfg"]
    cfg_field = "cfg=" + (",".join(f"{k}:{v}" for k, v in sorted(cfg.items())) if cfg else "-")
    return "\t".join([
        "spec_fn", case["fn"], state,
        ",".join(str(n) for n in case["nats"]),
        ",".join(str(i) for i in case["indices"]),
        ",".join(case["bytes"]),
        case["expected"],
        cfg_field,
    ])


def test_spec_fn(spec_fn_case, server):
    result = server.submit(request_line(spec_fn_case))
    assert result.passed, f"{spec_fn_case['fn']}: {result.bucket} — {result.detail}"
