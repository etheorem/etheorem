"""The pyspec test: one parametrized test per vector case.

The harness builds a request from the case on disk and submits it to the
worker's Lean server; the server returns the driver's classify verdict. The
assertion follows the reject-faithfulness audit (`SPECS_ARCHITECTURE.md` §10.2):

- `bug` (`outOfBounds` / `missingKey` on well-formed input, or a server crash) is
  always a hard failure, the bug-smell the audit hunts for;
- `todo` (an unimplemented branch we intend to fill) is `xfail`, the Phase-2
  work-queue: it does not fail the run, but it is visible and a vector that reaches
  it never passes silently;
- `skip` (a branch we deliberately do not model, an out-of-scope runner or type) is
  `pytest.skip`: it is not a failure and not work-queue, so it never inflates the
  `xfail` count;
- otherwise the case must `pass` (a valid vector's root matched, or an invalid
  vector was rejected by `assert`).

As Phase 2 fills the `todo` stubs, the `xfail`s turn into passes with no test
change. The `skip`s stay skipped, they are out of scope by design.
"""

import pytest

from harness import build_request


def test_case(case, server, tmp_path):
    request = build_request(case, tmp_path)
    result = server.submit(request)
    if result.bucket == "bug":
        pytest.fail(f"{case.case_id}: bug-smell — {result.detail}")
    if not result.passed and result.bucket == "skip":
        pytest.skip(f"out of scope (not modeled): {result.detail}")
    if not result.passed and result.bucket == "todo":
        pytest.xfail(f"unimplemented (Phase 2 work-queue): {result.detail}")
    assert result.passed, f"{case.case_id}: {result.bucket} — {result.detail}"
