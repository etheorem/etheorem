"""The ssz_generic conformance test: one parametrized test per vector case.

The harness builds a request from the case on disk and submits it to the worker's
`ssz_generic_runner`; the runner returns its classify verdict. The assertion
follows the same model as the EthCLSpecs harness:

- a shape outside SizzLean's `SSZType` universe (the progressive / stable /
  compatible test structs) `xfail`s, it is collected but not a real failure;
- `bug` (a decode/round-trip/root mismatch on a well-formed vector, or a server
  crash) is a hard failure;
- `todo` (a shape the runner does not parse) is `xfail`;
- otherwise the case must `pass` (valid round-trips + roots, or invalid rejects).
"""

import pytest

from harness import build_request


def test_case(case, server, tmp_path):
    if case.shape is None:
        pytest.xfail(f"shape out of SizzLean's universe: {case.handler}/{case.case_name}")
    result = server.submit(build_request(case, tmp_path))
    if result.bucket == "bug":
        pytest.fail(f"{case.case_id}: bug — {result.detail}")
    if not result.passed and result.bucket == "todo":
        pytest.xfail(f"out of scope: {result.detail}")
    assert result.passed, f"{case.case_id}: {result.bucket} — {result.detail}"
