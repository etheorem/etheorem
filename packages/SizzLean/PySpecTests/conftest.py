"""pytest-xdist configuration for the SizzLean ssz_generic conformance suite.

Each xdist worker holds one long-lived `ssz_generic_runner` through the
`session`-scoped `server` fixture (session scope is per-worker in xdist), so
there is no per-vector Lean startup. Cases are parametrized at collection time by
walking the downloaded `general` archive.

Run:
    pytest                # the dev subset (a few cases per handler)
    pytest -n auto        # sharded across cores via xdist
    pytest --subset=0     # the full in-scope suite
"""

import pytest

from harness import ServerClient, ensure_archive, walk_cases, PINNED_VERSION


def pytest_addoption(parser):
    parser.addoption("--subset", type=int, default=2,
                     help="cases per (handler, valid/invalid); 0 = the full suite")
    parser.addoption("--tag", default=PINNED_VERSION,
                     help="consensus-spec-tests release tag")


def pytest_generate_tests(metafunc):
    if "case" in metafunc.fixturenames:
        cfg = metafunc.config
        subset = cfg.getoption("--subset")
        tag = cfg.getoption("--tag")
        limit = None if subset == 0 else subset
        root = ensure_archive(tag)
        cases = list(walk_cases(root, limit=limit))
        metafunc.parametrize("case", cases, ids=[c.case_id for c in cases])


@pytest.fixture(scope="session")
def server():
    """One `ssz_generic_runner` per worker, re-spawned on death."""
    client = ServerClient()
    yield client
    client.close()
