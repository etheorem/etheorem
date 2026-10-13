"""pytest-xdist pyspec configuration.

Each xdist worker holds one long-lived `pyspec_server` through the
`session`-scoped `server` fixture (session scope is per-worker in xdist), so
there is no per-vector Lean startup and the crypto cache stays warm. Cases are
parametrized at collection time by walking the downloaded archive.

Run:
    pytest                       # the dev subset (a few cases per handler)
    pytest -n auto               # sharded across cores via xdist
    pytest --subset=0            # the full in-scope suite
    pytest --fork=gloas          # the Gloas vectors
    pytest --fork=heze           # the Heze vectors
    pytest --vectors=../theorem_vectors/formats/pyspec --fork=gloas
                                 # the generator's rendered tree, no archive
"""

from pathlib import Path

import pytest

from harness import ServerClient, ensure_archive, walk_cases, walk_vector_cases, PINNED_VERSION


def pytest_addoption(parser):
    parser.addoption("--preset", default="minimal",
                     help="consensus-spec-tests preset (minimal / mainnet)")
    parser.addoption("--fork", default="fulu", help="fork to run (fulu / gloas / heze)")
    parser.addoption("--subset", type=int, default=2,
                     help="cases per (runner,handler); 0 = the full suite")
    parser.addoption("--tag", default=PINNED_VERSION,
                     help="consensus-spec-tests release tag")
    parser.addoption("--vectors", default=None,
                     help="point at the theorem-vector generator's "
                          "formats/pyspec output directory instead of the "
                          "downloaded archive; --fork/--preset filter the "
                          "walk, their defaults still apply")
    parser.addoption("--no-crypto-cache", action="store_true", default=False,
                     help="disable the server's BLS-verify memo (plain FFI); "
                          "the default keeps caching on")


def pytest_generate_tests(metafunc):
    if "case" in metafunc.fixturenames:
        cfg = metafunc.config
        preset = cfg.getoption("--preset")
        fork = cfg.getoption("--fork")
        vectors = cfg.getoption("--vectors")
        if vectors is not None:
            # The rendered tree is curated; collect it directly, no archive
            # download and no cache read.
            cases = list(walk_vector_cases(Path(vectors), preset=preset, fork=fork))
            if not cases:
                raise pytest.UsageError(
                    f"--vectors={vectors} (fork={fork}, preset={preset}) "
                    f"collected no cases; check the path and the fork/preset filters")
        else:
            subset = cfg.getoption("--subset")
            tag = cfg.getoption("--tag")
            limit = None if subset == 0 else subset
            root = ensure_archive(tag, preset)
            cases = list(walk_cases(root, preset, fork, limit_per_handler=limit))
        metafunc.parametrize("case", cases, ids=[c.case_id for c in cases])


@pytest.fixture(scope="session")
def server(request):
    """One Lean server per worker at the selected fork + preset, re-spawned on death."""
    client = ServerClient(fork=request.config.getoption("--fork"),
                          preset=request.config.getoption("--preset"),
                          no_crypto_cache=request.config.getoption("--no-crypto-cache"))
    yield client
    client.close()
