# EthCLSpecs PySpecTests harness

`pytest-xdist` driver for the upstream `consensus-spec-tests` vectors. Each
worker holds one long-lived `pyspec_server` (the Lean conformance runner) through
a `session`-scoped fixture, so there is no per-vector Lean startup and the crypto
cache stays warm (`FRAMEWORK_ARCHITECTURE.md` §13.3).

## Layout

- `harness.py` — archive download/extract (cached under `~/.cache/sizzlean`),
  case-tree walk, `meta.yaml` parse, snappy decompression, the request encoding,
  and `ServerClient` (the long-lived server with re-spawn on death).
- `conftest.py` — the `server` session fixture and the `case` parametrization;
  options `--preset`, `--fork`, `--subset`, `--tag`, `--no-crypto-cache`.
- `test_conformance.py` — one test per case; the reject-faithfulness verdict
  (`bug` fails hard, `todo` is `xfail` the Phase-2 work-queue, otherwise the case
  must pass).

## Running

From this directory, with the repo venv:

```bash
../../../.venv/bin/python -m pytest                 # dev subset (2 cases/handler)
../../../.venv/bin/python -m pytest -n auto         # sharded across cores
../../../.venv/bin/python -m pytest --subset=0      # full in-scope suite
../../../.venv/bin/python -m pytest --fork=gloas    # the Gloas vectors
../../../.venv/bin/python -m pytest --preset=mainnet --subset=0   # mainnet (slow)
../../../.venv/bin/python -m pytest --no-crypto-cache   # plain FFI, BLS-verify memo off
```

`--no-crypto-cache` sets `ETHCL_DISABLE_CRYPTO_CACHE` for the server, swapping the
caching backend for the plain FFI (caching is on by default). Useful for comparing
cache-on against cache-off timings.

The pin (`--tag`, default `v1.7.0-alpha.10`) selects the release; the archive is
downloaded once and cached.

## Status

While the spec port is in progress, in-scope cases that reach an unimplemented
branch report `xfail` (`todo`) rather than failing, so the run stays green and the
work-queue stays visible. A vector that reaches a `todo` never passes silently; an
`outOfBounds` / `missingKey` on well-formed input fails hard as a bug-smell. As the
Fulu/Gloas ports fill the `todo` stubs (Phase 2+), the `xfail`s become passes with
no harness change.
