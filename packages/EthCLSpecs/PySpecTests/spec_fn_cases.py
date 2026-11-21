"""Generate the differential cases for the shuffle and selection functions.

The pinned pyspec is the oracle. This script calls each function on random and edge-case
inputs and records the answer, or the class of the exception the call raises.
`test_spec_fn.py` then runs the fork body on the same inputs through the `pyspec_server`
`spec_fn` request and compares the two, case by case.

The harness venv has no pyspec, so this script runs under the pinned spec's own interpreter:

    $PYSPEC_PYTHON -I -W ignore spec_fn_cases.py --fork gloas --preset minimal --out DIR

`DIR` receives one raw `.ssz` file per generated state and `cases.jsonl`, one JSON object
per case. Each object names the function, the state file (or `null`), the integer
arguments, the index list, the byte-string arguments as `0x` hex, the config overrides, and
the expected answer in the server's syntax (`ok:n:…`, `ok:b:0x…`, `err:<kind>`). The `--seed`
flag fixes the random choices, so a run is reproducible.
"""

from __future__ import annotations

import argparse
import json
import random
from importlib import import_module
from pathlib import Path

from eth_consensus_specs.test.helpers.genesis import create_genesis_state
from eth_consensus_specs.test.helpers.keys import pubkeys
from eth_consensus_specs.utils.ssz.ssz_impl import serialize

UINT64_MAX = 2**64 - 1


def answer(call, render):
    """Run `call` and render its result, or name the class of the exception it raises.

    The classes follow the reject kinds the Lean runner sees: `assert` for `AssertionError`,
    `index` for `IndexError`, and `arithmetic` for the `uint64` faults, which raise
    `ValueError` (`SSZValueError` and pydantic's `ValidationError` are subclasses),
    `OverflowError`, or `ZeroDivisionError`. Any other exception propagates, so a case the
    model cannot express stops the run instead of turning into a silent answer."""
    try:
        out = call()
    except AssertionError:
        return "err:assert"
    except IndexError:
        return "err:index"
    except (ValueError, ArithmeticError):
        return "err:arithmetic"
    return render(out)


def indices_out(xs) -> str:
    return "ok:n:" + ",".join(str(int(x)) for x in xs)


def count_out(n) -> str:
    return f"ok:n:{int(n)}"


def bytes_out(b) -> str:
    return "ok:b:0x" + bytes(b).hex()


class Gen:
    """Collect the cases of one fork at one preset."""

    def __init__(self, spec, fork: str, out: Path, rng: random.Random):
        self.spec = spec
        self.fork = fork
        self.out = out
        self.rng = rng
        self.cases: list[dict] = []
        self.state_count = 0

    def add(self, fn: str, expected: str, state_file: str | None = None, nats=(),
            indices=(), byte_args=(), cfg: dict[str, int] | None = None) -> None:
        self.cases.append({
            "fn": fn,
            "state": state_file,
            "nats": [int(n) for n in nats],
            "indices": [int(i) for i in indices],
            "bytes": ["0x" + bytes(b).hex() for b in byte_args],
            "cfg": cfg or {},
            "expected": expected,
        })

    def seed32(self) -> bytes:
        return bytes(self.rng.getrandbits(8) for _ in range(32))

    def save_state(self, state) -> str:
        name = f"state_{self.state_count:03d}.ssz"
        self.state_count += 1
        (self.out / name).write_bytes(serialize(state))
        return name

    # --- States ---------------------------------------------------------------------------

    def make_state(self, n: int, max_epoch: int):
        """A genesis state with `n` validators, then random registry and RANDAO changes so
        the active set, the effective balances, and the seeds vary by epoch."""
        spec, rng = self.spec, self.rng
        increment = spec.EFFECTIVE_BALANCE_INCREMENT
        top = spec.MAX_EFFECTIVE_BALANCE_ELECTRA
        # The Gloas genesis computes a PTC for every slot, which needs a committee member per
        # slot. So the genesis holds at least `2 * SLOTS_PER_EPOCH` validators, and the ones
        # past `n` never activate.
        built = max(n, 2 * spec.SLOTS_PER_EPOCH)
        balances = [top] * built
        for i in range(n):
            balances[i] = rng.choice([spec.MIN_ACTIVATION_BALANCE, top,
                                      rng.randrange(1, top // increment + 1) * increment])
        state = create_genesis_state(spec, balances, spec.MIN_ACTIVATION_BALANCE)
        for v in list(state.validators)[n:]:
            v.activation_epoch = spec.FAR_FUTURE_EPOCH

        for v in list(state.validators)[:n]:
            roll = rng.random()
            if roll < 0.3:
                v.activation_epoch = rng.randrange(0, max_epoch + 1)
            if roll < 0.15 or rng.random() < 0.1:
                v.exit_epoch = rng.randrange(int(v.activation_epoch) if v.activation_epoch < UINT64_MAX else 0,
                                             max_epoch + 2)
            if rng.random() < 0.1:
                v.slashed = True
            if rng.random() < 0.05:
                v.effective_balance = 0
            elif rng.random() < 0.3:
                v.effective_balance = rng.randrange(0, top // increment + 1) * increment

        vector = spec.EPOCHS_PER_HISTORICAL_VECTOR
        for epoch in range(0, max_epoch + 3):
            state.randao_mixes[(epoch + vector - spec.MIN_SEED_LOOKAHEAD - 1) % vector] = self.seed32()
        state.slot = rng.randrange(0, max_epoch + 1) * spec.SLOTS_PER_EPOCH + rng.randrange(spec.SLOTS_PER_EPOCH)

        if hasattr(state, "ptc_window"):
            for row in state.ptc_window:
                for k in range(len(row)):
                    row[k] = rng.randrange(0, max(n, 1))
        return state

    # --- Cases ----------------------------------------------------------------------------

    def pure_cases(self) -> None:
        """The two functions with no state: the permutation and the committee slice."""
        spec, rng = self.spec, self.rng
        for count in [0, 1, 2, 3, 5, 8, 17, 64, 100, 255, 256, 257, 1000]:
            seed = self.seed32()
            self.add("compute_shuffled_permutation",
                     answer(lambda: spec.compute_shuffled_permutation(spec.Uint64(count), spec.Bytes32(seed)), indices_out),
                     nats=[count], byte_args=[seed])
        for _ in range(40):
            size = rng.choice([0, 1, 2, 7, 33, 128, 300])
            indices = [rng.randrange(0, 2**20) for _ in range(size)]
            count = rng.choice([0, 1, 2, 4, 32, 64, rng.randrange(1, 200)])
            index = rng.choice([0, 1, count - 1 if count else 0, count, count + 1, rng.randrange(0, 300),
                                UINT64_MAX, 2**62, 2**64, 2**64 + 3])
            if rng.random() < 0.1:
                count = rng.choice([UINT64_MAX, 2**64])
            seed = self.seed32()
            # The arguments are `uint64` values, as every spec caller passes them. A value at
            # or above `2 ** 64` raises in its construction, which the model reports the same.
            self.add("compute_committee",
                     answer(lambda: spec.compute_committee([spec.ValidatorIndex(i) for i in indices],
                                                           spec.Bytes32(seed), spec.Uint64(index),
                                                           spec.Uint64(count)), indices_out),
                     nats=[index, count], indices=indices, byte_args=[seed])

    def state_cases(self, state, max_epoch: int, cfg: dict[str, int]) -> None:
        spec, rng = self.spec, self.rng
        name = self.save_state(state)
        n = len(state.validators)
        epochs = sorted({0, 1, max_epoch, max_epoch + 1, rng.randrange(0, max_epoch + 2),
                         rng.randrange(0, max_epoch + 2)})
        big_epochs = [UINT64_MAX, UINT64_MAX - spec.EPOCHS_PER_HISTORICAL_VECTOR + 2,
                      UINT64_MAX - spec.EPOCHS_PER_HISTORICAL_VECTOR + 1]
        spe = spec.SLOTS_PER_EPOCH

        for epoch in epochs + big_epochs:
            self.add("get_active_validator_indices",
                     answer(lambda: spec.get_active_validator_indices(state, spec.Epoch(epoch)), indices_out),
                     name, nats=[epoch])
            self.add("get_committee_count_per_slot",
                     answer(lambda: spec.get_committee_count_per_slot(state, spec.Epoch(epoch)), count_out),
                     name, nats=[epoch])
            for domain in self.domains():
                self.add("get_seed",
                         answer(lambda: spec.get_seed(state, spec.Epoch(epoch), spec.DomainType(domain)), bytes_out),
                         name, nats=[epoch], byte_args=[domain])

        for epoch in epochs:
            self.add("get_beacon_proposer_indices",
                     answer(lambda: spec.get_beacon_proposer_indices(state, spec.Epoch(epoch)), indices_out),
                     name, nats=[epoch])
            active = list(spec.get_active_validator_indices(state, spec.Epoch(epoch)))
            # The last two pools hold an index past the registry: alone, and behind valid ones.
            for pool in [active, [], rng.sample(active, min(len(active), 3)),
                         [rng.randrange(0, n) for _ in range(rng.randrange(1, 6))],
                         [len(state.validators) + rng.randrange(0, 5)],
                         active[:3] + [len(state.validators) + rng.randrange(0, 5)]]:
                seed = self.seed32()
                self.add("compute_proposer_indices",
                         answer(lambda: spec.compute_proposer_indices(
                             state, spec.Epoch(epoch), spec.Bytes32(seed), [spec.ValidatorIndex(i) for i in pool]),
                             indices_out),
                         name, nats=[epoch], indices=pool, byte_args=[seed])

        slots = sorted({rng.randrange(0, (max_epoch + 2) * spe) for _ in range(4)} | {0, (max_epoch + 1) * spe})
        for slot in slots:
            cps = int(spec.get_committee_count_per_slot(state, spec.compute_epoch_at_slot(spec.Slot(slot))))
            for index in sorted({0, cps - 1, cps, cps + 1, rng.randrange(0, cps * spe + 2), UINT64_MAX, 2**64}):
                if index < 0:
                    continue
                self.add("get_beacon_committee",
                         answer(lambda: spec.get_beacon_committee(state, spec.Slot(slot), spec.CommitteeIndex(index)),
                                indices_out),
                         name, nats=[slot, index])
            if hasattr(spec, "compute_ptc"):
                self.add("compute_ptc", answer(lambda: spec.compute_ptc(state, spec.Slot(slot)), indices_out),
                         name, nats=[slot])
                for fork_epoch in [0, max(0, int(spec.get_current_epoch(state)) - 1), max_epoch + 5]:
                    gcfg = dict(cfg, GLOAS_FORK_EPOCH=fork_epoch)
                    saved = spec.config
                    spec.config = saved._replace(GLOAS_FORK_EPOCH=fork_epoch)
                    try:
                        got = answer(lambda: spec.get_ptc(state, spec.Slot(slot)), indices_out)
                    finally:
                        spec.config = saved
                    self.add("get_ptc", got, name, nats=[slot], cfg=gcfg)
            if hasattr(spec, "get_inclusion_list_committee"):
                self.add("get_inclusion_list_committee",
                         answer(lambda: spec.get_inclusion_list_committee(state, spec.Slot(slot)), indices_out),
                         name, nats=[slot])

        if hasattr(spec, "compute_balance_weighted_selection"):
            active = list(spec.get_active_validator_indices(state, spec.get_current_epoch(state)))
            pools = [active, [], [rng.randrange(0, n) for _ in range(rng.randrange(1, 40))],
                     rng.sample(active, min(len(active), 5))]
            pools.append([len(state.validators) + rng.randrange(0, 5)])
            pools.append(active[:3] + [len(state.validators) + rng.randrange(0, 5)])
            for pool in pools:
                for size in [0, 1, rng.randrange(2, 40)]:
                    for shuffle in (0, 1):
                        seed = self.seed32()
                        self.add("compute_balance_weighted_selection",
                                 answer(lambda: spec.compute_balance_weighted_selection(
                                     state, [spec.ValidatorIndex(i) for i in pool], spec.Bytes32(seed),
                                     spec.Uint64(size), bool(shuffle)), indices_out),
                                 name, nats=[size, shuffle], indices=pool, byte_args=[seed])

        self.add("get_next_sync_committee",
                 answer(lambda: spec.get_next_sync_committee(state), lambda c: bytes_out(serialize(c))), name)

    def domains(self) -> list[bytes]:
        spec = self.spec
        names = ["DOMAIN_BEACON_ATTESTER", "DOMAIN_BEACON_PROPOSER", "DOMAIN_SYNC_COMMITTEE", "DOMAIN_PTC_ATTESTER"]
        return [bytes(getattr(spec, d)) for d in names if hasattr(spec, d)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--fork", required=True, choices=["fulu", "gloas", "heze"])
    parser.add_argument("--preset", required=True, choices=["minimal", "mainnet"])
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    spec = import_module(f"eth_consensus_specs.{args.fork}.{args.preset}")
    args.out.mkdir(parents=True, exist_ok=True)
    gen = Gen(spec, args.fork, args.out, random.Random(f"{args.fork}/{args.preset}/{args.seed}"))
    gen.pure_cases()

    # Registry sizes: tiny ones reach the empty-set paths, and the large ones fill several
    # committees per slot (mainnet needs SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE = 4096
    # validators per committee per slot, and the key list holds 8193).
    sizes = [1, 2, 5, 16, 33, 64, 130, 300] if args.preset == "minimal" else [1, 40, 600, 4300, len(pubkeys)]
    for n in sizes:
        max_epoch = gen.rng.randrange(2, 12)
        gen.state_cases(gen.make_state(n, max_epoch), max_epoch, {})

    with open(args.out / "cases.jsonl", "w") as f:
        for case in gen.cases:
            f.write(json.dumps(case) + "\n")
    print(f"{len(gen.cases)} cases, {gen.state_count} states -> {args.out}")


if __name__ == "__main__":
    main()
