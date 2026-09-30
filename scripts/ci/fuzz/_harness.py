"""What the fuzz targets in this directory share (docs/testing.md, "Fuzzing").

A target is a file fuzz_<name>.py with
  COVERS        the files (from the repository root) whose change makes the gate run it
  RUNS          how many inputs the gate feeds it (from a fixed seed, so a result can be reproduced)
  SEEDS         optional: more directories of seed inputs than its corpus/<name>/
  TestOneInput  takes the fuzzer's bytes and raises when a property of the code under test breaks

run.py picks the targets a change covers and runs each under atheris (coverage-guided, libFuzzer). Without
atheris (the unit tests, a Mac) a target still imports, and replay() feeds it its seeds and seeded mutations of
them, the same inputs every time.
"""

from __future__ import annotations

import contextlib
import importlib.util
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
# the repository, or the ClusterFuzzLite bundle, which carries scripts/ci and schemas/ (.clusterfuzzlite/build.sh)
ROOT = Path(sys._MEIPASS) if getattr(sys, "frozen", False) else HERE.parents[2]  # type: ignore[attr-defined]
for p in (str(ROOT / "scripts" / "ci"), str(HERE)):
    if p not in sys.path:
        sys.path.insert(0, p)


def instrumenting():
    """Coverage instrumentation for what is imported under it, when atheris is installed."""
    try:
        import atheris
    except ImportError:
        return contextlib.nullcontext()
    return atheris.instrument_imports()


def code_of(module: str):
    """The code of a gate script that does its work at import (validate_records.py, lint_banked.py), compiled as an
    import compiles it, instrumented under instrumenting(): a target runs it again and again with exec."""
    spec = importlib.util.find_spec(module)
    return spec.loader.get_code(module)


def main(test_one_input) -> None:
    import atheris

    atheris.Setup(sys.argv, test_one_input)
    atheris.Fuzz()


def seeds(target: str, extra: list[str] | None = None) -> list[bytes]:
    dirs = [HERE / "corpus" / target] + [ROOT / d for d in extra or []]
    return [p.read_bytes() for d in dirs if d.is_dir() for p in sorted(d.iterdir()) if p.is_file()]


def mutate(data: bytes, rng: random.Random) -> bytes:
    """One small edit: a byte replaced, inserted or deleted, a span repeated, or a special character put in."""
    b = bytearray(data)
    op = rng.randrange(5)
    i = rng.randrange(len(b) + 1)
    if op == 0 and b:
        b[min(i, len(b) - 1)] = rng.randrange(256)
    elif op == 1:
        b[i:i] = bytes([rng.randrange(256)])
    elif op == 2 and b:
        del b[min(i, len(b) - 1)]
    elif op == 3 and b:
        j = rng.randrange(len(b))
        b[i:i] = b[j : j + rng.randrange(1, 16)]
    else:
        b[i:i] = rng.choice([b"::", b"\n", b"\r", b"%", b'"', b"'", b"/-", b"-/", b"--", b"${{", b"}}", b"\\", "�".encode()])
    return bytes(b)


def replay(test_one_input, inputs: list[bytes], mutations: int = 0, seed: int = 1) -> int:
    """Feed every input, then `mutations` seeded mutations of them (chains of up to four edits). Returns the count."""
    rng = random.Random(seed)
    for data in inputs:
        test_one_input(data)
    pool = inputs or [b""]
    for _ in range(mutations):
        data = rng.choice(pool)
        for _ in range(rng.randrange(1, 5)):
            data = mutate(data, rng)
        test_one_input(data)
    return len(inputs) + mutations
