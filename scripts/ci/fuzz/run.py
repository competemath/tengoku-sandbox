#!/usr/bin/env python3
"""run.py (--changed BASE HEAD | --all) [--list | --replay] — run the fuzz targets a change covers.

pr-tests.yml runs it on a pull request and queue-gate.yml on a merge group, so a change to a covered gate script
waits for its targets. Each target (fuzz_<name>.py in this directory) runs under atheris for its RUNS inputs from
a fixed seed (-seed=1, PYTHONHASHSEED=0), starting from its corpus: a run is reproducible on the same Python. A
target runs when a file in its COVERS changed, or its own file or corpus; a change to run.py, _harness.py or the
fuzz requirements runs them all. A change that covers none runs nothing.

  --list    only print the targets that would run
  --replay  no atheris: feed each target its seeds and 2,000 seeded mutations of them (what the unit tests do)

A crash prints the input that caused it (it is also saved under $RUNNER_TEMP or /tmp); to reproduce it:
  python3 scripts/ci/fuzz/fuzz_<name>.py <that file>
"""

from __future__ import annotations

import ast
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ALL = {"scripts/ci/fuzz/run.py", "scripts/ci/fuzz/_harness.py", "scripts/ci/requirements/fuzz.txt"}
MAX_SECONDS = 90  # per target: a guard for a slow runner, well above what RUNS takes (a target stopped by it still passes)


def constants(path: Path) -> dict:
    """A target's COVERS, RUNS and SEEDS, read without importing it (no atheris needed)."""
    out = {}
    for node in ast.parse(path.read_text()).body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in ("COVERS", "RUNS", "SEEDS"):
                out[node.targets[0].id] = ast.literal_eval(node.value)
    return out


def targets() -> dict[str, dict]:
    return {p.stem[len("fuzz_") :]: constants(p) for p in sorted(HERE.glob("fuzz_*.py"))}


def selected(changed: list[str]) -> list[str]:
    everything = bool(ALL & set(changed))
    out = []
    for name, c in targets().items():
        own = {f"scripts/ci/fuzz/fuzz_{name}.py"}
        if (
            everything
            or own & set(changed)
            or set(c.get("COVERS", [])) & set(changed)
            or any(f.startswith(f"scripts/ci/fuzz/corpus/{name}/") for f in changed)
        ):
            out.append(name)
    return out


def fuzz(name: str, c: dict) -> bool:
    work = Path(tempfile.mkdtemp(prefix=f"fuzz-{name}-", dir=os.environ.get("RUNNER_TEMP")))
    (work / "corpus").mkdir()
    seeds = [str(HERE / "corpus" / name)] + [str(ROOT / d) for d in c.get("SEEDS", []) if (ROOT / d).is_dir()]
    runs = c.get("RUNS", 20_000)
    cmd = [
        sys.executable,
        str(HERE / f"fuzz_{name}.py"),
        f"-runs={runs}",
        "-seed=1",
        "-max_len=8192",
        "-timeout=10",
        f"-max_total_time={MAX_SECONDS}",
        "-print_final_stats=1",
        f"-artifact_prefix={work}/",
        str(work / "corpus"),
        *seeds,
    ]
    print(f"== fuzz_{name}: {runs} inputs from seed 1", flush=True)
    r = subprocess.run(cmd, env={**os.environ, "PYTHONHASHSEED": "0"}, capture_output=True, text=True)
    done = [
        line for line in r.stderr.splitlines() if line.startswith(("Done ", "stat::number_of_executed_units", "stat::average_exec_per_sec"))
    ]
    print("\n".join(done))
    if r.returncode == 0:
        return True
    print(r.stdout[-4000:] + r.stderr[-8000:])
    for crash in sorted(work.glob("crash-*")) + sorted(work.glob("timeout-*")) + sorted(work.glob("oom-*")):
        print(f"fuzz_{name} failed on {crash} = {crash.read_bytes()[:2000]!r}")
    print(f"FAIL: fuzz_{name} (reproduce: python3 scripts/ci/fuzz/fuzz_{name}.py <the input above, as a file>)")
    return False


def main(argv: list[str]) -> int:
    if argv[:1] == ["--all"]:
        names, rest = list(targets()), argv[1:]
    elif argv[:1] == ["--changed"] and len(argv) >= 3:
        diff = subprocess.run(
            ["git", "diff", "--name-only", "--no-renames", argv[1], argv[2]], cwd=ROOT, capture_output=True, text=True, check=True
        ).stdout.split()
        names, rest = selected(diff), argv[3:]
    else:
        print(__doc__)
        return 2
    if "--list" in rest:
        print("\n".join(names))
        return 0
    if not names:
        print("fuzz: no target covers this change")
        return 0
    if "--replay" in rest:
        import importlib

        sys.path.insert(0, str(HERE))
        from _harness import replay, seeds

        for name in names:
            t = importlib.import_module(f"fuzz_{name}")
            print(f"fuzz_{name}: {replay(t.TestOneInput, seeds(name, getattr(t, 'SEEDS', [])), mutations=2000)} inputs replayed")
        return 0
    ok = [fuzz(name, targets()[name]) for name in names]
    print(f"fuzz: {sum(ok)}/{len(ok)} targets passed ({', '.join(names)})")
    return 0 if all(ok) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
