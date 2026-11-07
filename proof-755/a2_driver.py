"""A2 proof for competemath/tengoku#755: tengoku's OWN scripts at one ref, on the real flows of an extend part and a tag group whose modules are
«2d» (formal-conjectures' Geometry/2d.lean, tengoku#752), «1102.4662» and «A-B».

    python3 a2_driver.py <tengoku checkout at the ref> <out.json> <lake package dir to write>

Records what each step printed (class, gate verdicts, the autotag plan's module list, the merge queue's targets) and writes a Lake package with the same files,
so the workflow can `lake build` exactly the names the scripts printed and map them back to files with the ref's isnad.module_file."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

tree, out, pkg = Path(sys.argv[1]).resolve(), Path(sys.argv[2]), Path(sys.argv[3])
CI = tree / "scripts" / "ci"
sys.path[:0] = [str(CI / "tests"), str(CI), str(tree / "scripts"), str(tree / "scripts" / "tests")]
import test_extend as ex  # noqa: E402
import test_tag_class as tc  # noqa: E402
from test_gates import Repo  # noqa: E402

EXTEND = {  # path -> the module as Lean spells it (what the factory writes into the manifest and the umbrella)
    "Tengoku/FxLib/FormalConjecturesForMathlib/Geometry/2d.lean": "Tengoku.FxLib.FormalConjecturesForMathlib.Geometry.«2d»",
    "Tengoku/FxLib/Tao/1102.4662.lean": "Tengoku.FxLib.Tao.«1102.4662»",
    "Tengoku/FxLib/Fx/A-B.lean": "Tengoku.FxLib.Fx.«A-B»",
}
TAG = {
    "Tengoku/FormalConjectures/FormalConjecturesForMathlib/Geometry/2d.lean": "Tengoku.FormalConjectures.FormalConjecturesForMathlib.Geometry.«2d»",
    "Tengoku/FormalConjectures/Tao/1102.4662.lean": "Tengoku.FormalConjectures.Tao.«1102.4662»",
    "Tengoku/FormalConjectures/Fx/A-B.lean": "Tengoku.FormalConjectures.Fx.«A-B»",
}
res: dict = {"ref": subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()}


def names(text: str) -> list[str]:
    return sorted(ln for ln in text.split() if ln.startswith("Tengoku."))


def tail(s: str, n: int = 6) -> str:
    return "\n".join(s.strip().splitlines()[-n:])


# --- an extend part (the intake lane: the autotag plans it, the merge queue builds its new modules) ---
r = ex.Extend().repo()
for i, path in enumerate(EXTEND):
    r.write(path, ex.module(f"n{i}", f"import {ex.Extend.A}\n"))
r.write("Tengoku/FxLib.lean", f"import {ex.Extend.A}\n" + "".join(f"import {m}\n" for m in EXTEND.values()))
manifest = (r.dir / "data/intake/fx-lib/manifest.jsonl").read_text()
r.write("data/intake/fx-lib/manifest.jsonl", manifest + "".join(ex.record(f"n{i}", m) for i, m in enumerate(EXTEND.values())))
r.write("data/intake/fx-lib/parts/002.json", json.dumps({"library": "fx-lib", "part": 2, "gate2_unjudged": []}) + "\n")
r.commit("part 2: a 2d, a dotted and a dashed module")
e: dict = {}
rc, o = r.gate("classify.py", env=ex.BOT)
e["classify"] = {"rc": rc, "class": next((ln for ln in o.split() if ln.startswith("class=")), ""), "tail": tail(o)}
rc, o = r.gate("intake_check.py", "main", "pr")
e["intake_check"] = {"rc": rc, "tail": tail(o)}
p = subprocess.run(
    [sys.executable, str(CI / "autotag.py"), "plan", r.git("rev-parse", "main").strip(), r.git("rev-parse", "pr").strip(), "tengoku-intake[bot]"],
    cwd=r.dir,
    capture_output=True,
    text=True,
    env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "TENGOKU_ISNAD_REQUIRED": "1"},
)
plan = json.loads(p.stdout.strip().splitlines()[-1]) if p.returncode == 0 and p.stdout.strip() else {}
e["autotag_plan"] = {"rc": p.returncode, "lane": plan.get("lane"), "refused": plan.get("refused"), "modules": sorted(plan.get("modules", [])), "tail": tail(p.stderr)}
rc, o = r.gate("queue_targets.py")
e["queue_targets"] = {"rc": rc, "targets": names(o), "tail": tail(o)}
res["extend"] = e

# --- a tag group on those modules of an intake library (the merge queue builds exactly the changed modules) ---
r = Repo()
for path in TAG:
    r.write(path, tc.PLAIN)
r.write("data/intake/formal-conjectures/manifest.jsonl", json.dumps({"name": "x", "module": next(iter(TAG.values())), "library": "formal-conjectures"}) + "\n")
r.commit("formal-conjectures is in the tree")
r.git("checkout", "-q", "main")
r.git("merge", "-q", "--ff-only", "pr")
r.git("checkout", "-q", "pr")
for path in TAG:
    r.write(path, tc.tagged(tc.PLAIN, tc.TRANSLATED))
r.commit("tags")
t: dict = {}
rc, o = r.gate("classify.py", env=tc.BOT)
t["classify"] = {"rc": rc, "class": next((ln for ln in o.split() if ln.startswith("class=")), ""), "tail": tail(o)}
rc, o = r.gate("tag_check.py")
t["tag_check"] = {"rc": rc, "tail": tail(o)}
rc, o = r.gate("queue_targets.py")
t["queue_targets"] = {"rc": rc, "targets": names(o), "tail": tail(o)}
res["tag"] = t
res["expected"] = {"extend": sorted(EXTEND.values()), "tag": sorted(TAG.values())}

# --- the Lake package: the same files (plain theorems), and a root that imports them as the tree's umbrella does ---
files = {**EXTEND, **TAG}
for i, path in enumerate(files):
    (pkg / path).parent.mkdir(parents=True, exist_ok=True)
    (pkg / path).write_text(f"theorem a2_{i} : {i} + 1 = {i + 1} := rfl\n")
(pkg / "Tengoku.lean").write_text("".join(f"import {m}\n" for m in files.values()))
(pkg / "lakefile.toml").write_text('name = "tengoku"\n\n[[lean_lib]]\nname = "Tengoku"\n')
(pkg / "lean-toolchain").write_text((tree / "lean-toolchain").read_text())
out.write_text(json.dumps(res, ensure_ascii=False, indent=1) + "\n")
print(json.dumps({k: res[k] for k in ("ref", "expected")}, ensure_ascii=False))
