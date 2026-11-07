"""A2 proof, second half: for one ref, `lake build` each module name its scripts printed (the autotag plan's list, the queue's targets) one at a time in the
package a2_driver.py wrote, and map each name back to its file with that ref's isnad.module_file (what `isnad.py tag/check-tags --module` writes into).

    python3 a2_lake.py <tengoku checkout at the ref> <res.json from a2_driver.py> <package dir>   -> adds "lake" and "module_file" to res.json
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

tree, res_path, pkg = Path(sys.argv[1]).resolve(), Path(sys.argv[2]), Path(sys.argv[3]).resolve()
sys.path.insert(0, str(tree / "scripts"))
import isnad  # noqa: E402

res = json.loads(res_path.read_text())
lists = {
    "extend: autotag plan (lake build + isnad --module)": res["extend"]["autotag_plan"]["modules"],
    "extend: merge queue targets": res["extend"]["queue_targets"]["targets"],
    "tag: merge queue targets": res["tag"]["queue_targets"]["targets"],
}
lake: dict = {}
mf: dict = {}
for label, mods in lists.items():
    lake[label] = []
    mf[label] = []
    for m in mods:
        p = subprocess.run(["lake", "build", m], cwd=pkg, capture_output=True, text=True)
        o = p.stdout + p.stderr
        err = next((ln.strip() for ln in o.splitlines() if "error" in ln.lower()), "")
        built = next((ln.strip() for ln in o.splitlines() if " Built " in ln or "Build completed" in ln), "")
        lake[label].append({"module": m, "rc": p.returncode, "error": err, "built": built})
        try:
            f = isnad.module_file(m, pkg)
            mf[label].append({"module": m, "file": str(f.relative_to(pkg)), "exists": f.is_file()})
        except ValueError as e:
            mf[label].append({"module": m, "file": f"refused: {e}", "exists": False})
res["lake"], res["module_file"] = lake, mf
res_path.write_text(json.dumps(res, ensure_ascii=False, indent=1) + "\n")
for label in lists:
    for b, f in zip(lake[label], mf[label]):
        print(f"{label}\t{b['module']}\tlake rc={b['rc']} {b['error'] or b['built']}\tmodule_file={f['file']} exists={f['exists']}")
