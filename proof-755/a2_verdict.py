"""A2 proof, verdict: main (before tengoku#755) must fail where #752 failed, #755 must pass every step. Prints a Markdown table (the run's summary) and exits 1
if either side does not do what it must.

    python3 a2_verdict.py <res-main.json> <res-pr.json>
"""

from __future__ import annotations

import json
import sys

main, pr = (json.load(open(p)) for p in sys.argv[1:3])
rows: list[tuple[str, str, str]] = []
problems: list[str] = []


def ok_steps(r: dict) -> list[tuple[str, bool, str]]:
    e, t = r["extend"], r["tag"]
    out = [
        ("extend: classify", e["classify"]["rc"] == 0 and e["classify"]["class"] == "class=extend", e["classify"]["class"]),
        ("extend: intake_check", e["intake_check"]["rc"] == 0, f"rc={e['intake_check']['rc']}"),
        (
            "extend: autotag plan lists Lean's names",
            e["autotag_plan"]["lane"] == "intake" and not e["autotag_plan"]["refused"] and e["autotag_plan"]["modules"] == r["expected"]["extend"],
            ", ".join(e["autotag_plan"]["modules"]),
        ),
        ("extend: queue targets are Lean's names", e["queue_targets"]["targets"] == r["expected"]["extend"], ", ".join(e["queue_targets"]["targets"])),
        ("tag: classify", t["classify"]["rc"] == 0 and t["classify"]["class"] == "class=tag", t["classify"]["class"]),
        ("tag: tag_check", t["tag_check"]["rc"] == 0, f"rc={t['tag_check']['rc']}"),
        ("tag: queue targets are Lean's names", t["queue_targets"]["targets"] == r["expected"]["tag"], ", ".join(t["queue_targets"]["targets"])),
    ]
    for label, builds in r["lake"].items():
        for b in builds:
            out.append((f"lake build ({label}) {b['module']}", b["rc"] == 0, b["error"] or b["built"]))
    for label, files in r["module_file"].items():
        for f in files:
            out.append((f"isnad.module_file ({label}) {f['module']}", f["exists"], f["file"]))
    return out


m_steps, p_steps = ok_steps(main), ok_steps(pr)
print(f"| step | main {main['ref'][:7]} | #755 {pr['ref'][:7]} |\n|---|---|---|")
for (label, mok, mwhat), (plabel, pok, pwhat) in zip(m_steps, p_steps):
    name = label if label == plabel else f"{label} / {plabel}"
    print(f"| {name} | {'✅' if mok else '❌'} {mwhat} | {'✅' if pok else '❌'} {pwhat} |")
for label, pok, what in p_steps:
    if not pok:
        problems.append(f"#755 fails: {label}: {what}")
twod = [
    b
    for builds in main["lake"].values()
    for b in builds
    if b["module"].endswith("Geometry.2d") and b["rc"] != 0 and "unknown target" in b["error"] and "Geometry.2d" in b["error"]
]
if not twod:
    problems.append("main does not fail with `unknown target …Geometry.2d` (the tengoku#752 error)")
print()
print("\n".join(f"- {p}" for p in problems) if problems else "VERDICT: main fails with tengoku#752's `unknown target …Geometry.2d`; #755 passes every step.")
sys.exit(1 if problems else 0)
