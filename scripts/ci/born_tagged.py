#!/usr/bin/env python3
"""born_tagged.py <base> <head> — every theorem of a lane PR arrives with its isnad tag (docs/isnad.md, "Born tagged").

The lanes that put new theorems into the tree by themselves, the studied lane (Leak's best theorems, scripts/ci/studied_check.py) and the intake lane
(translated libraries, scripts/ci/intake_check.py), used to leave the tags to a second pull request, the sweep's: one more PR to approve for every PR
the lane opened. Now the lane's PR carries them. The workflow `autotag-build` tags the PR's modules on the compiled tree and `autotag-push` adds the tags to the
PR's branch as one commit (scripts/ci/autotag.py, autotag_push.py); this is the gate that holds them to it:

  studied  always. Every module of the PR has well-formed tags (`isnad.parse_tag`: exactly the fields, printable ASCII, a known version), each the last line of its
           docstring and from the place the module lives (`from=novel`), and the theorem its manifest line names carries one.
  intake   when the repository variable TENGOKU_ISNAD_REQUIRED is `1` (the lane's tagging stage is live): a module that declares a theorem has at least one tag, and
           every tag is well formed and from the module's place (`from=translated`).

The gate runs no Lean, so it cannot know that an id IS the id of its theorem: the merge queue builds the modules and `scripts/ci/tag_verify.py` recomputes every
tag (`isnad.py check-tags`). A tag that is not the build's, a theorem left without one, a tag that belongs to no theorem, all eject the PR from the queue.
ISNAD_TAGS_PENDING=1 skips the check: the autotag workflow runs the lane's own gate that way, before it builds anything, to be sure the content passed the
rules (allow-list, shape) first; it is the only caller that sets it.
"""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))  # scripts/ of the checkout this file is in
import isnad  # noqa: E402
import isnad_tag as tg  # noqa: E402
from _git import blob, changed_files, fail  # noqa: E402
from lean_lex import code_only  # noqa: E402
from studied_check import is_studied  # noqa: E402
from tag_check import doc_tag_errors, module_of  # noqa: E402

INTAKE_MANIFEST = re.compile(r"data/intake/([^/]+)/manifest\.jsonl")
STUDIED_MODULE = re.compile(r"Tengoku/Studied/[^/]+/S[0-9a-f]{12}\.lean")
UMBRELLAS = ("Tengoku/All.lean", "Tengoku/Studied.lean")
ROOT_FILE = re.compile(r"Tengoku/[^/]+\.lean")  # a library's (or a target's) file that only imports its modules
# a theorem a tagger tags: not private (it skips those by rule), one per line start; an approximation that only decides whether "no tag at all" is an error
THEOREM = re.compile(r"^(?:@\[[^\]\n]*\][ \t]*)*(?:protected[ \t]+)?(?:theorem|lemma)[ \t]+\S", re.M)


def lane_of(base: str, head: str) -> str | None:
    """`studied`, `intake` (an intake or extend PR: a library's manifest changes), or None."""
    if is_studied(base, head):
        return "studied"
    if any(INTAKE_MANIFEST.fullmatch(p) for _, p in changed_files(base, head)):
        return "intake"
    return None


def lane_modules(base: str, head: str, lane: str) -> list[str]:
    """The paths of the Lean modules the PR adds that a tagger tags: not the umbrella files, not a library's root file that only imports."""
    out = []
    for st, p in changed_files(base, head):
        if st != "A" or not p.startswith("Tengoku/") or not p.endswith(".lean") or p in UMBRELLAS or ROOT_FILE.fullmatch(p):
            continue
        if lane == "studied" and not STUDIED_MODULE.fullmatch(p):
            continue
        out.append(p)
    return sorted(out)


def decl_tagged(text: str, name: str) -> bool:
    """The declaration `name` (the last component of a written name) has a docstring whose last line is an isnad tag."""
    decl = re.compile(
        rf"^(?:@\[[^\]\n]*\][ \t]*)*(?:protected[ \t]+|private[ \t]+)?(?:theorem|lemma)[ \t]+(?:[\w.']*\.)?{re.escape(name.split('.')[-1])}(?![\w'.])",
        re.M,
    )
    segs = tg.scan(text)
    for i, (kind, a, b) in enumerate(segs):
        m = decl.search(text[a:b]) if kind == "code" else None
        if not m:
            continue
        prev = segs[i - 1] if i else None
        if prev and prev[0] == "doc" and not re.sub(r"@\[[^\]]*\]|\s", "", text[a : a + m.start()]):
            last = [x for x in text[prev[1] + 3 : prev[2] - 2].split("\n") if x.strip()][-1:]
            return bool(last) and bool(tg.TAG_LINE.match(last[0]))
        return False
    return False


def module_errors(path: str, text: str, name: str | None = None, require_theorem_tag: bool = False) -> list[str]:
    """What is wrong with the tags of one module of a lane PR. `name`: the theorem the lane says the module is about (studied): it must carry a tag."""
    origin = isnad.origin_of(module_of(path))
    errors: list[str] = []
    tags = 0
    for kind, a, b in tg.scan(text):
        if kind == "doc":
            more, n = doc_tag_errors(path, text[a + 3 : b - 2], origin)
            errors += more
            tags += n
    if name is not None:
        if not decl_tagged(text, name):
            errors.append(f"{path}: the theorem {name} has no isnad tag as the last line of its docstring")
    elif (require_theorem_tag or THEOREM.search(code_only(text))) and not tags:
        errors.append(f"{path}: declares theorems and carries no isnad tag")
    return errors


def pending() -> bool:
    return os.environ.get("ISNAD_TAGS_PENDING") == "1"


def required(lane: str | None) -> bool:
    return lane == "studied" or (lane == "intake" and os.environ.get("TENGOKU_ISNAD_REQUIRED") == "1")


def main(argv: list[str]) -> int:
    base, head = argv[1], argv[2]
    lane = lane_of(base, head)
    if lane is None:
        print("not a lane PR: nothing to check")
        return 0
    if pending():
        print("tags pending (the autotag workflow's own run): not checked")
        return 0
    if not required(lane):
        print(f"{lane} PR: born-tagged is not required yet (TENGOKU_ISNAD_REQUIRED is not 1)")
        return 0
    errors: list[str] = []
    names: dict[str, str] = {}
    if lane == "studied":
        for st, p in changed_files(base, head):
            if re.fullmatch(r"data/studied/[^/]+/manifest\.jsonl", p):
                old = (blob(base, p) or b"").decode("utf-8")
                new = (blob(head, p) or b"").decode("utf-8")
                for ln in new[len(old) :].splitlines() if new.startswith(old) else []:
                    try:
                        row = json.loads(ln)
                        names[str(row["module"]).replace(".", "/") + ".lean"] = str(row["name"])
                    except (ValueError, KeyError):
                        pass
    mods = lane_modules(base, head, lane)
    for p in mods:
        text = (blob(head, p) or b"").decode("utf-8", errors="replace")
        errors += module_errors(p, text, names.get(p) if lane == "studied" else None)
    if errors:
        fail(f"{lane} PR is not born tagged: " + "; ".join(errors[:8]) + (f"; and {len(errors) - 8} more" if len(errors) > 8 else ""))
    print(f"born tagged ok: {len(mods)} module(s) of a {lane} PR carry their tags")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
