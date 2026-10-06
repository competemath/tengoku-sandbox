#!/usr/bin/env python3
"""tag_check.py <base> <head> — the checks of a TAG PR (docs/pr-classes.md, section 7).

A tag PR writes isnad tags (`@isnad1 id=… from=… src=… shape=… vocab=…`, the last line of a theorem's docstring; docs/isnad.md) into modules that are already
in the tree, and changes nothing else. It is judged without Lean and without running anything of the PR:
  - every changed file is an existing module (status M) of the seed (`Tengoku/Seed/`), of Native (`Tengoku/Native/`) or of a library that arrived as an
    intake bundle (data/intake/<library>/ at the base); a library whose modules are generated from records is not tagged here (the promote bot regenerates
    those files), nor are the umbrella files;
  - after the tags are taken out of both sides, the code is the same bytes and every docstring the same words (scripts/isnad_tag.py `equivalent`, the law the
    tagger itself keeps): what the PR adds is tags and nothing a compiler reads. Since the code is exactly the base's, which the merge queue has already built and
    scanned, building the PR runs no code that was not run before;
  - every tag line the PR leaves in a docstring is one well-formed tag (`isnad.parse_tag`: exactly the fields, printable ASCII, a known version), at most one per
    docstring and the last line of it, and its `from=` is where the module lives (seed, novel for Native, translated for a library): a tag that claims another
    origin is refused;
  - at most 400 modules (the queue builds ~3 s a module in its 40 minutes).
What the gate cannot know without Lean is whether an id IS the id of its theorem: the merge queue builds the modules and `scripts/ci/tag_verify.py` recomputes
every tag (`scripts/isnad.py check-tags`): a tag that is not the build's, a theorem left without one, a tag that belongs to no theorem, all eject the PR.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))  # scripts/ of the checkout this file is in
import isnad  # noqa: E402
import isnad_tag as tg  # noqa: E402
from _git import blob, changed_files, fail, pascal, run  # noqa: E402

MAX_TAG_MODULES = 400
SEED_LIKE = ("Seed", "Native")


def intake_namespaces(base: str) -> set[str]:
    """the libraries that arrived as intake bundles (data/intake/<library>/manifest.jsonl at the base), as module namespaces"""
    return {
        pascal(m.group(1))
        for p in run("ls-tree", "-r", "--name-only", base, "data/intake").split("\n")
        if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))
    }


def in_scope(path: str, intake: set[str]) -> bool:
    """a module that may be tagged: below Tengoku/Seed/, Tengoku/Native/ or Tengoku/<intake library>/"""
    m = re.fullmatch(r"Tengoku/([^/]+)/.+\.lean", path)
    return bool(m) and (m.group(1) in SEED_LIKE or m.group(1) in intake)


def module_of(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def texts(base: str, head: str, path: str) -> tuple[str, str] | None:
    ob, nb = blob(base, path), blob(head, path)
    if ob is None or nb is None:
        return None
    try:
        return ob.decode("utf-8"), nb.decode("utf-8")
    except UnicodeDecodeError:
        return None


def tags_of(text: str) -> list[str]:
    """every tag line of the text's docstrings, in order"""
    return [ln.strip() for kind, a, b in tg.scan(text) if kind == "doc" for ln in tag_lines(text[a + 3 : b - 2])]


def is_tag(base: str, head: str) -> bool:
    """The diff has the shape of a tag PR and every file is a tags-only change: classify.py names it `tag`. A file that changes more than tags is not a tag PR (it
    falls to the other classes, which judge it as what it is)."""
    files = changed_files(base, head)
    if not files:
        return False
    intake = intake_namespaces(base)
    for st, p in files:
        if st != "M" or not in_scope(p, intake):
            return False
        pair = texts(base, head, p)
        if pair is None or tags_of(pair[0]) == tags_of(pair[1]) or not tg.equivalent(*pair):  # the change must write (or replace) a tag
            return False
    return True


def tag_lines(doc_body: str) -> list[str]:
    return [ln for ln in doc_body.split("\n") if tg.TAG_LINE.match(ln)]


def doc_tag_errors(path: str, body: str, origin: str) -> tuple[list[str], int]:
    """The tags of one docstring: (what is wrong with them, how many there are). One at most, well formed, from where the module is, the last line of the docstring."""
    lines = tag_lines(body)
    errors = [f"{path}: a docstring with {len(lines)} tag lines"] if len(lines) > 1 else []
    last = [x for x in body.split("\n") if x.strip()][-1:]
    tags = 0
    for ln in lines:
        try:
            tag = isnad.parse_tag(ln)
        except ValueError as e:
            errors.append(f"{path}: {e}")
            continue
        tags += 1
        if tag["from"] != origin:
            errors.append(f"{path}: from={tag['from']} but the module is {origin} content")
        if last != [ln]:
            errors.append(f"{path}: the tag is not the last line of its docstring")
    return errors, tags


def tag_errors(path: str, text: str, before: str = "") -> list[str]:
    """What is wrong with the tags the file has (every docstring: `doc_tag_errors`); and the change must write or replace a tag."""
    origin = isnad.origin_of(module_of(path))
    errors: list[str] = []
    tags = 0
    for kind, a, b in tg.scan(text):
        if kind == "doc":
            more, n = doc_tag_errors(path, text[a + 3 : b - 2], origin)
            errors += more
            tags += n
    if not tags or tags_of(before) == tags_of(text):
        errors.append(f"{path}: the change writes no tag")
    return errors


def main(argv: list[str]) -> None:
    base, head = argv[1], argv[2]
    files = changed_files(base, head)
    intake = intake_namespaces(base)
    errors: list[str] = []
    if not files:
        errors.append("an empty diff")
    if len(files) > MAX_TAG_MODULES:
        errors.append(f"{len(files)} modules: a tag PR has at most {MAX_TAG_MODULES}")
    for st, p in files:
        if st != "M" or not in_scope(p, intake):
            errors.append(
                f"{p}: a tag PR only modifies existing modules of the seed, of Native or of a library that arrived as an intake bundle (status {st}; generated libraries and umbrella files are not tagged here)"
            )
            continue
        pair = texts(base, head, p)
        if pair is None:
            errors.append(f"{p}: not readable as UTF-8 at both commits")
        elif not tg.equivalent(*pair):
            errors.append(f"{p}: changes more than tags (code or docstring words differ once the tags are taken out)")
        else:
            errors += tag_errors(p, pair[1], pair[0])
    if errors:
        fail("tag PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
    print(f"tag ok: {len(files)} modules, only tags")


if __name__ == "__main__":
    main(sys.argv)
