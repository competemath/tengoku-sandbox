# Bulk attribution

Writes your credit into every declaration of a Lean project, so a project with
three hundred theorems does not need three hundred hand-written docstrings
before it is submitted.

## Use

```
python3 tools/attribute/attribute.py path/to/project \
  --credit "Author: Ada Lovelace (https://github.com/ada), with Claude Fable 5.1."
```

For every `theorem`, `lemma`, `def`, `abbrev`, `instance`, `structure`,
`inductive`, `class` and `opaque` under the directory (`.lake/` is skipped):

- a declaration with a docstring gets the credit as its last line;
- a declaration without one gets `/-- <credit> -/` above it (above its
  attributes, below any `open … in`);
- a declaration that already carries this credit is left as it is, so the tool
  can be run again after adding files;
- a declaration whose docstring names another author is left alone and listed,
  so nobody's credit is overwritten.

`--dry-run` prints what would change and writes nothing. `--kinds theorem,lemma`
restricts it. Commented-out code and `example`s are never touched. The tool
writes the credit only; a sentence on what each theorem says is still yours to
add.

## The credit line

One line, starting with `Author:` (`Authors:` for several), naming the human
author, the AI used if any, and a link to you: GitHub, LinkedIn, ORCID, or your
[CompeteMath ID](https://competemath.com/whoami).

```
Author: Ada Lovelace (https://github.com/ada), with Claude Fable 5.1.
Authors: Ada Lovelace (https://orcid.org/0000-0002-1825-0097), Charles Babbage (CompeteMath 7f3a9c1e).
```

The word matters. `Author:` is what the tree's checks key on: `tools/harvest.py`
keeps a docstring carrying it with the theorem's statement (other docstrings
stay at `source_url`), and the credits check fails any pull request that
removes or edits the line afterwards.

## Where it ends up

The docstring is the first lines of the record's `statement`
(`data/staging/<library>/<file>.jsonl`, see [CONTRIBUTING.md](../../CONTRIBUTING.md)).
The generator writes the statement verbatim into the tree's module, promotion
moves the record unchanged, and the module is regenerated from it. Writing
records by hand, put the docstring at the top of `statement` yourself.
