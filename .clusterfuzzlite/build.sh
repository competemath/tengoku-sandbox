#!/bin/bash -eu
# Packs each fuzz target (scripts/ci/fuzz/fuzz_*.py) with the gate scripts and schemas it reads, and its corpus as
# the seed corpus. The same targets run on pull requests and in the merge queue (scripts/ci/fuzz/run.py).
pip3 install --require-hashes --only-binary :all: -r scripts/ci/requirements/yaml.txt
for target in scripts/ci/fuzz/fuzz_*.py; do
  name="$(basename "$target" .py)"
  compile_python_fuzzer "$target" --paths scripts/ci --paths scripts/ci/fuzz \
    --add-data scripts/ci:scripts/ci --add-data schemas:schemas
  corpus="scripts/ci/fuzz/corpus/${name#fuzz_}"
  [ -d "$corpus" ] && (cd "$corpus" && zip -q -r "$OUT/${name}_seed_corpus.zip" .)
done
