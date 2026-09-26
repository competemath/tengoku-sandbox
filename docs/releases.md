# Releases

A release is a version of the library you can pin, verify and build on. It is cut by
`.github/workflows/release.yml` from a commit of `main` that the nightly build has already compiled and
published, so every release comes with a compiled cache built from exactly its commit.

| Asset | What it is |
| --- | --- |
| `tengoku-<v>-source.tar.gz` | The buildable tree at the release commit: `Tengoku/`, the root modules, the Lake and toolchain files, the licences and `SEED.md`. |
| `tengoku-<v>.cdx.json` | The bill of materials (CycloneDX 1.5): the Lean toolchain, every package the tree was seeded from, and every library whose records the tree holds, each with its exact commit and licence. |
| `tengoku-<v>-cache.json` | The compiled cache built from the release commit: its release tag and the SHA-256 digest of each part. |
| `CHANGELOG-<v>.md` | The PRs merged since the previous release. |

## Verifying a release

Every asset carries a build-provenance attestation, signed through GitHub's Sigstore instance by the release
workflow on this repository. The bill of materials also carries an SBOM attestation bound to the source archive.
With the [GitHub CLI](https://cli.github.com/):

```bash
v=v0.1.0
gh release download "$v" -R competemath/tengoku
for f in tengoku-$v-source.tar.gz tengoku-$v.cdx.json tengoku-$v-cache.json CHANGELOG-$v.md; do
  gh attestation verify "$f" -R competemath/tengoku --signer-workflow competemath/tengoku/.github/workflows/release.yml
done
gh attestation verify tengoku-$v-source.tar.gz -R competemath/tengoku --predicate-type https://cyclonedx.org/bom
```

A file that was changed after the release, or published by anything other than the release workflow, fails.

## Using the compiled cache

The cache parts are assets of the release named in `tengoku-<v>-cache.json`. Each part has its own build-provenance
attestation from the nightly build (`.github/workflows/build.yml`), and its digest must match the manifest:

```bash
tag=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["cache"])' "tengoku-$v-cache.json")
gh release download "$tag" -R competemath/tengoku -p 'tengoku-cache.tar.zst.part-*'
for f in tengoku-cache.tar.zst.part-*; do
  gh attestation verify "$f" -R competemath/tengoku --signer-workflow competemath/tengoku/.github/workflows/build.yml
done
python3 - "tengoku-$v-cache.json" <<'PY'
import hashlib, json, sys
m = json.load(open(sys.argv[1]))
for p in m["parts"]:
    got = "sha256:" + hashlib.sha256(open(p["name"], "rb").read()).hexdigest()
    assert got == p["digest"], f"{p['name']}: {got} is not {p['digest']}"
print("every part matches the manifest")
PY
checkout=path/to/your/tengoku/checkout   # a checkout of the release commit
mkdir -p "$checkout/.lake"
cat tengoku-cache.tar.zst.part-* | zstd -d | tar -x -C "$checkout/.lake"
```

`scripts/cache.sh get` does the same for a checkout of the repository, and refuses parts without an attestation
when `TENGOKU_VERIFY=require`.

## What a release does and does not promise

It promises that the files are exactly what the release workflow produced from the named commit of `main`, that
the cache was compiled from that commit by the nightly build, and that the bill of materials lists what the tree
was made from. The commit itself passed every gate on its way to `main`. The nightly build and the independent
check (`.github/workflows/independent-check.yml`) compile and re-check the tree; a release does not by itself re-run
them.
