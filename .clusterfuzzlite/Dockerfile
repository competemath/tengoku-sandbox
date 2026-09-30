# ClusterFuzzLite's build of the gate's fuzz targets (.github/workflows/fuzz.yml; docs/testing.md, "Fuzzing").
# The OSS-Fuzz Python builder (atheris, PyInstaller), pinned by digest.
FROM gcr.io/oss-fuzz-base/base-builder-python@sha256:79cc75a68ab65120da54f35d53f10c7536554ffe684eea5bae078a9a5ff82923
COPY . $SRC/tengoku
WORKDIR $SRC/tengoku
COPY .clusterfuzzlite/build.sh $SRC/
