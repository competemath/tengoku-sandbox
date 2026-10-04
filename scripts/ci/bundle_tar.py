#!/usr/bin/env python3
"""bundle_tar.py DIR OUT.tar — the canonical archive of a factory bundle: one function, written the same in competemath/emissary-archangel
(scripts/bump/bundle_tar.py) and here, pinned by the same golden digest in both test suites.

The factory attests the archive it built; the gate rebuilds the archive from the files of the intake PR and checks the attestation against
those bytes. So the bytes must not depend on the machine: regular files only, sorted by name, owner 0, mode 0644, time 0, GNU format
(not the tar program, whose flags differ between systems, and not PAX, whose headers differ between Python versions)."""

from __future__ import annotations

import hashlib
import io
import os
import sys
import tarfile
import tempfile
from pathlib import Path


def checked_output(out: str) -> str:
    """The archive is written inside the working directory or a temporary directory (the runner's too), never anywhere a `..` or a symlink
    could lead: the real path of the destination must be under one of them."""
    real = os.path.realpath(out)
    roots = [os.path.realpath(r) for r in (os.getcwd(), tempfile.gettempdir(), os.environ.get("RUNNER_TEMP", "")) if r]
    if not any(real.startswith(r + os.sep) for r in roots):
        raise ValueError(f"{out}: the archive is written inside the working directory or a temporary directory only")
    return real


def write_tar(files: dict[str, bytes], out: str) -> str:
    dest = checked_output(out)
    with open(dest, "wb") as f:
        with tarfile.open(fileobj=f, mode="w", format=tarfile.GNU_FORMAT) as tf:
            for name in sorted(files):
                ti = tarfile.TarInfo(name)
                ti.size, ti.mtime, ti.mode, ti.uid, ti.gid, ti.uname, ti.gname = len(files[name]), 0, 0o644, 0, 0, "", ""
                tf.addfile(ti, io.BytesIO(files[name]))
    return hashlib.sha256(Path(dest).read_bytes()).hexdigest()


def read_dir(d: str) -> dict[str, bytes]:
    """The regular files under `d`. A symlink is never followed (the directory may come from a job that ran code of a library)."""
    root = Path(d).resolve()
    return {
        str(p.relative_to(root)): p.read_bytes()
        for p in sorted(root.rglob("*"))
        if p.is_file() and not p.is_symlink() and root in p.resolve().parents
    }


if __name__ == "__main__":
    print(write_tar(read_dir(sys.argv[1]), sys.argv[2]))
