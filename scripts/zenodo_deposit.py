#!/usr/bin/env python3
"""zenodo_deposit.py --metadata FILE --version X.Y.Z --date YYYY-MM-DD [--related URL] FILE... — a DOI for one release.

Deposits the files on Zenodo as version X.Y.Z of the record whose title is the metadata's, through Zenodo's REST
API with ZENODO_TOKEN (scopes deposit:write and deposit:actions): the first version creates the record, later ones
are new versions of it (one concept DOI for all of them). Only the snapshot workflow calls this, and only for a
vX.Y.Z release: Zenodo's GitHub integration would mint a DOI for every release, the nightly cache ones included.

A version Zenodo already has is not deposited again. Prints the version's DOI. ZENODO_URL chooses the server
(https://sandbox.zenodo.org to try it out)."""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

URL = os.environ.get("ZENODO_URL", "https://zenodo.org").rstrip("/")
TOKEN = os.environ.get("ZENODO_TOKEN", "")


def call(method: str, url: str, body: bytes | dict | None = None, raw: bool = False) -> dict:
    if not url.startswith("http"):
        url = URL + url
    data, headers = None, {"Authorization": f"Bearer {TOKEN}", "Accept": "application/json"}
    if isinstance(body, dict):
        data, headers["Content-Type"] = json.dumps(body).encode(), "application/json"
    elif body is not None:
        data, headers["Content-Type"] = body, "application/octet-stream"
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=600) as r:
            text = r.read()
    except urllib.error.HTTPError as e:
        sys.exit(f"zenodo: {method} {url.split('?')[0]}: HTTP {e.code}: {e.read()[:500].decode(errors='replace')}")
    return {} if raw or not text else json.loads(text)


def mine(title: str) -> list[dict]:
    """This account's depositions of the record: every version, published or draft, whose title is exactly `title`."""
    q = urllib.parse.urlencode({"q": f'title:"{title}"', "size": 100, "sort": "mostrecent"})
    return [d for d in call("GET", f"/api/deposit/depositions?{q}") or [] if d.get("metadata", d).get("title") == title]


def deposit(meta: dict, version: str, date: str, related: str | None, files: list[Path]) -> str:
    title = meta["title"]
    found = mine(title)
    for d in found:
        if d.get("submitted") and d.get("metadata", {}).get("version") == version:
            print(f"version {version} is already on Zenodo", file=sys.stderr)
            return d.get("doi") or d["metadata"].get("doi", "")
    published = [d for d in found if d.get("submitted")]
    if published:
        latest = call("GET", published[0]["links"]["latest"])  # the newest published version of the record
        draft = call("POST", f"/api/deposit/depositions/{latest['id']}/actions/newversion")["links"]["latest_draft"]
        draft = call("GET", draft)
        for f in draft.get("files", []):  # a new version starts with the previous one's files
            call("DELETE", f["links"]["self"], raw=True)
    else:
        draft = call("POST", "/api/deposit/depositions", {})
    bucket = draft["links"]["bucket"]
    for f in files:
        call("PUT", f"{bucket}/{urllib.parse.quote(f.name)}", f.read_bytes())
    metadata = {**meta, "version": version, "publication_date": date}
    if related:
        metadata["related_identifiers"] = [
            *meta.get("related_identifiers", []),
            {"identifier": related, "relation": "isIdenticalTo", "scheme": "url"},
        ]
    call("PUT", draft["links"]["self"], {"metadata": metadata})
    done = call("POST", draft["links"]["publish"])
    return done.get("doi") or done.get("metadata", {}).get("doi", "")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--metadata", required=True, help="Zenodo metadata (title, upload_type, creators, description, license, …)")
    ap.add_argument("--version", required=True)
    ap.add_argument("--date", required=True)
    ap.add_argument("--related", help="the GitHub release this deposit is identical to")
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    if not TOKEN:
        sys.exit("zenodo: no ZENODO_TOKEN")
    meta = json.loads(Path(args.metadata).read_text(encoding="utf-8"))
    print(deposit(meta, args.version, args.date, args.related, [Path(f) for f in args.files]))


if __name__ == "__main__":
    main()
