"""zenodo_deposit.py against a fake Zenodo: the first version creates the record, later ones are new versions of it
(the previous files replaced, not kept), and a version Zenodo already has is not deposited twice."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TITLE = "Tengoku: a test record"


class FakeZenodo:
    def __init__(self):
        self.deps: dict[int, dict] = {}
        self.next = 100
        self.calls: list[str] = []
        fake = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *a):
                pass

            def reply(self, code, obj=None):
                body = json.dumps(obj).encode() if obj is not None else b""
                self.send_response(code)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def body(self):
                return self.rfile.read(int(self.headers.get("Content-Length") or 0))

            def handle_any(self, method):
                fake.calls.append(f"{method} {self.path.split('?')[0]}")
                if self.headers.get("Authorization") != "Bearer secret":
                    return self.reply(401, {"message": "no token"})
                return self.reply(*fake.route(method, self.path, self.body()))

            def do_GET(self):
                self.handle_any("GET")

            def do_POST(self):
                self.handle_any("POST")

            def do_PUT(self):
                self.handle_any("PUT")

            def do_DELETE(self):
                self.handle_any("DELETE")

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.url = f"http://127.0.0.1:{self.server.server_port}"
        threading.Thread(target=self.server.serve_forever, daemon=True).start()

    def new_draft(self, concept: int | None, files: list[dict]) -> dict:
        i = self.next
        self.next += 1
        d = {
            "id": i,
            "concept": concept or i,
            "submitted": False,
            "metadata": {},
            "files": [dict(f, links={"self": f"{self.url}/files/{i}/{f['filename']}"}) for f in files],
            "links": {
                "self": f"{self.url}/api/deposit/depositions/{i}",
                "bucket": f"{self.url}/bucket/{i}",
                "publish": f"{self.url}/api/deposit/depositions/{i}/actions/publish",
                "latest": f"{self.url}/api/records/{i}",
            },
        }
        self.deps[i] = d
        return d

    def route(self, method: str, path: str, body: bytes):
        p = path.split("?")[0]
        if method == "GET" and p == "/api/deposit/depositions":
            return 200, sorted(self.deps.values(), key=lambda d: -d["id"])
        if method == "POST" and p == "/api/deposit/depositions":
            return 201, self.new_draft(None, [])
        m = re.fullmatch(r"/bucket/(\d+)/(.+)", p)
        if method == "PUT" and m:
            d = self.deps[int(m.group(1))]
            d["files"].append({"filename": m.group(2), "size": len(body), "links": {"self": f"{self.url}/files/{d['id']}/{m.group(2)}"}})
            return 201, {"key": m.group(2)}
        m = re.fullmatch(r"/files/(\d+)/(.+)", p)
        if method == "DELETE" and m:
            d = self.deps[int(m.group(1))]
            d["files"] = [f for f in d["files"] if f["filename"] != m.group(2)]
            return 204, None
        m = re.fullmatch(r"/api/deposit/depositions/(\d+)", p)
        if m and method == "GET":
            return 200, self.deps[int(m.group(1))]
        if m and method == "PUT":
            self.deps[int(m.group(1))]["metadata"] = json.loads(body)["metadata"]
            return 200, self.deps[int(m.group(1))]
        m = re.fullmatch(r"/api/deposit/depositions/(\d+)/actions/publish", p)
        if m:
            d = self.deps[int(m.group(1))]
            d["submitted"], d["doi"] = True, f"10.5072/zenodo.{d['id']}"
            d["metadata"]["doi"] = d["doi"]
            return 202, d
        m = re.fullmatch(r"/api/records/(\d+)", p)
        if m:
            concept = self.deps[int(m.group(1))]["concept"]
            newest = max(i for i, d in self.deps.items() if d["concept"] == concept and d["submitted"])
            return 200, {"id": newest}
        m = re.fullmatch(r"/api/deposit/depositions/(\d+)/actions/newversion", p)
        if m:
            old = self.deps[int(m.group(1))]
            draft = self.new_draft(old["concept"], [{"filename": f["filename"], "size": f["size"]} for f in old["files"]])
            return 201, {**old, "links": {**old["links"], "latest_draft": draft["links"]["self"]}}
        return 404, {"message": f"no route {method} {p}"}


class ZenodoDeposit(unittest.TestCase):
    def setUp(self):
        self.z = FakeZenodo()
        self.dir = Path(tempfile.mkdtemp())
        (self.dir / "meta.json").write_text(json.dumps({"title": TITLE, "upload_type": "dataset", "creators": [{"name": "T"}]}))

    def tearDown(self):
        self.z.server.shutdown()

    def deposit(self, version: str, files: dict[str, str], token: str = "secret"):
        paths = []
        for name, text in files.items():
            (self.dir / name).write_text(text)
            paths.append(str(self.dir / name))
        env = {**os.environ, "ZENODO_URL": self.z.url, "ZENODO_TOKEN": token}
        args = ["--metadata", str(self.dir / "meta.json"), "--version", version, "--date", "2026-10-01"]
        args += ["--related", f"https://github.com/x/y/releases/tag/v{version}"]
        return subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "zenodo_deposit.py"), *args, *paths], capture_output=True, text=True, env=env
        )

    def test_first_version_then_a_new_version_then_no_duplicate(self):
        r = self.deposit("1.0.0", {"snapshot.json": "{}", "data.gz": "a"})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(r.stdout.strip(), "10.5072/zenodo.100")
        first = self.z.deps[100]
        self.assertEqual(first["metadata"]["version"], "1.0.0")
        self.assertEqual(first["metadata"]["publication_date"], "2026-10-01")
        self.assertEqual(first["metadata"]["related_identifiers"][0]["relation"], "isIdenticalTo")
        self.assertEqual(sorted(f["filename"] for f in first["files"]), ["data.gz", "snapshot.json"])

        r = self.deposit("1.1.0", {"snapshot.json": "{}", "data2.gz": "b"})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(r.stdout.strip(), "10.5072/zenodo.101")
        second = self.z.deps[101]
        self.assertEqual(second["concept"], 100)  # a new version of the same record
        self.assertEqual(sorted(f["filename"] for f in second["files"]), ["data2.gz", "snapshot.json"])  # the old file went
        self.assertEqual(second["metadata"]["version"], "1.1.0")

        calls = len(self.z.calls)
        r = self.deposit("1.1.0", {"snapshot.json": "{}", "data2.gz": "b"})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(r.stdout.strip(), "10.5072/zenodo.101")
        self.assertIn("already on Zenodo", r.stderr)
        self.assertEqual(len(self.z.deps), 2)
        self.assertTrue(all(c.startswith("GET") for c in self.z.calls[calls:]))  # looked, changed nothing

    def test_no_token_is_an_error(self):
        r = self.deposit("1.0.0", {"snapshot.json": "{}"}, token="")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("no ZENODO_TOKEN", r.stderr)

    def test_a_refused_request_is_an_error(self):
        r = self.deposit("1.0.0", {"snapshot.json": "{}"}, token="wrong")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("HTTP 401", r.stderr)


if __name__ == "__main__":
    unittest.main()
