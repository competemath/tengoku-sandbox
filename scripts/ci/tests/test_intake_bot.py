"""The intake App (tengoku-intake) opens intake and extend PRs for the factory, unattended (the factory's scripts/bump/intake_open.py). classify.py lets its account send exactly those
two classes. Everything else that asks for the bot's account (a promotion, a tag, a scope fix, a restructure) stays the bot's. Its own file, like test_extend.py."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import test_extend as ex  # noqa: E402  (the module, not its test class: importing the class would run its tests again here)
from test_gates import Repo  # noqa: E402

APP = {"PR_ACTOR": "tengoku-intake[bot]", "TENGOKU_BOT": "tengoku-bot"}


class IntakeApp(unittest.TestCase):
    def first_part(self):
        r = ex.Extend().repo(with_library=False)
        r.write("Tengoku/FxLib/Fx/A.lean", ex.module("a"))
        r.write("Tengoku/FxLib.lean", f"import {ex.Extend.A}\n")
        r.write("data/intake/fx-lib/manifest.jsonl", ex.record("a", ex.Extend.A))
        r.write("data/intake/fx-lib/report.json", json.dumps({"library": "fx-lib", "part": 1}) + "\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("part 1")
        return r

    def test_the_app_may_send_a_first_part(self):
        rc, out = self.first_part().gate("classify.py", env=APP)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=intake", out)

    def test_the_app_may_send_the_next_part(self):
        e = ex.Extend()
        r = e.repo()
        e.part2(r)
        rc, out = r.gate("classify.py", env=APP)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=extend", out)

    def test_anyone_else_may_not(self):
        for actor in ("someone", "other-app[bot]", ""):
            rc, out = self.first_part().gate("classify.py", env={"PR_ACTOR": actor, "TENGOKU_BOT": "tengoku-bot"})
            self.assertNotEqual(rc, 0, actor)
            self.assertIn("factory's account", out)

    def test_the_account_is_configurable(self):
        env = {"PR_ACTOR": "renamed-app[bot]", "TENGOKU_BOT": "tengoku-bot", "TENGOKU_INTAKE_BOT": "renamed-app[bot]"}
        self.assertEqual(self.first_part().gate("classify.py", env=env)[0], 0)
        self.assertNotEqual(
            self.first_part().gate("classify.py", env=APP | {"TENGOKU_INTAKE_BOT": "renamed-app[bot]"})[0], 0
        )  # the default is replaced, not added to

    def test_the_app_may_not_promote(self):
        # a promotion (derived files plus content, the promote bot's class) is granted by the bot's account only
        r = Repo()
        r.append("data/trusted/lib.jsonl", "\n")
        r.append("Tengoku/Lib/Basic.lean", "-- regenerated\n")
        r.commit("promote")
        self.assertEqual(r.gate("classify.py", env={"PR_ACTOR": "tengoku-bot", "TENGOKU_BOT": "tengoku-bot"})[0], 0)
        rc, out = r.gate("classify.py", env=APP)
        self.assertNotEqual(rc, 0, out)


if __name__ == "__main__":
    unittest.main()
