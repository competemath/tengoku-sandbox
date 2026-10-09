# Agent security

Every AI agent that writes to Tengoku is treated as an untrusted party. It reads text that anyone can write, so it can be talked into things;
it holds credentials, so it can leak them; it opens pull requests, so it can touch what it should not. Prompts are guidance, not a boundary.
The checks on this page are the part that is code: they run on main's copy of the scripts, read the pull request only as git objects, and
say what they saw.

The toolkit behind them is [tengoku-warden](https://github.com/competemath/tengoku-warden), vendored here (below). It exists because the
[Tau Ceti project](https://github.com/TauCetiProject) published, with dates, what it takes to run a library that AI agents write and review,
and where that went wrong before it went right. Everything it learned from them, and what we did differently, is in
[warden's `docs/TAU-CETI.md`](https://github.com/competemath/tengoku-warden/blob/8e78f4f1e2b204f7c81da3b155d54e7502086420/docs/TAU-CETI.md);
what remains unsolved is in its [`SECURITY.md`](https://github.com/competemath/tengoku-warden/blob/8e78f4f1e2b204f7c81da3b155d54e7502086420/SECURITY.md).
The credit for the ideas belongs to the people who wrote them down, above all Kim Morrison. We copied no code and no prose.

## What runs

| Check | Where | Blocks? | What it protects |
| --- | --- | --- | --- |
| `scope` (this page, section 1) | `agent-guard.yml`, every pull request | no, advisory | agent PRs stay in their paths; no symlink, submodule or executable under `data/` or `Tengoku/`; no secret in a PR's title, body, commit messages or added lines; no human-owned work dropped by an agent's push; CODEOWNERS and the policy agree |
| sealed-step self-test (section 2) | first command inside the sealed step of `pr-gate.yml` (vacuity); `pr-tests.yml` runs the same battery on a hosted runner | yes for eight probes: a step that fails one does not start; four probes that are open on a hosted runner are named advisories until `seal_harden.sh` is adopted | the PR's Lean runs with no network, no sight of the runner, no credentials |
| vendored warden modules (section 3) | `scripts/ci/warden/`, tested for drift | yes (tooling tests) | the code the checks use is the code that was reviewed |

## 1. The `scope` check

`.github/workflows/agent-guard.yml` runs on `pull_request_target` (main's copy of the workflow and of the scripts; the PR is fetched as git
objects and never checked out or run). It is a separate file from `pr-gate.yml`, like `sonar.yml`, so the gate's carefully tuned `needs` list
is untouched and the merge queue never waits for it. Two jobs, as in the trust-shadow workflow: `guard` holds a read token, judges the PR
with `scripts/ci/agent_guard.py check` and uploads `result.json`; `publish` holds `checks: write` and nothing else, takes only that file after
`validate_result` has checked its shape (fixed words, bounded plain text), and posts the check run named **`scope`**
(`success`, `neutral` when something could not be verified, `failure` when there are findings). The same text is in the job summary.

What it checks:

1. **Scope of agent PRs.** A PR is an agent PR when it comes from a bot account (`tengoku-bot`, `dependabot[bot]`, any login ending `[bot]`,
   or a user of type `Bot`), when the account named by the repository variable `TENGOKU_BOT` opens a PR that `classify.py` gives one of the factory's
   classes (promotion, intake, extend, tag, native, scope-fix, restructure), or when the branch or title is worded as the factory's are (`intake/…`,
   `promote/…`, `isnad/…`, `scopefix-…`, `intake: …`, `scope fix: …`). In the sandbox `TENGOKU_BOT` is a person, so that person's tooling PRs are not agent PRs; their
   promotions are. The PR is then held to the class it fell in, from `scripts/ci/agent-paths.json`:
   - `factory`: `data/tentative/`, `data/staging/`, `data/trusted/`, `data/intake/`, `data/stats.json`, `data/cache-latest.json`, `Tengoku/`. Nothing under `scripts/`,
     `.github/`, `schemas/`, the lakefile, the manifest, the toolchain, `pyproject.toml`, the pre-commit configuration or the root Lean files; those are listed as protected, and the
     class may not touch protected paths. A restructure PR is the one exception: `restructure_check.py` recomputes it byte for byte, so the path rule is not applied to it.
   - `dependabot`: `.github/workflows/*.yml` and `scripts/ci/requirements/*.txt` (what `.github/dependabot.yml` updates).
   - any other bot: nothing.
   - for all of them: file mode `100644` only, at most 2000 files, 400,000 added and 200,000 deleted lines, no new module of more than 20,000 lines, no binary file.
     The caps are runaway guards sized from the largest intake bundle so far (403 files, 131,303 added lines), not review limits; tune them in the file.
2. **Modes, for every PR.** No symlink (`120000`), submodule (`160000`) or executable (`100755`) is added under `data/` or `Tengoku/`, or changed into one.
   Checked in the repository before this: the content lint and the record validator read file contents, not git modes, and `restructure_check.py`
   compares modes only for its own class. A symlink in a bot PR is found twice: by this rule and by the scope policy's mode list.
3. **Secrets in what the agent publishes.** `warden.secretscan` reads the PR title, the body, every commit message and the lines the PR adds outside
   `data/` and `Tengoku/` (TruffleHog and detect-secrets read the files; a PR's metadata is what an agent also publishes). The pragma
   `pragma: allowlist secret` hides nothing in metadata. Findings name the kind and the place (`commit 1a2b3c4d5e6f`, `PR body`, `file:line`); the secret is never printed, not even a prefix.
   Lines that carry the pragma are counted in a notice.
4. **Dropped human-owned work.** On a push (`synchronize`, with the event's `before`), if the push was made by an agent, `warden.scope.dropped_human_owned` compares the previous head with the new
   head over the paths humans own (`.github/agent-paths.json` of the base) and reports those the PR itself changes. This sees what the base-to-head diff cannot: a revert to the base shows as no
   change at all. An *agent* push is one by a bot account, or one whose commits carry an AI co-author trailer (`Co-Authored-By: Claude …`, `Generated with Claude Code`).
   A bot updating its own PR is not judged; a force-push that removed the previous head is a notice (`neutral`), never a pass.
5. **Ownership divergence.** `warden.ownership.divergence` compares `.github/CODEOWNERS` with `.github/agent-paths.json`, using CODEOWNERS' real rules (last match wins, `*`, `**`, a
   leading and a trailing `/`), and checks that the scope policy lies inside the ownership policy (what it protects is human-owned; a class that may not touch protected paths is not
   allowed to write one). Both files are read from the PR's head, so a PR that edits either must keep them in step.

### The two policy files

- `.github/agent-paths.json` is the single source of who owns what: `human` is the list of globs the repository's CODEOWNERS gives to the maintainers, `agent` the globs that
  have no code owner. CODEOWNERS here has no `*` default rule, so everything not listed is ownerless, which the policy says with `"agent": ["*"]`. `review` is empty: no path
  is yet one that the AI review may stand in for a human on.
- `scripts/ci/agent-paths.json` is the scope policy of section 1, in `warden.scope`'s format.

`warden.ownership` compares one owner per rule; this repository's rules name two accounts (either one's approval counts). `agent_guard.py` therefore rewrites every rule whose owners are
exactly the two human accounts into one before comparing; a rule with only one of them is a divergence, as it should be. To run it by hand:

```bash
python3 scripts/ci/agent_guard.py ownership
python3 scripts/ci/agent_guard.py check --repo . --base <base sha> --head <head sha> --out /tmp/guard   # then read /tmp/guard/summary.md
```

### Making it required

It is advisory until the maintainer decides otherwise (tengoku-warden `docs/RUNBOOK.md`, items 2 and 4). A required status check that names no integration can be set by any identity
with write access, which is a hole Tau Ceti's own rulesets show. The check run is made by the Actions identity (app id 15368); a ruleset that requires `scope` should pin that
`integration_id`, or the id of a dedicated App if one is created.

## 2. The sealed-step self-test

The gate compiles the PR's records in a "sealed" step: `unshare --net --pid --fork --mount-proc runuser -u <user> -- env -i …`. That line is only as good as the runner it runs on.
`scripts/ci/sandbox_selftest.py` is the first command inside it: it probes, from inside, what must be denied, prints `ok` or `FAIL` and what it saw (never the value of a variable), and
exits 1 before the PR's code starts if any probe says the step is not sealed. With a command after `--` it then replaces itself with that command.

| Probe | Must hold |
| --- | --- |
| `unprivileged` | not root, no effective capability |
| `no_network_testnet` | a connection to 192.0.2.1 fails for want of a route (a timeout is not a seal: nothing answers there either way) |
| `no_network_named_host` | `api.github.com` and 1.1.1.1 cannot be reached |
| `no_metadata_service` | 169.254.169.254 cannot be reached |
| `own_pid_namespace` | few processes are visible, and pid 1 is not the runner's init or a runner process |
| `pid1_environment` | `/proc/1/environ` is unreadable, or holds only allowed names |
| `environment_empty` | only the allowed variables, and nothing named like a credential or the runner's state |
| `cannot_write_system` | nothing can be created under `/`, `/etc`, `/usr`, `/bin`, `/opt`, `/var/lib` |
| `cannot_write_runner_channels` | the files a step appends to for `GITHUB_ENV`, `GITHUB_PATH`, `GITHUB_OUTPUT`, and the code of the downloaded actions, are not writable |
| `cannot_read_runner_credentials` | the runner's credential files and a home directory's usual token files are not readable (a Docker config only when it holds a registry credential) |
| `no_container_socket` | the Docker, containerd and Podman sockets cannot be connected to (a unix socket is addressed by path, so a network namespace does not stop it) |
| `scratch_writable` | `/tmp` and the working directory are writable, so the sealed command can still work |

**What the first run on a hosted runner found (2026-10-09, `ubuntu-latest`, the `sealed-selftest` job of this pull request).** Inside the gate's own seal, the network, PID-namespace, `/proc/1`,
privilege and environment probes pass: the seal does what it says. Four probes do not, and all four are about the one thing the seal does not change, the user: a sealed step runs as the runner's own user.

| Open probe | What the sealed step can do | Why it matters |
| --- | --- | --- |
| `no_container_socket` | connect to `/var/run/docker.sock` | a unix socket is addressed by path, so a network namespace does not stop it; a container started through it has the host's network and, with a bind mount, the host's disk, as root: no network, no PID namespace, no environment scrub is left |
| `cannot_write_runner_channels` | append to the files `GITHUB_ENV`, `GITHUB_PATH`, `GITHUB_OUTPUT` are read from, and change the code of the downloaded actions | the steps after it, including the post step of every action, run with the job's token and read those files and run that code |
| `cannot_write_system` | create files in `/usr/local/bin` and `/opt` | both are on the `PATH` of every later step |
| `cannot_read_runner_credentials` | read `~/.docker/config.json` (only flagged when it holds a registry credential) | the Docker client's credential file |

None of this is an attack on the job's own token (the vacuity job holds `contents: read`) but each is a way out of "it can reach neither the cache service nor a token" (the comment of
the vacuity step). `scripts/ci/seal_harden.sh` closes all four for the sealed step only: run as root inside the same `unshare`, in a mount namespace of its own, it replaces the container
sockets and the Docker config with `/dev/null`, empties the command-file directory, makes the downloaded actions, `/usr/local/bin` and `/opt` read-only, and then drops to the user and runs the command.
`pr-tests.yml` runs the battery inside it with no probe excused, and checks that the job still reaches Docker afterwards.

**Wiring.** `pr-gate.yml`'s vacuity step runs `sandbox_selftest.py --allow-env TENGOKU_CI_ROOT -- python3 scripts/ci/vacuity.py …` inside the seal, with the four open probes named as advisories
(`--advisory`): each run prints them as warnings and the gate does not stop on them. Closing them is one edit, which the maintainer makes after running it in the sandbox: put
`sh scripts/ci/seal_harden.sh "$(id -un)" --` in place of `runuser -u "$(id -un)" --` and delete the four flags. I did not make that edit myself because it changes the command that compiles the PR's
records, and nothing here can run Lean to prove the compile still works inside the narrower seal. **A change to `pr-gate.yml` takes effect only after it is merged** (`pull_request_target` runs
main's copy), so the first real run of the self-test in the gate is the first content PR after the merge. The nightly build (`build.yml`) has a seal of the same shape and is not wired here.
`jinshi-pr.yml` is open as a pull request while this is written and is not on `main`; when it lands, its sealed step gets the same change:

```diff
-            python3 scripts/ci/jinshi_check.py "$BASE" "$HEAD"
+            python3 scripts/ci/sandbox_selftest.py --allow-env TENGOKU_CI_ROOT --allow-env JINSHI_PR_TARGETS \
+              --advisory cannot_write_system --advisory cannot_write_runner_channels --advisory cannot_read_runner_credentials --advisory no_container_socket \
+              -- python3 scripts/ci/jinshi_check.py "$BASE" "$HEAD"
```

`--advisory PROBE` turns a known gap into a warning printed on every run. Use it only with the reason written beside the workflow line.

Credit: the idea of a self-test that aborts the job when the sandbox is not enforcing is Tau Ceti's: the nine-probe bubblewrap self-test of `pr-build.yml` (their PR 5800, 2026-09-06; no write to `/` or
`/etc`, no read of a host canary, no network, no nested user namespace, a different user namespace, an empty PID-1 environment), and the `/proc/1/environ` leak that taught them `env -i`.
Ours is independent code for a different seal (namespaces and `runuser`, not bubblewrap) that also looks for what bypasses a network and PID namespace on a hosted runner.

## 3. The vendored warden modules

`scripts/ci/warden/` holds `scope`, `secretscan`, `ownership`, `eligibility`, `safegit` and `__init__` of tengoku-warden, byte for byte. `PIN` names the warden commit and the sha256 of each
file in `sha256sum -c` format; `scripts/ci/tests/test_warden_vendor.py` fails when a file differs from its hash, when a module has no pin, or when pins name different commits. To refresh, change the
code in tengoku-warden, copy the file here and update `PIN`; never edit a copy. The folder is excluded from ruff, coverage and Sonar (its tests live in warden). `agent_guard.py` imports it as
`warden`, from the script's own directory, as `trust_shadow.py` imports `trust_vendor`.

## What this does not do

- It cannot tell which agent works through a person's account: an agent that pushes as `mikael-bashir` is a bot only if its commits say so (a co-author trailer), and a trailer can be left off.
- The secret scan is a heuristic filter: encoded or split secrets and secrets without a recognisable shape are not found.
- Section 1 is advisory. Until it is required, pinned to the App that makes it, nothing stops a merge.
- The seal is a network and PID namespace and an empty environment, run as the runner's own user; it is not a virtual machine, and a kernel escape defeats it. The self-test tells what it probes:
  a pass proves those vectors are closed on this runner today.
- Moving `scope` to a dedicated App, and the other settings only a maintainer can change, are in tengoku-warden `docs/RUNBOOK.md`.
