#!/bin/sh
# seal_harden.sh USER -- COMMAND [ARGS...] — what a network and PID namespace leaves open on a hosted runner, closed for this step only.
#
# Run as root inside `unshare --net --pid --fork --mount-proc` (so in a mount namespace of its own: nothing mounted here is seen by the rest of the
# job), it hides or freezes what scripts/ci/sandbox_selftest.py found reachable from a sealed step of the runner's own user, then drops to USER and runs
# COMMAND:
#   - the Docker, containerd and Podman sockets: a unix socket is addressed by path, so a network namespace does not stop a connection to one, and a
#     container started through it has the host's network and, with a bind mount, the host's disk. Replaced by /dev/null.
#   - the runner's command files (GITHUB_ENV, GITHUB_PATH, GITHUB_OUTPUT) and the downloaded actions: the sealed step runs as the runner's user, who owns
#     them, and the steps after it (the post steps of every action) run with the job's token. The first is emptied, the second made read-only.
#   - /usr/local/bin and /opt, which the hosted image makes writable and which are on every later step's PATH: read-only.
#   - the Docker client's credential file: replaced by /dev/null.
# A path that does not exist is skipped; a mount that fails stops the step (fail closed).
#
# Credit: Tau Ceti Project's bubblewrap seal (--tmpfs / with read-only binds, PR 5800, 2026-09-06) is the model of a seal built from read-only binds; this is
# the same idea for the namespace seal the gate already uses, narrower on purpose: it closes what the self-test showed open and nothing else.
set -eu
[ "$(id -u)" = 0 ] || { echo "seal_harden: run it as root inside unshare" >&2; exit 2; }
[ "$#" -ge 3 ] && [ "$2" = "--" ] || { echo "usage: seal_harden.sh USER -- COMMAND [ARGS...]" >&2; exit 2; }
user=$1
shift 2

hide() { [ -e "$1" ] && mount --bind /dev/null "$1"; return 0; }
freeze() { [ -d "$1" ] && { mount --bind "$1" "$1" && mount -o remount,bind,ro "$1"; }; return 0; }
empty() { [ -d "$1" ] && mount -t tmpfs -o mode=0555,size=4k tmpfs "$1"; return 0; }

for sock in /run/docker.sock /run/containerd/containerd.sock /run/podman/podman.sock; do hide "$sock"; done   # /var/run is /run
for home in /home/*; do
  [ -d "$home" ] || continue
  hide "$home/.docker/config.json"
  empty "$home/work/_temp/_runner_file_commands"
  freeze "$home/work/_actions"
done
freeze /usr/local/bin
freeze /opt
exec runuser -u "$user" -- "$@"
