#!/usr/bin/env bash
# add_swap.sh MAX_GB KEEP_GB: a swap file on / for modules that need more memory than a 16 GB runner has.
#
# The real case: competemath/tengoku#779 (prime-gaps-186, one module of 166,723 lines) left the merge queue twice on 12 Nov 2026 (queue-gate runs
# 43306897671 and 43313465453): each time the runner was shut down 13-16 minutes into `Tengoku.PrimeGaps186`, with no error of its own. The same module built in 21 minutes on the same kind of runner
# in autotag-build (twice), and the factory's verify lost its runner on it twice until it added the swap its shard had (emissary-archangel #182). It sits
# at the edge of the runner's memory, so whether the queue passes it is luck; flt-anthropic's top modules were killed at 14 GB and will not pass at all.
#
# Swap costs nothing while memory is enough: the kernel uses it only under pressure. It is disk, so the size is what the disk can spare after the tree's
# cache is unpacked: free space (whole GB, rounded down) minus KEEP_GB, which is left for the build and the pack, and never more than MAX_GB.
# Under 8 GB to spare: no swap, said, exit 0 (the build runs as it did before). A command that fails: the file is removed, exit 1.
set -u
max=${1:-}; keep=${2:-}
case $max in ''|*[!0-9]*|0) echo "add_swap.sh: MAX_GB is a positive whole number, not '$max'" >&2; exit 2 ;; esac
case $keep in ''|*[!0-9]*) echo "add_swap.sh: KEEP_GB is a whole number, not '$keep'" >&2; exit 2 ;; esac
bytes=$(df -B1 --output=avail / | tail -n 1 | tr -dc '0-9')
case $bytes in ''|*[!0-9]*) echo "add_swap.sh: cannot read the free space; no swap"; exit 0 ;; esac
avail=$((bytes / 1073741824))
room=$((avail - keep))
if [ "$room" -lt 8 ]; then
  echo "add_swap.sh: ${avail} GB free, ${keep} GB kept for the build: under 8 GB to spare, no swap"
  exit 0
fi
size=$room
[ "$size" -le "$max" ] || size=$max
fail() {
  echo "add_swap.sh: $1 failed; the swap file is removed" >&2
  sudo swapoff /swapfile 2> /dev/null || true
  sudo rm -f /swapfile
  exit 1
}
sudo swapoff -a || true
sudo rm -f /swapfile
sudo fallocate -l "${size}G" /swapfile || fail fallocate
sudo chmod 600 /swapfile || fail chmod
sudo mkswap /swapfile > /dev/null || fail mkswap
sudo swapon /swapfile || fail swapon
echo "add_swap.sh: ${size} GB of swap (${avail} GB were free, ${keep} kept, at most ${max})"
