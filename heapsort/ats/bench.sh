#!/bin/sh
set -e
cd "$(dirname "$0")"
runs=${RUNS:-20}
out=$(mktemp)
for r in $(seq "$runs"); do
  for s in cert plain c; do taskset -c 2 ./driver bench $s >> "$out"; done
done
grep -v "checksum 393660565753209066784$" "$out" && { echo "bad checksum"; exit 1; }
for s in cert plain c; do
  grep "^$s " "$out" | awk '{print $2}' | sort -n |
    awk -v s=$s '{t[NR]=$1} END {m = NR%2 ? t[(NR+1)/2] : (t[NR/2]+t[NR/2+1])/2;
      printf "%-6s runs=%d min=%.1f ms median=%.1f ms\n", s, NR, t[1], m}'
done
rm -f "$out"
