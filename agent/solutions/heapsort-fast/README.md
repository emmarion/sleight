# heapsort-fast solutions

Heap sorts certified against `agent/tasks/heapsort-fast/spec.sl`, written by
agents on the heapsort-fast task. Each directory's `files.txt` lists its files
in order. Each sorts `perf.sl`'s 2^20 pseudo-random integers below 2^30, once,
and prints the time and what the sort allocates. `heapsort/bench/` times them
against the other heap sorts in `heapsort/`.

`mimo/` was written by the mimo-v2.6-pro agent. From the repository root:

```
dune exec bin/main.exe -- std/nat.sl std/list.sl std/immediate.sl agent/tasks/heapsort-fast/spec.sl \
  $(cat agent/solutions/heapsort-fast/mimo/files.txt) agent/tasks/heapsort-fast/perf.sl \
  --build agent/solutions/mimo_perf && agent/solutions/mimo_perf
dune exec bin/main.exe -- --goal proved std/nat.sl std/list.sl std/macro.sl std/tactics.sl std/immediate.sl \
  agent/tasks/heapsort-fast/spec.sl $(cat agent/solutions/heapsort-fast/mimo/files.txt)
```

Each directory's last file, `qed.sl`, was added after the agents' runs: it
discharges the spec's goal with the agent's `heapsort-fast`, which the
second command checks.

`opus/` was written by the claude-opus-5-5 agent in the first session of run
`20261012-1220-claude-opus-5-5-heapsort-fast`; of the runs in
`heapsort/agent-runs-8860c75.csv`, it is the smallest solution by
non-whitespace characters outside comments. It runs as `mimo/` does, with
`opus` for `mimo`.
