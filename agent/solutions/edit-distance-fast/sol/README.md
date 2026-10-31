# edit-distance-fast: gpt-6.1-sol's solution

An edit distance certified against `agent/tasks/edit-distance-fast/spec.sl`,
written by OpenAI's gpt-6.1-sol through `agent/pi.py` on the
edit-distance-fast task. `files.txt` lists its files in order;
`test-distance.sl` and `test-kernel.sl` are the agent's own tests. `HANDOFF.md`
and `FEEDBACK.md` are its last session's, as it wrote them.

## Running it

From the repository root, with `T=agent/tasks/edit-distance-fast` and
`O=agent/solutions/edit-distance-fast/sol`:

```
F="std/nat.sl std/list.sl std/macro.sl std/tactics.sl std/immediate.sl $T/spec.sl $(cat $O/files.txt)"
_build/release/slc --goal proved $F > /dev/null
_build/release/slc $F $T/perf.sl --build agent/solutions/sol_perf && agent/solutions/sol_perf
```

The first command reports the goal proved by the `qed` in `distance.sl`. For a
test, compile `$F $O/test-distance.sl` (or `test-kernel.sl`) the same way;
`test-distance.sl` prints `ok: 10 edit-distance regressions`.

## The run

Run `20261024-0741-gpt-6.1-sol-edit-distance-fast`, 4 sessions, started
2026-10-24 07:41 UTC on a DigitalOcean s-2vcpu-4gb droplet shared with two
other runs, on commit fc3603d. Sessions 2 to 4 ran `agent/pi.py` from 92c12fe;
slc was the same build throughout. Costs are `agent/pi.py`'s list-price
estimates.

| session | time | cost | |
|---|---|---|---|
| 1 | 1476 s | $1.78 | the cost, minimum and recurrence pieces and the first row, tested; no `qed` |
| 2 | 450 s | $0.48 | the swap case, the row and outer loops, and the `qed`; `check` first passed at 08:15 UTC |
| 3 | 105 s | $0.12 | re-checked; no change to the code |
| 4 | 94 s | $0.11 | re-checked; no change to the code |

A first attempt at session 1 ended after about 7 minutes, and $0.44, on an
OpenAI `server_is_overloaded` failure, and the session restarted; in all the
run cost $2.94. The solution's files are those of session 2.

## What it does

As a Claude session reads it: three arrays of `len(t) + 1` cells, rows along
the second string `t`, allocated once per call with `array-make`; a row loop
that reads the two previous rows and writes the next, and an outer loop over
the first string that rotates the three arrays. Each cell's value is kept
below 2^60, so the arithmetic is `u62-*`. The extracted inner loop is a tail
call doing a `Bytes.unsafe_get`, two `Array.unsafe_get`s and an
`Array.unsafe_set` on an `int array`, with native `int` comparisons and
additions. Empty strings are handled before the arrays are made.

729 lines, 636 of them neither blank nor comment, in 14 files; the tests are
another 193.

## Measurements

`perf.sl` at 2f4e1bd gives the six distances 3670, 39200, 39200, 103, 1168 and
5801, the same as a Python port of GCC's `get_edit_distance`.

- On the droplet (OCaml 4.14.1), the agent measured 1.51 s wall time for the
  six calls, 0 minor words and 95,436 major words: three arrays of
  `len(t) + 2` words each per call.
- On an Apple M4 Pro (OCaml 5.4.1), the median of 5 runs was 0.37 s. OCaml
  5.4's `major_words` there leaves out some recent allocations, so it reads
  lower.
