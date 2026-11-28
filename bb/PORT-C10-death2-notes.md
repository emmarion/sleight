# Notes on DEATH's final comparison

These notes are a session's measurements and reading of the code; they
may be wrong in places.

## The comparison at 1d4fef80

DEATH (index 10) runs as `c-death-u` (`bb/l3c10-uniform.sl`), which
falls back to `c-death`'s `death-end` (`bb/l3c10-death.sl`) only when
`death-end-u` fails. In piece 21 of `bb/l3c10bound-110012-bstr.sh`, an
instrumented copy of the extracted program, timing each call site of
`rq-same` (`bb/l3c10-child.sl`, the one returning an erased equality),
gives:

| caller | calls | time |
|---|---|---|
| `death-end-u` | 1,183 | 58.3 s |
| `rs-to` | 987 | 0.12 s |
| `c-reach` | 138,647 | 0.12 s |
| `c-certify` and `c-certify-c` | 3 | 0.19 s |

`death-end` made no call there, and `bb/l3c10-trlaw.sl`'s `rns-same`,
the one returning `Bool`, seems not to be the one in the earlier stack
samples: those stacks were `bb/l3c10-child.sl`'s, cut off by `bt 1500`
inside its non-tail recursion.

Every one of the 1,183 comparisons answered `ESome`. The right side
held 1.1 to 2.0 million runs, and after its first 489 or 1,961 runs the
two right sides were physically the same list; the two left sides, of
620 to 2,568 runs, were the same list throughout. So the time seems
to go to walking one to two million shared runs, one stack frame each,
to build an equality proof that `death-end-u` and `death-end` then
drop: both return the walk's own `e1` and `ch1`.

## What the code does

`death-end-u` and `death-end` compare with `rq-eq` (`bb/l3c10-desc.sl`),
which answers `Bool`, and `rns-eq` answers `BTrue` as soon as
`slot-eq` finds both lists at one slot. The macro's result is the
certified `e1`, so its type and its proof are unchanged and
the comparison only decides whether `e1` is the proposal.

## Measurements

Shared 4-core container, other sessions running (load 8 to 12), single
runs unless stated.

Each piece of the extracted program of `bb/l3c10bound-110012-bstr.sh`,
head (1d4fef80) and this code run side by side, one pair at a time
(user seconds; peaks barely change):

| piece | head | this code |
|---|---|---|
| 0 to 18 | 1,744 | 1,741 |
| 19 | 129.7, 126.5 | 121.9, 120.3 |
| 20 | 134.4, 133.6 | 111.4, 112.0 |
| 21 | 237.7, 241.8 | 182.4, 183.6 |
| 22 | 114.4 | 112.7 |
| 23 | 88.2, 87.9 | 87.4 |
| 24 | 93.9 | 94.0 |
| all (first runs) | 2,543 | 2,451 |

The first run of piece 23 with this code was killed for lack of
memory, so the sum counts its rerun.

Pieces 19 to 21 seem to be where DEATH meets the long right side; the
others are within noise. In 45 stack samples of piece 21 with this
code, none is in DEATH; TRAIN's walk (`train-lw`) has about half of
them and AEND (`ms-loop`) about 38%.

The whole goal under `/usr/bin/time -v`, PASS and exit 0 each time,
3.44 GB peak each time:

| run | wall | user |
|---|---|---|
| this code, load 10 to 12 | 32:10 | 2,562 s |
| head, next, load 6 to 8 | 20:26 | 2,562 s |
| this code, next, load 6 to 8 | 16:41 | 2,473 s |

`bb/l3c10bound.sl` after the same file list, with `--goal proved`:
PASS, exit 0, 126 s user against 117 s for head in the run after it,
0.72 GB peak for both.
