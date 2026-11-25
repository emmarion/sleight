# Notes on `bb/l3c10-desc.sl`

These notes are a session's account of the file; they may be wrong in
places.

## What the file holds

Six of simC10's entries as Sleight macros of type
`Rch l3 c0 e -> Rs l3 c0`, so each one's type is its soundness
statement and no axiom is used:

| # | name | Sleight | Rocq |
|---|---|---|---|
| 2 | RET | `c-wr (BTrue)` | `try_retS` |
| 4 | WALKN | `c-wr (BFalse)` | `try_walkNS` |
| 17 | FDESC | `c-fdesc` | `try_fdescK` |
| 3 | VDESC | `c-vdesc (BTrue)` | `vdescCS` |
| 25 | VDESC2 | `c-vdesc (BFalse)` | `try_vdesc2` |

AEND (#11) is `c-aend` in `bb/l3c10-aend.sl` (notes in
`bb/PORT-C10-aend-notes.md`); `dprop` below dispatches to it, so that
file is loaded before this one.

- WALKN and RET: `stk-all` parses the left token stack with no cap on
  the token sizes, keeping an erased `K2` proof that every token is at
  least 2. `rv-run` builds Rocq's run list `retV` at run time and, only
  erased, the walked word, its `Wk` proof and its bits; `wk-ok` and
  `go-run` give the run. For RET the walk continues over the bottom
  stack kA from an empty run list, and the left-end episode (39,886
  steps from `0inf [C]1 0^220`) is the lemma `le-go`, whose `ARun` is
  found at compile time by `srun` under `native-compute`. Its segments
  enter through `Cat` facts (`gs-cat`, `gs-z`) and its run of 220 zeros
  through `rp-dec` at compile time; writing them as explicit proof
  chains made the file's build about 20 s slower and 2 GB larger.
- FDESC, VDESC and VDESC2: one level is `fd-level`: `c-jump` with its
  new `full` flag (the whole life to phi(0)), `c-round` (the end round)
  and `c-shedr` (the SHED round: the 29-step gadget `c-shed`, then
  `rd-after`, the part of a normal round after its gadget, on +1Y).
  FDESC takes the level count from the budget test `fd-loop`; VDESC
  descends to level 1; VDESC2 takes levels while they fit the tape, in
  place of Rocq's `vdescF` budget.

## Checking

`dmain` reads `hints mine` output and checks every kind-3 record of
these indices and AEND's against Rocq; `tmain` takes `IDX REPS` first and repeats
that macro REPS times, for timing. On moves 1 to 40,035 all 3,066
records match: 544 RET, 853 WALKN, 1,012 FDESC, 2 VDESC, 14 VDESC2 and
641 AEND.

## Timings (one shared 4-core container, noisy)

User time of `tmain` with extra repetitions, against Rocq's own time
for the same moves from `hints mine`:

| macro | Sleight | Rocq |
|---|---|---|
| WALKN, 853 moves | about 0.03 s | 0.058 s |
| RET, 544 moves | below the noise, under 0.01 s | 0.005 s |
| FDESC, 1,012 moves | about 44 s | 36 s |
| VDESC, 2 moves | about 80 s, by difference of whole runs | 0.042 s |

VDESC is slow because each of its levels re-derives the register's
words in O(P), so a descent costs O(P^2); Rocq uses a closed form for
the token stack.

## Changes outside this file

`bb/l3c10.sl`: `c-jump` takes a `full` flag first; `c-move9` passes
`(BFalse)`.
