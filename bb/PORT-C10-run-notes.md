# Notes on `bb/l3c10-run.sl`

These notes are a session's account of the free-running port of simC10
and its measurements; they may be wrong in places.

## What the file holds

- `c10-ent i` is entry `i` of Rocq's `msB10` (numbering as in
  `bb/PORT-C10.md`), and entry 26 is M9 (`c-move9-at`). DEATH, FDESC,
  VDESC and VDESC2 are the closed-form descents of
  `bb/l3c10-uniform.sl`.
- `c10-try` is one entry, with a result equal to its input counted as
  not firing. `fd-level` (`bb/l3c10-desc.sl`) answers `RsOk` with the
  unchanged configuration when `c-jump` fails, and with the older
  `c-vdesc` that made VDESC2 fire as an identity move from move 1,276
  on; the check keeps such answers from stopping the run.
- `c10-move` parses the configuration once (`c-lm`) and passes the
  parse to M9 and, as an `LmC` (`lc-of`), to CHILD, BCOVF, REENT and
  BEVEN, with `fe-of` computed only once entries 0 to 4 have failed.
  It returns the index that fired.
- `c10-run2` iterates `c10-move` with fuel, carrying `Rch`.
- `bb/l3c10bound.sl` runs `c10-run2` for 40,035 moves under
  `native-compute` and turns the tape span into a `NoHaltBelow` goal
  for 10^15568 steps.

`bb/l3c10-runh.sl` is a `Program` harness: per move it prints the entry
that fired, the process's user and wall time, the user time of each
entry tried and of the shared parse, and the configuration at the moves
given to `rprog`. `bb/l3c10-runh0.sl`, loaded first, keeps the
prelude's `Stop` before `bb/rle.sl` shadows it.

## Agreement with Rocq

From the blank tape to move 40,035, the entry that fired agrees with
Rocq's trace (`drv trace`) on every move, and the configurations equal
Rocq's at moves 1,000, 10,000, 22,268, 38,513 and 40,035.

## Timings

One shared 4-core container, one run, user time of the harness
(which also measures each entry), Rocq's from its trace on what may
have been a different load:

| to move | steps | Sleight | Rocq |
|---|---|---|---|
| 22,268 | 10^2314 | 4.4 s | 24.5 s |
| 38,513 | 10^6145 | 55 s | 195 s |
| 40,035 | 10^15573 | 336 s | 803 s |

Per entry over moves 1 to 40,035, the time of the moves it made
(including the entries tried before it on those moves):

| entry | moves | Sleight | Rocq |
|---|---|---|---|
| CHILD | 250 | 181 s | 124 s |
| ABSORB | 42 | 111 s | 471 s |
| CHAIN | 34 | 11.8 s | 138 s |
| TRAIN | 789 | 11.8 s | 0.8 s |
| RESUME1 | 70 | 8.0 s | 1.0 s |
| M9 | 29,657 | 4.6 s | 14.8 s |
| AEND | 641 | 2.9 s | 8.0 s |
| BCOVF | 424 | 2.9 s | 0.9 s |
| FDESC | 1,012 | 0.8 s | 39.2 s |
| others | | under 0.4 s each | |

Two moves dominate: CHILD at 39,807 (about 141 s) and ABSORB at
39,956 (about 92 s). The entries that are tried and fail cost about
5 s in all, the shared parse under 1 s.

## The goal

`slc` on `full-list.txt` (the coordinator's file list), `bb/l3c10-run.sl`
and `bb/l3c10bound.sl` with `--goal proved` prints `--goal proved:
PASS` and exits 0, in about 360 s of user time.
