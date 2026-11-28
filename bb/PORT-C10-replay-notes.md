# Notes on the replays of the 10^110012 goal

These notes are a session's account of a profile of
`bb/l3c10bound-110012-bstr.sh` and of the code that follows from it;
they may be wrong in places.

## Which entries replay, and what they cost

An instrumented copy of the goal's extracted program (CPU time of each
entry call that `c10-scan-h` and `s15-ent` make, its inner calls
counted once) puts most of pieces 0 to 18 in BIGJ (`c10-big-p`, two
`c-move9-at` and a CONTACT per move), which is not a replay and which
Rocq's `bigJC10` also takes as `move9`. The entries that replay or
step through a run, and their inclusive times in that copy (inflated
by the instrumentation, most for DEATH):

| entry | piece 19 | piece 20 | piece 21 | piece 22 | piece 23 |
|---|---|---|---|---|---|
| DEATH (10, script 30) | 13 s | 105 s | 483 s | 28 s | 7 s |
| AEND (11) | 21 s | 53 s | 69 s | | |
| CHILD (5, script 42) | 8 s | 19 s | 25 s | | 17 s |
| RESUME1 (24, script 26) | | | | 55 s | 11 s |

DEATH is not changed here.
TRAIN (15) and ABSORB (script 41) are laws already, not replays.

## AEND: `c-aend-v` (`bb/l3c10-blklaw.sl`)

`c-aend` climbs the debris one marker at a time with `ms-loop`, whose
jump (`ms-jump`) and IDENT (`stride`) each rebuild or reparse the
register, so a marker costs time linear in the register. In piece 19,
205,592 of the 207,030 jumps of AEND's climbs end in the contact with
2 blanks (`ct-absorb`), which seems to be ABSORB's step; the rest seem
to be the last, failing, attempt of each climb. `c-aend-v` keeps
`c-aend`'s guards, `dd-out` and rounds, and climbs in three parts: one
`ms-loop` step for the first marker, whose block the ABSORB step seems
not to take (its lowest pair is not `pDp`, so `zjump` answers `AkNo`),
then ABSORB's `af-loop` (`zjump`'s value jump, `blk-snoc`, `wjump` and
`ct-run`, with the register's tokens erased) for as many markers as it
takes, then `ms-loop` again for the rest. In piece 19, `af-step` takes
204,084 markers and `ms-loop` the first marker of each of the 1,508
climbs. `bb/l3c10-run.sl`'s entry 11 is `c-aend-v`;
`bb/l3c10-desc.sl`'s `dprop` keeps `c-aend`.

## RESUME1: `try-resume-h` (`bb/l3c10-chf.sl`)

`try-resume-f` reaches CHILD through `fe-cert-f`, that is `c-child-f`,
whose replay climbs the death train with one M9 jump per marker.
`try-resume-h` is `try-resume-f` with CHILD taken by `c-child-h`,
whose `reach-c` climbs with `cl-run`. `c10-ent-h` (entry 24) and
`s15-ent` (script entry 26, `bb/l3c10-far2.sl`) call it.

## What a closed form would need

Rocq's AEND (`lin3s4_aend.try_aend4`) does not run the climb: it
checks `aendChk` and writes the output from `nBN`, and its soundness
goes through `lin3m2_rcfg.try_aend_sound` to `lin3d28_aend`
(`aend_gen`, `aend_ovf`) and `lin3d28_climb.climb_canon`, whose
premise `CanonC` is the per-marker check, resting on `first_contact`,
`contact_end`, `marker_t1` and `Ul_contact` (lin3d14 to lin3d27). A
port of that web seems much larger than one session; the code here
keeps a per-marker certificate (about 6 us per marker in piece 19 in
the instrumented copy, against about 110 us for `ms-loop`). CHILD's
head, walk and death are still replayed; Rocq takes them from
lin3d31's lemmas. DEATH's cascade would seem to need
`death_casc_exact` (`bb/PORT-C10-death-notes.md`).

## Timings

On a shared 4-core container whose load average stayed near 6 to 12
from other sessions' runs; user seconds.

The goal, `bb/l3c10bound-110012-bstr.sh` under `/usr/bin/time -v`,
this code and then 1d4fef80, each run's pieces timed by a wrapper
around the compiled program: PASS, exit 0, 30:58 wall, 2,514 s user,
3.45 GB peak, against 27:04, 2,616 s and 3.45 GB. Pieces 0 to 18,
which seem not to reach the changed entries, took 1,818 s against
1,763 s, so the load seems to have been somewhat higher during the
first run; pieces 23 and 24 took 90 s and 100 s against 92 s and 95 s.
A later run of the goal with this code, under a lighter load: PASS,
exit 0, 21:40 wall, 2,391 s user, 3.45 GB peak, with the same warnings
as 1d4fef80.

Pieces 19 to 22, each run as the compiled program of the goal with the
program of 1d4fef80 at the same time on the same piece, which seems to
be the fairer comparison under this load:

| piece | 1d4fef80 | this code | in the goal runs |
|---|---|---|---|
| 19 | 128.5 s | 109.4 s | 131 s / 115 s |
| 20 | 134.9 s | 87.4 s | 135 s / 89 s |
| 21 | 237.3 s | 174.9 s | 241 s / 184 s |
| 22 | 112.8 s | 74.4 s | 116 s / 76 s |

In the instrumented copy, AEND takes 2.1 s of piece 19 and 4.7 s of
piece 20, against 23.7 s and 52.9 s. Each piece's end configuration is
checked against its checkpoint by the goal itself, so the
configurations at the piece boundaries are the same as before.

`bb/l3c10bound.sl` after the goal's file list, `--goal proved`: PASS,
exit 0, 111 s user, 0.72 GB peak.
