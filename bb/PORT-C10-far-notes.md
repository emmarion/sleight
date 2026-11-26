# Notes on running simC10 past move 40,035 (`bb/l3c10-far.sl`)

These notes are a session's account of the runs and their measurements;
they may be wrong in places.

## Files

- `bb/l3c10-far.sl`:
  - `c10-big` computes entries 0 (BIGJC) and 1 (BIGJ) together: BIGJC
    is BIGJ, then M9, then CONTACT, so the BIGJ move is made once and
    BIGJC continues from it.
  - `c-certify-f` certifies a proposal on a cut configuration. The cut
    is at the gap run in front of the tail that the configuration and
    the proposal share (found by `slot-eq` on the tail's first cell); the
    cut pair is replayed by the framed simulator (`f-run`), lifted by
    `frame-one`, and the two zero runs at the junction are merged
    (`rnorm-pre`). `certify-fc` falls back to `c-certify-c` when the
    framed replay does not reach the proposal.
  - `c10-ent-f` is `c10-ent` with CHILD (5), BCOVF (6) and RESUME1 (24)
    over `certify-fc`, and BEVEN (8) as `certify-fc` with a replay budget
    of 3,000,000 moves. `c10-move-f` dispatches with these and `c10-big`;
    `c10-run3` iterates it.
  - All have the type `Rch l3 c0 e -> Rs l3 c0` (or return an `Rs`); no
    axiom is used.
- `bb/l3c10-farh.sl`: a `Program` harness that reads a configuration on
  standard input, runs `c10-move-f`, and prints per move the index and
  the process's times, and at checkpoint moves a fingerprint (state,
  head, run counts, and a hash of each side's runs modulo 2^61-1).
- `bb/l3c10drv.ml`: `tracefrom FILE M0 N DIR m...` traces Rocq's simC10
  from a configuration file; with `C10FP` set it writes only fingerprints.
- `bb/l3c10bound-37981.sl`: `c10-run3` for 89,501 moves from the blank
  tape, then the span bound.

## Agreement with Rocq

- From the blank tape to move 40,035 the index agrees with Rocq's trace
  on every move, and the fingerprint at 40,035 equals that of Rocq's
  configuration.
- Moves 40,036 to 69,895 against Rocq's trace from its configuration at
  40,035: every index agrees, and the configurations are equal at
  42,500, 45,000, ..., 67,500. Rocq's trace was stopped at 69,895, where
  its BIGJ moves took about 1.1 s each.
- At move 89,501 the fingerprint equals that of `lin3c1_m3/m3_c16.v`,
  the configuration of Rocq's certificate at that move (the generators
  `trnU`/`trnD`/`repL` expanded by a script). The tape span there has
  37,982 digits.
- Moves 89,502 to 367,361 against Rocq's simC10 traced from that
  configuration: every index agrees, and the fingerprint is equal at
  350,000 (an earlier run, with the BEVEN budget still at 100,000, had
  equal fingerprints at the 12 checkpoints from 90,000 to 150,000, and
  diverged at 334,276 where BEVEN did not fire). At 345,355, the end of the
  epoch-3 counter, the fingerprint equals that of `lin3c3_s0/s0_c66.v`,
  and so do those of `s0_c1.v` to `s0_c16.v` (moves 93,501 to 157,501).
  The span at 345,355 still has 37,982 digits.
- Past the counter, simC10's list takes the stack phase through long
  runs of BIGJ moves (4,072 of Rocq's first 54,645 moves there), as
  lin3c3's notes describe; Rocq's 10^110012 comes from a different,
  scripted list (lin3c4's simS over msC15), which these files do not
  port.

## Timings

User time on a shared 4-core container; Rocq's from its trace, which
ran alongside.

| stretch | Sleight | Rocq simC10 (OCaml) |
|---|---|---|
| 40,036 to 68,197 | 2,091 s (`c10-move`) | 13,106 s |
| 67,501 to 69,895 | 247 s | 2,531 s |
| 67,501 to 89,501 | 2,292 to 2,868 s | not measured |
| 89,502 to 367,361 | 1,749 s | 3,687 s |

- In the counter TRAIN takes most of the Sleight time (12,711 moves,
  about 1,040 s, against 30 s in Rocq), then CHILD (174 s) and AEND
  (145 s). Before `c-certify-f`, CHILD and BCOVF took about 0.6 s each:
  the replay certifier rebuilt and compared the whole right side, whose
  tail holds about 1 GB of digits.
- `slc` with `--goal proved` on `bb/l3c10bound-37981.sl` printed PASS
  and exited 0 in about 4,116 s of user time, 1.9 GB peak, with the
  dispatcher before the framed certifier.
