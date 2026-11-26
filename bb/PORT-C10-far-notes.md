# Notes on running simC10 past move 40,035 (`bb/l3c10-far.sl`)

These notes are a session's account of the runs and their measurements;
they may be wrong in places.

## Files

- `bb/l3c10-far.sl`: `c10-move-f` is `c10-move` with entries 0 (BIGJC)
  and 1 (BIGJ) computed together. BIGJC is BIGJ, then M9, then CONTACT,
  so `c10-big` makes the BIGJ move once and continues BIGJC from it;
  when BIGJC fails it answers BIGJ's result. `c10-run3` iterates it.
  Over the 697 moves where both dispatchers were run from one
  configuration, the indices agreed and the move took about 0.10 s
  against 0.15 s.
- `bb/l3c10-farh.sl`: a `Program` harness that reads a configuration on
  standard input and runs `c10-move-f`, printing per move the index and
  the process's times, and at checkpoint moves a fingerprint (state,
  head, run counts, and a hash of each side's runs modulo 2^61-1).
- `bb/l3c10drv.ml`: `tracefrom FILE M0 N DIR m...` traces Rocq's simC10
  from a configuration file; with `C10FP` set it writes only
  fingerprints at the checkpoint moves.
- `bb/l3c10bound-37981.sl`: `c10-run3` for 89,501 moves from the blank
  tape, then the span bound.

## Agreement with Rocq

- Moves 40,036 to 56,563 (Rocq's trace from its configuration at
  40,035, against the harness from the same configuration): the entry
  that fired agrees on every move, and the configurations are equal at
  42,500, 45,000, ..., 55,000. Rocq's trace was still running past move
  65,000 when these notes were written.
- The harness reaches move 89,501 by VDESC (index 3). The tape span
  there has 37,982 digits, so the bound is 10^37981 (Rocq's step count
  gives 10^37987). The configuration is about 1.2 GB of text, with
  63,040 runs of more than 100 digits on the left.
- Rocq's simC10 run from the harness's configuration at 89,501 agrees
  with the harness on every move to 118,559, with equal fingerprints at
  90,000, 92,500, ..., 115,000. At 118,560 Rocq's TRAIN fires and the
  older TRAIN port (`try-train`) did not; the base's `try-train2` fires
  there and gives Rocq's configuration on the first 19,800 runs of a
  truncated copy. The run past 89,501 is being repeated on that base.

## Timings

One shared 4-core container, user time.

| stretch | Sleight | Rocq simC10 (OCaml) |
|---|---|---|
| 40,036 to 56,563 | 907 s | 5,663 s |
| 67,501 to 89,501 | 2,868 s | not yet measured |
| 89,502 to 118,559 | about 1,360 s | about 276 s |

- From 40,036 to 89,501 most moves are BIGJC and BIGJ; a BIGJ move took
  about 0.1 s in Sleight against 0.3 to 1.0 s in Rocq, growing with the
  register.
- In the epoch-3 counter Rocq is faster: CHILD and BCOVF take about
  0.6 s each in Sleight (both replay M9 to certify) against about 25 ms
  and 5 ms in Rocq, and there are about 10,000 of them in the counter.
- `slc` with `--goal proved` on `bb/l3c10bound-37981.sl` printed PASS
  and exited 0 in about 4,116 s of user time, 1.9 GB peak.
