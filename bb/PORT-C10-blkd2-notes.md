# Notes on lin3s22's block-word check and parse-once dispatcher

These notes are a session's account of a profile of the 10^110012
goal and of what it seems to say about porting lin3s22 (busycoq-L3
c8664dd); they may be wrong in places. No Sleight code follows from
them: `bb/` holds no counterpart of `blkD2`, `checkG`, or `moveL26`.

## The block from its value

Rocq's `blkD` tries digit candidates for `blkN P rho` and falls back
to `blkW2`, which is quadratic in `P`; lin3s22 puts `firstG`, a
candidate checked over a window of 64 heights, in front of that
fallback, for two word shapes logged at `P` about 1.8 million.

Sleight's counterpart seems to be `blk-fast` (`bb/l3phi.sl`), which
`blk-top`, `blk-odd`, `phi-run`, and `phi-chk` call: `fast-try` reads
the word top-down from the bits of `3 s + 1` (`awalk`, `twalk`,
`ewalk`, `xstep`), with `blk-run`, the definition of `PBlk` level by
level, for the last levels (`bottom`) and as the fallback when
`fast-try` answers `BrNo`.

- In the 25 pieces of `bb/l3c10bound-110012-bstr.sh` (an instrumented
  copy of the extracted program), `blk-fast` is called about 8.3
  million times and falls back to `blk-run` about 709,000 times, every
  one of them with `P` at most 30, where `fast-try` answers `BrNo`
  before reading any bit; those fallbacks take about 0.2 s in all.
- The extracted `fast-try` of 52565672, run on 23 constructed
  canonical words of 40 to 20,000 levels, among them both shapes
  lin3s22 logs (`pA` at levels 12 to 15 of a frozen-free word, and
  `pA` at levels 12 to 18 above a lowest `pA` over a frozen `pDp`),
  and on 3,000 values `rho` drawn at segment boundaries and at random
  for `P` from 31 to 3,000, answered `BrOk` each time, with the word
  that a direct transcription of `PBlk` in Python gives.

So the case lin3s22 addresses, the quadratic fallback on a long
block, seems not to arise here.

## Parsing once

`c10-move-h` parses the L-moment once (`ahead-lm`, `lc-of`) and hands
`lm` and `lc` to each entry that `c10-scan-h` tries, much as `moveL26`
hands `v` to each macro.
Some entries parse again: TRAIN's `train-tgt-s`, `train-lw`, and
`ls-train` each call `c-lm`. In pieces 19 to 21, the instrumented
`c-lm` calls under `train-lw` number about 363,000 and take about
2.1 s in all, against about 98 s for `train-lw`.

## Where the time goes

Instrumented copies of the extracted program, one run of each piece,
four at a time, on a shared 4-core container; inclusive user time of
a function, its recursive calls counted once. The instrumentation
seems to slow the self-recursive functions most.

| function | calls | time |
|---|---|---|
| `c-move9-at` | 13.2 M | 1,329 s |
| `xg` | 1.45 M | 484 s |
| `c-lm` | 17.0 M | 407 s |
| `phi-run` | 3.06 M | 373 s |
| `blk-fast` | 8.31 M | 331 s |
| `decode` | 2.53 M | 300 s |
| `phi-chk` | 3.09 M | 234 s |
| `c-aend` | 0.28 M | 152 s |
| `train-lw` | 0.42 M | 143 s |

The pieces' user times add up to about 3,160 s with this
instrumentation, against about 2,500 s for the 25 pieces and their
compilation in an uninstrumented run of the goal in the same session.

- Pieces 0 to 18 seem to be mostly M9 (`c-move9-at`, `c-jump`,
  `c-pgrp`, `xg`) and the collector: in stack samples of pieces 6 and
  12, more than half of the samples are in the collector.
- In piece 21, by about 190 stack samples, `ms-loop` (AEND) has about
  29% of the samples, TRAIN's walk about 28%, and `rns-same` about
  21%, which seems to be `rq-same` in DEATH's `death-end`, where each
  step compares the whole configuration with the target.
- Inside TRAIN in piece 21, `blk-fast` takes about 17 s of
  `train-lw`'s 62 s, `decode` about 10 s, and `phi-chk` about 10 s
  (these overlap).
- Within `blk-fast`, stack samples put about half of its time in
  `awalk` and its `bit-test`s, and much of the rest in `bottom`'s
  `revapp` and `mk-topl`.

## Measurements of the goal

Same container, at 52565672 (the code these notes describe):

- `bb/l3c10bound-110012-bstr.sh` under `/usr/bin/time -v`: PASS,
  exit 0, 11:39 wall, 2,500 s user, 3.45 GB peak.
- `bb/l3c10bound.sl` after the file list of that script, with
  `--goal proved`: PASS, exit 0, 111 s user, 0.72 GB peak.
