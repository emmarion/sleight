# Notes on `bb/l3c10-trlaw.sl`

These notes are a session's account of the file and its measurements;
they may be wrong in places.

## What it is

`try-trainl` and `try-traingl` are TRAIN and TRAING (simC10 entries 15
and 16) with type `Rch l3 c0 e -> Rs l3 c0`, built without axioms and
without a replay:

- `train-tgt-s` gives the proposal `t` and the shared tail `S`; the
  number of markers is read from the position of `S`.
- `ls-train` walks the markers on `Ls`, the parsed L-moment (the left
  `00 1^n lz`, the register's tokens, and the runs after them), which
  carries an erased run from `c0` and an erased `CEz`. Each marker is
  IDENT, or JUMP from the member followed by IDENT or by ROUND and IDENT,
  and then one level of the uniform descent of `bb/l3c10-uniform.sl`
  (`dsc-run`, `dch-mk`, `dch-run`), which seems to be the jump of family
  `P+1` and the SHED back to the member.
- IDENT in the walk (`ls-ident`) is its parse followed by one round
  (`ls-round`) rather than by `itl`'s rounds and their `canon` checks;
  the descent's `decode` and `phi-chk` then check that the round reached
  a register of family `P+1`. `ls-walk` walks a marker this way first
  and, where it fails, again with `itl` (`ls-mark`'s `once`).
- `Mc` caches the member's decoding, its `Phi` proof and its cells, so
  JUMP does not decode the member again and the descent checks its
  output against the cache instead of rebuilding it.
- `ls-out` builds the `Rq` and the `Rch` once, at the end; `train-lw`
  compares it with `t` on the runs in front of the tails they share, and
  `train-l` falls back to `train-f` (`try-train3`'s cut replay) when the
  walk or the comparison fails.
- `c10-move-l` is `c10-move-t` with entries 15 and 16 replaced by these;
  `c10-run5` iterates it.

The walk still does work linear in the register's length per marker:
the `c-at` calls of the jump (one or two per marker in the runs below,
each a `phi-run` and a cell count), IDENT's parse and round, and the
decoding, `phi-chk` and cell count of its output. Rocq's TRAIN law
(lin3s2 `comp1`) is not ported. In the runs below, IDENT's one round
reached family `P+1` at every marker, so lin3d18's `even_reentry`
rounds seem not to be what the walk lacks. What an arithmetic marker
would seem to need instead is the block of the contact state built
from its value without its word (its cell count and sum of pair
deltas, which seem to depend on every digit; in the TRAINs looked at,
the contact state grew about sixteenfold from one marker to the next,
so the jump does not end on a fixed level), ABSORB's contact
round (`af-step`'s `blk-snoc` and `wjump`, `bb/l3c10-blklaw.sl`) for
TRAIN's gaps and tail, and the descent started from a block.

## Changes to shared files

`bb/l3c10.sl` gains `rest-take-x` and `CTakeX`, `rest-take`'s result
under constructor names that `bb/l3c10-local.sl` does not shadow.

## Agreement and timings

Shared 4-core container, single runs, user time, from
`far/sr/c89501.txt` with a copy of `bb/l3c10-farh.sl`'s harness that
calls `c10-move-l`.

- Moves 89,502 to 400,000: the index of every move equals that of
  Rocq's simC10 trace, and the fingerprints equal Rocq's at the 22
  checkpoints from 90,000 to 350,000. TRAING does not fire in this
  range, so its walk is untested in situ.
- On the 152 TRAIN moves from 89,502 to 92,500, the walk reached the
  proposal every time. Over the whole range, the TRAIN moves slowest
  relative to the cut replay are short ones of 1 to 3 ms, at most 1.44
  times as long; a fallback would add the whole cut replay, so it seems
  not to have been taken there.

| stretch | TRAIN moves | `c10-move-t` | `c10-move-l` | Rocq |
|---|---|---|---|---|
| 89,502 to 110,000 | 1,059 | 23.8 s | 7.6 s | 2.8 s |
| 89,502 to 345,355 | 12,711 | 659 s (52 ms each) | 155 s (12 ms each) | 30 s |

The whole run from 89,502 to 400,000 took 939 s against 1,479 s.

Goals, `slc` with `--goal proved`, user time:

- `bb/l3c10bound.sl` (`c10-run2`) after the full file list and
  `bb/l3c10-run.sl`: PASS, exit 0, 146 s and 0.6 GB peak, against 168 s
  for the base tree in the same session; with `bb/l3c10-far.sl`,
  `bb/l3c10-train.sl` and `bb/l3c10-trlaw.sl` added before it: PASS,
  exit 0, 147 s.

## Where TRAIN's time goes in the 10^110012 goal

A harness that decodes a checkpoint of `bb/l3c10bound-110012-bstr.sl`,
runs `c10-move-h` move by move with its `Ahead`, and adds up the user
time of the moves that `c10-move-h` reports as entries 15 and 16 (the
failed entries scanned before them included); the configuration's
fingerprint (`show-fp`'s) is printed at the end. TRAIN fires in pieces
19 to 21 only (the script of pieces 22 to 24 has no entry 15 or 16):
1,864, 4,693 and 6,154 TRAIN moves, with no TRAING. Shared 4-core
container, the runs of one table row at the same time as one or three
others; 2f5e3780 against this code:

| piece | moves | all moves | TRAIN moves | TRAIN, this code | all, this code |
|---|---|---|---|---|---|
| 19 | 37,563 | 93.7 s | 6.1 s | 4.2 s | 91.8 s |
| 20 | 90,406 | 91.6 s | 25.8 s | 17.7 s | 83.0 s |
| 21 | 129,448 | 161.2 s | 56.0 s | 38.4 s | 144.8 s |

- The fingerprints at the end of each piece, and the moves at which
  TRAIN fired, are the same with both.
- The goal in 25 pieces, `bb/l3c10bound-110012-bstr.sh` under
  `/usr/bin/time -v`, this code and then 2f5e3780: PASS, exit 0,
  9:34 wall, 2,050 s user and 3.45 GB peak, against 9:46, 2,097 s and
  3.45 GB. CPU seconds per piece from `ps` every 5 s, 2f5e3780 in
  parentheses: 19: 90 (94), 20: 80 (89), 21: 143 (158); the sum over
  all pieces 1,953 (1,996).
- In all 12,711 TRAINs, every marker was walked with one round and
  none again with `itl` (a copy of `ls-walk` that counts them).
- The TRAINs of the first 600 moves of piece 21 have 27 markers at
  `P = 59`, 119 at `P = 242` or 243, or 251 or 252 at `P = 978` or 979,
  `P` the member's family. With 2f5e3780, `ls-train` took about 18, 46
  and 200 us per marker for these, and `train-tgt-s`, `find-at` and
  `rq-same` together about a tenth of its time or less. Per marker at
  `P = 978`, the jump took about 57 us (two `c-at` calls, against one
  at the smaller `P`), IDENT about 110 us and the descent about 60 us;
  with this code, IDENT about 45 us. By stack samples most of
  the rest is `blk-odd` (in `c-at`'s `phi-run` and the descent's
  `phi-chk`) and `decode`.
