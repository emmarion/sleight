# Notes on `bb/l3c10-train.sl`

These notes are a session's account of the file and its measurements;
they may be wrong in places.

## What it is

`try-train3` and `try-traing3` are TRAIN and TRAING (simC10 entries 15
and 16) with type `Rch l3 c0 e -> Rs l3 c0`, built without axioms:

- `train-tgt-s` (`bb/l3c10-local.sl`) is `train-tgt`'s proposal, and
  also returns the runs after the last walked marker, which the
  configuration and the proposal share.
- `cut-cert` cuts both at the gap in front of that shared tail, as
  `c-certify-f` does for CHILD, replays the cut pair with `fm-run`, lifts
  the framed sequence with `frame-one`, and merges the two blank runs at
  the junction (`rs-normpre`). Equality is tested only on the cut pair.
- `fm-move` is `f-move` with two more framed moves before the single
  step: `f-ident` (IDENT's parse, `ident-lm`, applied by `f-apply`) and
  `f-sweep3` (SWEEP3, whose `Go` is rebuilt for any right tail by
  `s3-go` from the block witness `S3w` that `sw3` returns). So the cut
  replay takes the moves `r-move` takes.
- Where the cut replay does not reach the proposal, `train-f` falls
  back to `r-run` on the whole configuration.
- `c10-move-t` is `c10-move-f` with entries 15 and 16 replaced by these;
  `c10-run4` iterates it.

## Changes to shared files

`bb/l3c10-local.sl`:

- `Tw`, `tw-snoc`, `trip-step`, `trips`, `tw-fn`, `blk3` and
  `cat-nilr` move above `(def-lvl LF)`, so that a framed move can use
  them; `S3w` and `s3-go` are new, next to them.
- `sw3`'s `S3Ok` carries an `S3w` witness in place of its `Go`;
  `try-sweep3` gets the `Go` from `s3-go` with an empty tail.
- `ident-lm` (with the result type `IdtR`) is `try-ident`'s parse;
  `try-ident` is `ident-lm` followed by `c-apply`.
- `train-tgt-s` (result type `TgR`) is `train-tgt`'s body;
  `train-tgt` keeps its signature.

## Agreement and timings

Shared 4-core container, single runs, user time, from
`far/sr/c89501.txt` with a copy of `bb/l3c10-farh.sl`'s harness that
calls `c10-move-t`.

- Moves 89,502 to 400,000: the index of every move equals that of
  Rocq's simC10 trace and that of the far session's run with
  `c10-move-f`, and the fingerprints equal Rocq's at the 22 checkpoints
  from 90,000 to 350,000. TRAING does not fire in this range, so its
  cut path is untested in situ.
- On the 152 TRAIN moves from 89,502 to 92,500, the cut replay reached
  the proposal every time; the fallback was not taken.

| stretch | TRAIN moves | `c10-move-f` (far run) | `c10-move-t` | Rocq |
|---|---|---|---|---|
| 89,502 to 110,000 | 1,059 | 29.9 s | 20.1 s | 2.8 s |
| 89,502 to 345,355 | 12,711 | 1,037 s (82 ms each) | 659 s (52 ms each) | 30 s |

The whole run from 89,502 to 400,000 took 1,479 s against 1,848 s.

What seems to remain is the replay itself: in two instances near move
89,600, the cut replay took about 1,700 and 8,100 moves (about 20 and
70 per marker, most of them single steps), about 2.5 and 40 ms. Before
the cut, a final comparison of the whole right side (about 127,000 runs at
that point) added about 7 ms per TRAIN, and it grew with the tape.

## Open

Rocq's TRAIN law (lin3s2 `comp1`, from lin3d25 `comp_exact_even`) is
not ported: the cut replay still takes tens of moves per marker.
