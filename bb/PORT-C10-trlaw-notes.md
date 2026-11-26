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
the rounds of IDENT (`itl`), the decoding and `phi-chk` of IDENT's
output, and the `c-at` calls of the jump. Rocq's TRAIN law (lin3s2
`comp1`) is not ported; what seems to be missing for it is a proof that
IDENT's rounds re-enter family `P+1` (lin3d18 `even_reentry`) and the
margin arithmetic, uniform in `P`.

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

For one TRAIN of 119 markers at move 89,641, a profile of the walk gave
per marker about 45 us for IDENT, 26 us for the descent, 17 us for
JUMP, and 1 us for the IDENT that fails before the jump.

Goals, `slc` with `--goal proved`, user time:

- `bb/l3c10bound.sl` (`c10-run2`) after the full file list and
  `bb/l3c10-run.sl`: PASS, exit 0, 146 s and 0.6 GB peak, against 168 s
  for the base tree in the same session; with `bb/l3c10-far.sl`,
  `bb/l3c10-train.sl` and `bb/l3c10-trlaw.sl` added before it: PASS,
  exit 0, 147 s.
