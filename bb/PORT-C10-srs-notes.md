# Notes on a structural right side for the 10^110012 goal

These notes are a session's account of an experiment and its
measurements; they may be wrong in places. No code in the load list
comes from it.

## The question

The late pieces of `bb/l3c10bound-110012-bstr.sl` (19 to 23) carry a
regular train of about 63,000 markers (`0^g 1^6`, each gap `g` with
`4 g + 6` the gap before it) at the far end of the right side, about
0.5 GB of digits (`bb/PORT-C10-bstr-notes.md`, Memory). Rocq's
`lin3s21_fold.v` folds such trains into `TReg` nodes and materialises
items ahead of the register (`peelA`). The question was whether a
fold could be added here at little cost, and how much it would save.

## What a sound fold seems to need here

- Each macro is a function `Rch l3 c0 e -> Rs l3 c0`, and its proof
  takes the right side apart through `Den R r` and builds a run from
  the zero-padded configuration of `e`. Moving such a run onto a tape
  with something behind `R` (`run-eqz` over `CEz`) seems to fail
  exactly where a step pulls from the end of `r`, so there seems to be
  no lemma that lifts an arbitrary macro's `Rch` to `R ++ mat T`
  without knowing that the run never reads past `R`, which the run's
  type does not record.
- Rocq's `lin3s11_frame.v` gets the frame from each macro's soundness
  lemma holding for every run list plus a proof that the macro's
  function is local (`m (appR c X) = Some (appR c' X, k)`), proved per
  macro (DDJ, ITER, WIN there, and the moves of `lin3s14` to
  `lin3s21`). The Sleight checker does not evaluate (DESIGN.md §29),
  so the analogue here seems to be a frame-parametric certificate per
  macro, as `FR` and `f-move` (`bb/l3c10-local.sl`) give for the
  framed simulator: about 76 `MkRch` sites in 25 files, with the
  certificate chains under them (`c-apply`, `rdk-run`, `xg`,
  `rest-take` and others), restated over a far context.
- Running a macro on the explicit part and re-certifying its proposal
  with `f-cert` is sound and generic, but replays `f-move`, which seems
  far too slow for M9, CHILD9, ABSORB8 and CHAIN8V.

## Measurement of the most a fold could save

A scratch harness (not in the repository) decodes the checkpoint of
pieces 20 to 23, optionally removes the far train and everything after
it (the last four runs, `0^6 1^3 0^1 1^6`), runs the piece's moves and
script, and prints the user time and a fingerprint of the result.
This is not a proof: it runs the zero-padded tape. Same 4-core
container, the two variants of a piece run at the same time, four
processes at once.

| piece | full: user s | full: peak GB | cut: user s | cut: peak GB | cut run |
|---|---|---|---|---|---|
| 20 | 178 | 1.62 | 188 | 1.13 | same left side; right side the full one less the train |
| 21 | 141 | 2.91 | 159 | 1.84 | as for piece 20 |
| 22 | 264 | 3.51 | 282 | 2.53 | stops after 417 of its 419 steps |
| 23 | 266 | 2.83 | 5 | 1.33 | stops at its first step (index 40) |

- So the far train seems to be read by the last steps of piece 22,
  which take one marker from it (63,083 to 63,082 markers counted
  this way), and by piece 23, whose first step absorbs it (the full
  run ends with no train there).
- Removing the train lowers the peak by about 0.5 to 1.0 GB in
  pieces 20 to 22 and raises the user time by 5 to 13%, seemingly
  because the collector runs more often over the smaller heap (the
  same trade as `OCAMLRUNPARAM=o=60` in `bb/PORT-C10-bstr-notes.md`).
- A fold would thus seem to save memory only, and not in piece 23 or
  the end of piece 22, where the train would have to be materialised;
  piece 23 alone peaks at 2.83 GB.
