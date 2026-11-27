# Notes on the summing block jump and the scripted CHILD9

These notes are a session's account of the code and its measurements;
they may be wrong in places.

## What the code does

- `zjump` (`bb/l3c10-blklaw.sl`) walks the block word with `zwalk`,
  which keeps the lower part of the old and new windows and the old
  window itself erased, and adds the pair deltas and cell counts of
  both windows as it goes (`zacc`). `wtail` takes those sums as
  inputs; `wjump`, whose walk does not sum, counts them with `sd-run`
  and `ds-dg` before calling it. The new window is still built, and
  `push-all` still rebuilds the word from it.
- `s15-ent` (`bb/l3c10-far2.sl`) takes entry 42 (CHILD9) by
  `c-child-h` (`bb/l3c10-chf.sl`), whose `reach-c` climbs with
  `cl-run`, rather than by `fe-cert-f`'s M9 replay of `reach-t1`.

Where a fast step does not apply, the loops fall back (`am-slow`,
`ms-loop`, the M9 replay of `reach-c`). None uses an axiom.

## Where the time goes

In steps 1,605 (CHILD9), 1,612 (ABSORB8) and 1,619 (CHAIN8V) of the
script, the work seems to be the walk of the block word from the
bottom to the jump level and the passes over the window below it, once
per marker. Before step 1,612 the right side holds the register (about
125,700 runs) and then the big train; the step absorbs about 54,000 of
its markers, and the jump level, computed from each gap as `af-step`
does, goes from about 56,900 down to about 1, one level per marker, so
the walks add up to about 1.5 * 10^9 levels. The right tail's large
numbers do not seem to be compared or rebuilt as a whole in these
steps.

## Timings

User seconds of compiled runs of a harness that builds the
configuration of script step 1,199 from `bb/l3c10bound-110012-par.sl`'s
checkpoint `g3` and runs the script, on a shared 4-core container,
single runs:

| step | s |
|---|---|
| 1,605 (CHILD9) | 52 |
| 1,612 (ABSORB8) | 200 |
| 1,619 (CHAIN8V) | 262 |
| 1,200 to 1,621 | 618 |

Step 1,605 by `fe-cert-f`'s M9 replay instead took 717 s, about 96% of
it in `c-move9-at` and its `c-jump` by stack samples. The CHILD9s at
steps 1,298 and 1,586 took about 5 s each.

With `OCAMLRUNPARAM=s=32M` (a minor heap of 32M words), steps 1,605 and
1,612 took 45 s and 150 s.

## Agreement

Rocq's side is far2's `drv15` (lin3c4's msC15, extracted) run over
lin3c4_s2's script from `lin3c3_s0/s0_c66.v`'s configuration, with
fingerprints from step 1,600 on and the configurations at steps 1,604,
1,611 and 1,618 written out. The fingerprints after each of steps 1,600
to 1,621 equal Rocq's; that after step 1,621 is the one the far2 and
par110 notes give for Rocq's `s2_c2.v`. In a second run, the
fingerprints after each of steps 1,200 to 1,621 (422 steps) equal those
of far2's Rocq traces (`rq` and `rq3`).

## Goals

- A copy of `bb/l3c10bound-110012.sl` with `c10-run6` in place of
  `c10-run4`, after the full file list, `bb/l3c10-run.sl`,
  `bb/l3c10-far.sl`, `bb/l3c10-train.sl`, `bb/l3c10-trlaw.sl`,
  `bb/l3c10-chf.sl` and `bb/l3c10-far2.sl`, under `--goal proved` and
  `ulimit -s unlimited`: PASS, exit 0, 4,826 s wall, 4,774 s user,
  3.97 GB peak, on a shared 4-core container.

## Open

- Each marker still costs a walk over the levels below the jump level
  and a rebuild of the word below it. Rocq's `fastStep` keeps only the
  block's value, its pair-delta sum and its bottom pair; doing so here
  seems to need lin3s7's `T_rel`, `Tv_digit` and `okW_crit` stated
  against `PBlk`, or a word that the jump can change in place.
