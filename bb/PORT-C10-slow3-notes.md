# Notes on `bb/l3c10-slow3.sl`

These notes are a session's account of the file and its measurements;
they may be wrong in places.

## What the file holds

- `zjump3` has the type and the result of `zjump`
  (`bb/l3c10-blklaw.sl`). Its walk (`zwalk3`) keeps the lower part of
  the old and new windows and the old window itself erased, and adds the
  pair deltas and cell counts of both windows as it goes (`zacc`), so
  its tail (`ztail3`, `wtail` with those sums as inputs) no longer
  recounts them with `sd-run` and `ds-dg`. The new window is still
  built, and `push-all` still rebuilds the word from it.
- `cl-step3` to `c-child-h3`, `af-step3` to `mac-absorb4`, and
  `cf-step3` to `mac-chain3v` are copies of `cl-step` to `c-child-h`
  (`bb/l3c10-chf.sl`), `af-step` to `mac-absorb3`
  (`bb/l3c10-blklaw.sl`), and `cf-step` to `mac-chain3g`
  (`bb/l3c10-blklaw2.sl`), with `zjump3` in place of `zjump`.
- `s15-ent3` is `s15-ent` (`bb/l3c10-far2.sl`) with entry 42 (CHILD9)
  taken by `c-child-h3`, entry 40 (CHAIN8V) by `mac-chain3v` without
  the whole-side guard, and entry 41 (ABSORB8) by `mac-absorb4`;
  `s15-move3` and `s15-run3` are `s15-move` and `s15-run` over it.

All have the type `Rch l3 c0 e -> Rs l3 c0` (or return an `Rs`); none
uses an axiom. Where a fast step does not apply, the copied loops fall
back as the originals do (`am-slow`, `ms-loop`, the M9 replay of
`reach-c`).

## Where the time went

Stack samples taken with gdb every few seconds of a compiled harness run
(tens of samples per step, so the shares are rough):

- Step 1,605 (CHILD9, `fe-cert-f`): about 96% in `reach-t1`'s M9
  replay, mostly `c-move9-at` and its `c-jump`. Over `reach-c`
  (`c-child-h`) the climb is taken by `cl-run`, and about 96% of the
  step is then `zjump`: `zwalk` about 68%, `wtail` about 29%.
- Step 1,612 (ABSORB8, `mac-absorb3`): about 75% in `zjump` (`zwalk`
  59%, `wtail` 16%), most of the rest in `wtail`'s `sd-run` and
  `ds-dg`; the garbage collector shows in about 57% of the samples.
- Step 1,619 (CHAIN8V, `mac-chain3g`): about 71% in `zjump` (`zwalk`
  69%), the rest in `ds-dg`, `sd-run` and `nfw-chk`.

In all three the work seems to be the walk of the block word from the
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
checkpoint `g3` and runs the script with the dispatcher given, on a
shared 4-core container, single runs. "Before" is `s15-ent`.

| step | `s15-ent` | `c-child-h`, `zjump` | `s15-ent3` |
|---|---|---|---|
| 1,605 (CHILD9) | 717 | 89 to 91 | 52 |
| 1,612 (ABSORB8) | 347 | 347 to 353 | 200 |
| 1,619 (CHAIN8V) | 466 | 448 | 262 |
| 1,200 to 1,621 | 1,695 | | 618 |

The other entries 40, 41 and 42 of the script gain too: the CHILD9s at
steps 1,298 and 1,586 took about 33 s before and about 5 s now.

With `OCAMLRUNPARAM=s=32M` (a minor heap of 32M words), steps 1,605 and
1,612 took 45 s and 150 s with `s15-ent3`.

## Agreement

Rocq's side is far2's `drv15` (lin3c4's msC15, extracted) run over
lin3c4_s2's script from `lin3c3_s0/s0_c66.v`'s configuration, with
fingerprints from step 1,600 on and the configurations at steps 1,604,
1,611 and 1,618 written out. With `s15-ent3`, the fingerprints after
each of steps 1,600 to 1,621 equal Rocq's; that after step 1,621 is the
one the far2 and par110 notes give for Rocq's `s2_c2.v`. In a second
run, the fingerprints after each of steps 1,200 to 1,621 (422 steps)
equal those of far2's Rocq traces (`rq` and `rq3`).

## Goal

A copy of `bb/l3c10bound-110012.sl` with `c10-run6` in place of
`c10-run4` and `s15-run3` in place of `s15-run`, after the full file
list, `bb/l3c10-run.sl`, `bb/l3c10-far.sl`, `bb/l3c10-train.sl`,
`bb/l3c10-trlaw.sl`, `bb/l3c10-chf.sl`, `bb/l3c10-far2.sl` and
`bb/l3c10-slow3.sl`, under `--goal proved` and `ulimit -s unlimited`:
PASS, exit 0, 4,826 s wall, 4,774 s user, 3.97 GB peak, on a shared
4-core container (the far2 notes give 8,328 s wall for the original).

## Open

- Each marker still costs a walk over the levels below the jump level
  and a rebuild of the word below it, now with about a third of the
  former allocation. Rocq's `fastStep` keeps only the block's value,
  its pair-delta sum and its bottom pair; doing so here seems to need
  lin3s7's `T_rel`, `Tv_digit` and `okW_crit` stated against `PBlk`, or
  a word that the jump can change in place.
- The copied loops duplicate the originals except for the jump.
