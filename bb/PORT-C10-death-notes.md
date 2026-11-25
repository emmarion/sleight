# Notes on `bb/l3c10-death.sl`

These notes are a session's measurements and reading of the code; they
may be wrong in places.

## What is proven

`c-death` (DEATH, index 10) has the soundness type
`Rch l3 c0 e -> Rs l3 c0` and uses no axiom. It takes Rocq's guard and
output from `m-death` (`bb/l3c10-child.sl`) and certifies the output by
following the cascade of `death_casc_exact` (`lin3d27_death.v`):

- `fd-levels P` (`bb/l3c10-desc.sl`): P levels, each the life jump
  (`c-jump` with the full flag), the end round (`c-round`) and the SHED
  round (`c-shedr`), from phi_O(P, top) down to phi_O(0, 0);
- `death-end`: `c-move9` moves for the round of `2 2 0` and the death
  episode, about 30 of them, until `c-wr-n` can walk the debris: a walk
  over exactly the stack entries above the target's left side (the
  depth is the difference in run counts, halved), whose result must
  equal the normalized proposal (`rq-norm`, `rq-same`);
- `c-certify` with no fuel then hands back the proposal itself.

`c-wr-n` is `bb/l3c10-desc.sl`'s `c-wr` with the depth of `stk-all` as
a parameter; `c-wr` is `c-wr-n 1000000000`. The M9 walk `c-walk` does
not take these debris stacks in one move, which seems to be why the
replay spent about 10 M9 moves per level there.

## Agreement

`cmain` mode 10 (`bb/l3c10-childh.sl`, which now dispatches index 10 to
`c-death`) on the stream of moves 1 to 39,806 (which holds all 179 DEATH moves
before move 40,035): 179/179 match Rocq.

## Timings (shared container, single runs, noisy)

Mode 10 against mode 99 (no macro checked) on the same stream puts the
179 DEATH moves at about 34 s of user time, against about 218 s for the
replay and 0.08 s for Rocq. Nearly all of it is the levels: each costs
O(P) (decoding, two phi words, two rounds, re-parsing the register), so
a cascade costs O(P^2). The one P = 3,657 cascade takes about 12 s, a
P = 721 one about 0.5 s, a P = 242 one about 0.04 s. Rocq computes the
output in closed form (`KdF2`, `UoN2`, `MdeathN2`) and relies on the
induction of `death_casc_exact`; matching that would seem to need an
erased proof of the cascade by induction on q, with the end and SHED
rounds of phi_O(q, 0) proven for all q (Rocq's `shed_margin`), which
this file does not attempt.
