# Notes on `bb/l3c10-child.sl`

These are a session's measurements and reading of the code; they may be
wrong in places.

## What is proven

Six macros have the soundness type `Rch l3 c0 e -> Rs l3 c0`:
`try-fe (BFalse)` (BCOVF, index 6), `try-fe (BTrue)` (CHILD, 5),
`try-resume` (RESUME1, 24), `try-death` (DEATH, 10), `try-beven`
(BEVEN, 8) and `try-reent` (REENT, 7). None uses an axiom.

Each takes the configuration proposed by its unproven port (`m-bcovf`,
`m-child`, `m-death`, `m-beven`, `m-reent`) and certifies it with
`c-certify`: `rnorm` merges equal-bit neighbours and drops empty runs
(Rocq's outputs may contain both) with a proof that the denotation is
unchanged, and `c-reach` runs the proven `c-move9` until it reaches the
normalized configuration exactly (`rq-same`). Before each move
`walk-to` tries `c-walk-n`, a walk over exactly the stack entries above
the target's left side, since some outputs lie inside one M9 walk; the
depth is the difference between the numbers of leading stack entries
(`0^1 1^t`, `2 <= t <= 64`) of the two left sides (`stk-cnt`), the
target's counted once. The fuel is 10^7 replay moves for CHILD.
`try-resume` is Rocq's guard, `c-move9`, then the certified BCOVF or
CHILD. `bb/l3c10.sl`'s `c-walk` is `c-walk-n` with an unbounded depth.

## Agreement

`cmain` in `bb/l3c10-childh.sl` reads a mode, a repetition count and a
hint stream; mode 0 checks every macro on every move, mode j only
macro j. On moves 1 to 39,806: BCOVF 424/424, RESUME1 70/70, DEATH
179/179 and CHILD 249/249. Move 39,807 (CHILD at `Pb = 7828`), from a
one-record stream starting at move 39,806, is certified and equal to
Rocq's output. In mode 0 no macro fired on another move. On the
synthetic stream of `bb/l3c10gen.ml`: REENT 4,028/4,028, BEVEN 20/20.

## Timings (shared container, single runs, noisy)

Sleight times are a mode-j run of `cmain` over moves 1 to 39,806 less
a run that checks nothing (about 4.2 s).

| macro | Sleight | Rocq |
|---|---|---|
| BCOVF | ~4.6 s | 0.25 s |
| RESUME1 | ~15 s | 0.79 s |
| DEATH | ~62 s | 0.08 s |
| CHILD, 249 to 39,806 | ~94 s | ~7 s |
| CHILD, move 39,807 | ~279 s | 125 s |
| REENT (syn) | ~0.16 s | 0.036 s |
| BEVEN (syn) | ~0.002 s | 0.0002 s |

At 39,807 about 34 s of the 279 s seem to be the unproven proposal
(`child-run`), the rest the replay. `OCAMLRUNPARAM=s=8M` took move
38,258 from about 14 s to about 11 s.

## Where the CHILD replay spends its moves

`Pb` takes three values below 39,807: 121 (242 instances, 15,138 replay
moves each), 484 (moves 21,268 and 21,564, 64,740) and 1,956 (five
from 38,258, 279,510); 39,807 has 7,828. At `Pb = 121` the replay is
13,470 single steps, 843 WIPE/CHAIN-W, 242 JUMP, 228 ROUND, 241 WALK,
113 SHIFT and one SWEEP. Read against `lin3d31_child`'s three parts,
about 13,600 moves are about 240 repetitions of a jump, a round and an
episode of about 90 mostly single steps, which seems to be the child's
death cascade (`lin3d31_death`'s `death_casc_E`, whose blank use is
the closed form `Uout + Kd` that `m-child` also uses); about 1,240 are
the climb over the death train, about ten moves per marker; the rest
are rounds and jumps. So the move count grows about linearly in `Pb`,
and every jump or round costs time linear in the register, which makes
the replay about quadratic in `Pb`, as Rocq's `chainF2` climb seems to
be, with a larger constant. Rocq's `try_child7H` never runs the death:
it checks a certificate of the climb (`chainb`) and takes the death's
blank use in closed form. Closing the gap would seem to need a proven
macro for the death cascade with tail `""` (for DEATH, with tail `1`,
`lin3d27`'s `death_casc_exact`) and the climb as `ms-loop` runs, or
the value law of `lin3e16_child` (`child_value`, from `lin3e16_pi`'s
positional potential).

A callgrind profile of 38,258 puts about 45% in the garbage collector
and the rest in no single function above 3%. Running single steps in
place of `c-move9` when the state is not 2 made move 21,268 slower,
since SHIFT then no longer skips its periods. Trying `c-aend`,
`mac-chain` and `mac-absorb` before each replay move saved under 1% of
the moves.
