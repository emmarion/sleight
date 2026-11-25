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
the target's left side, since some outputs lie inside one M9 walk.
`try-resume` is Rocq's guard, `c-move9`, then the certified BCOVF or
CHILD. `bb/l3c10.sl`'s `c-walk` is `c-walk-n` with an unbounded depth.

## Agreement

`cmain` in `bb/l3c10-childh.sl` reads a mode, a repetition count and a
hint stream; mode 0 checks every macro on every move, mode j only
macro j. On moves 1 to 40,035: BCOVF 424/424, RESUME1 70/70, DEATH
179/179, CHILD 249/250 (move 39,807 is not reached within the fuel of
10^6 M9 moves), and in mode 0 no macro fired on another move. On the
synthetic stream of `bb/l3c10gen.ml`: REENT 4,028/4,028, BEVEN 20/20.

## Timings (shared container, single runs, noisy)

| macro | Sleight | Rocq |
|---|---|---|
| BCOVF | ~1.6 s | 0.25 s |
| RESUME1 | ~114 s | 0.79 s |
| DEATH | ~218 s | 0.08 s |
| CHILD (249) | ~315 s | 132 s (125 s at 39,807) |
| REENT (syn) | ~0.16 s | 0.036 s |
| BEVEN (syn) | ~0.002 s | 0.0002 s |

The replay is as long as the machine's own M9 trajectory: DEATH took a
median of 31,869 M9 moves (max 547,961), CHILD a median of 15,138
(279,510 at move 38,258). Matching Rocq's speed would seem to need
closed-form proofs in place of the replay (Rocq's `death_casc_exact`,
`lin3e16_pi`'s `child_value`). Trying `c-aend`, `mac-chain` and
`mac-absorb` before each replay move saved under 1% of the moves.
