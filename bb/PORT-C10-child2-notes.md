# Notes on `bb/l3c10-child2.sl`

These notes are a session's account of the file and its measurements;
they may be wrong in places.

## What the file holds

- `c-reach-c` is `c-reach` with a number of leading replay moves before
  each of which `c-casc` (`bb/l3c10-uniform.sl`) is tried; once it fires,
  the rest is `c-reach`. `c-certify-c` is `c-certify` over it.
- `c-child-r` (CHILD, index 5) keeps `m-child`'s guards (`child-pre`) and
  head check (`child-head`, both split out of `bb/l3c10-child.sl` without
  a change in behaviour), and the check that the gap covers the head, the
  child's death (`uon`) and `kdf`. It then replays M9 with `reach-t1`:
  `c-casc` is tried before each of the first 256 moves, and from the move
  it fires (or from move 256) the replay stops at the first configuration
  whose parsed tail is `1`. From there it takes Rocq's final step
  (`canon-stride 1`, `finalb`'s rounds to a canonical `phi_O`), checks that
  the gap covers that step, and certifies the result with `c-certify-c`.
- `fe-cert-c` is `fe-cert` with `c-child-r` for CHILD and `c-certify-c`
  (no cascade) for BCOVF; `try-fe-c` and `try-resume-c` (RESUME1, 24) are
  `try-fe` and `try-resume` over it.
- `bb/l3c10-run.sl`'s entries 5, 6 and 24 use `fe-cert-c` and
  `try-resume-c`.

All have the type `Rch l3 c0 e -> Rs l3 c0`; none uses an axiom.

## Where CHILD can differ from Rocq

`c-child-r` does not run Rocq's chain search (`chainF2`). Where that
search fails while the guards above pass, Rocq's CHILD does not fire,
and `c-child-r` would still fire if the replay reaches a canonical
configuration with tail `1`. Its output is a configuration the machine
reaches either way, but the move would then differ from Rocq's trace. On
moves 1 to 40,035 this did not happen (below).

## Agreement

From the blank tape to move 40,035, the entry that fired agrees with
Rocq's trace on every move, and the configurations equal Rocq's at moves
1,000, 10,000, 22,268, 38,513 and 40,035 (`bb/l3c10-runh.sl`, the
coordinator's `cmp.py`). With the cascade alone (before `c-child-r`),
`cmain` over moves 1 to 39,806 matched CHILD 249/249, RESUME1 70/70 and
BCOVF 424/424.

## Where the replay goes

At `Pb = 121` the cascade starts after about 105 replay moves (the jump
and the collision), and a replay of about 15,100 moves becomes about
1,570. At move 38,258 (`Pb = 1956`) about 279,500 become about 19,700,
at 39,807 (`Pb = 7828`) about 78,400. The rest seems to be mostly M9
jumps (`c-jump`, whose `phi-run` and `decode` take most of the time),
the walk that lays the child's shed tokens down as the death train, and
the climb over it. At 39,807 `m-child` alone took about 34 s, mostly in
the chain's slow steps (`step-gen`, `phio`), which `c-child-r` does not
run.

## Timings

One shared 4-core container, one run each, user time of
`bb/l3c10-runh.sl`; Rocq's from its trace.

| entry | moves | before | now | Rocq |
|---|---|---|---|---|
| CHILD | 250 | 181 s | 62 s | 124 s |
| RESUME1 | 70 | 8.0 s | 3.8 s | 1.0 s |
| BCOVF | 424 | 2.9 s | 2.9 s | 0.9 s |
| all, to 40,035 | | 336 s | 211 s | 803 s |

`slc` on `full-list.txt`, `bb/l3c10-child2.sl`, `bb/l3c10-run.sl` and
`bb/l3c10bound.sl` with `--goal proved` prints `--goal proved: PASS`
and exits 0, in about 232 s of user time.

CHILD at move 39,807 alone, from a one-record stream, took about 45 s
(`cmain` mode 5), against about 141 s before.
