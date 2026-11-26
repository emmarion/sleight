# Notes on lin3c4's scripted stack phase (`bb/l3c10-far2.sl`)

These notes are a session's account of the runs and their measurements;
they may be wrong in places.

## What the files do

- `bb/l3c10-far2.sl`:
  - `s15-ent i` applies the macro that lin3c4's table msC15 has at
    index `i` (lin3c4_csim.v), as a step of type
    `Rch l3 c0 e -> Rs l3 c0`; any index the table does not list gives
    `RsNo`. `s15-run` applies a list of indices in order and stops at
    the first that does not fire; `rd-nats` reads such a list from a
    string.
  - Indices served by existing macros: 0 (M9: `c-move9-at`), 1
    (VDESC2: `c-vdesc-u`), 6 (WALKN: `c-wr`), 20 (CONTACT), 23
    (IDENT), 24 (SWEEP3), 26 (RESUME1J: `try-resume-f`), 30 (DEATH3:
    `c-death-u`), 38 and 39 (BCOVF: `fe-cert-f`), 41 (ABSORB8:
    `mac-absorb3`), 42 (CHILD9: `fe-cert-f` with CHILD).
  - Index 37 (FDESC6) is `c-fdesc-k` with no level cap; `c-fdesc-u`
    is the same function with the cap of 256 levels that simC10's
    FDESC has.
  - Index 40 (CHAIN8V) is `mac-chain3g` without the guard over the
    whole right side; `mac-chain3` keeps it.
  - Index 33 (ITERV) is `try-iter` behind lin3s4's `wordShort` guard
    (`rshort 64` on the runs after the register) instead of the guard
    over the whole right side.
  - Index 28 (DDJ) is `c-ddj`: the DD contact `ct-dd` at the L-moment
    itself, through `dd-out`, which is the tail of `c-aend` moved into
    a function of its own (`c-aend` calls it after its rounds).
  - Index 35 (JUNC) is `c-junc`: `jx-prop` computes the result of
    lin3r3_macro's `try_junc` (the split of the digits, the window
    rounds `lwin`, the search for `K` with `canonL`, `cparse` and
    `rest_take`) as unproven code, and `c-certify-c` certifies it by
    `c-move9` steps until the configuration equals it. A first version
    that stopped at the first L-moment with the expected out tail went
    past Rocq's result at move 1,620, where `c-lm` reads the frontier
    word after the window as register digits.
- `bb/l3c10-far2h.sl`: a `Program` harness that reads a configuration,
  the moves at which to print a fingerprint, and a script, and prints
  per move the index and the times; `(s15-prog (BTrue) m0)` prints the
  light fingerprint (state, head, run counts and the hash of the right
  side only).
- `bb/l3c10bound-110012.sl`: `c10-run4` for 345,355 moves from the
  blank tape, `s15-run` over lin3c4_s2's script (s2_k0 and s2_k1, 1,621
  moves), then the span bound for 10^110012.
- Shared files: `c-fdesc-k` (`bb/l3c10-uniform.sl`), `mac-chain3g`
  (`bb/l3c10-blklaw2.sl`) and `dd-out` (`bb/l3c10-aend.sl`) are
  additions; `c-fdesc-u`, `mac-chain3` and `c-aend` keep their
  signatures and, as far as these runs show, their results.

## Agreement with Rocq

Rocq's side is lin3c4_cextract2's msC15 extracted to OCaml
(x_c4sim15b.ml, with lin3c1's `module Z` renaming), applied index by
index to the configuration of lin3c3_s0/s0_c66.v (the end of the
epoch-3 counter, move 345,355 of simC10), whose fingerprint equals that
of `c10-run3` at 345,355 (the far session's notes).

- Moves 1 to 105 of the script: full fingerprints (both sides hashed)
  equal Rocq's at the 30 moves checked. A first run, before FDESC6 had
  no level cap, diverged at move 8.
- Moves 106 to 1,618, from Rocq's configuration at 105: the light
  fingerprint equals Rocq's at all 1,513 moves compared, with the
  first JUNC rule; the run stopped at 1,619 (CHAIN8V, still behind the
  whole-side guard in that build).
- With the final code: JUNC from Rocq's configurations at 105, 260 and
  1,612, and moves 1,620 and 1,621 from Rocq's configuration at 1,619,
  give Rocq's light fingerprints; CHAIN8V at 1,619 from Rocq's
  configuration at 1,618 does too.
- After move 1,621 the right side holds a 0-run of 5 + 3 rho + n cells
  (a 365,455-bit number), so the span has 110,013 digits; lin3c4_s2's
  s2_c2.v, parsed with its `catN` numerals, has the same.
  Before that move the span seems to stay at 37,982 digits (s2_c1.v,
  move 1,199), so a bound file between 10^37981 and 10^110012 does not
  seem to be available on this path.

## Goal

`slc` with `--goal proved` on the full file list, `bb/l3c10-run.sl`,
`bb/l3c10-far.sl`, `bb/l3c10-train.sl`, `bb/l3c10-far2.sl` and
`bb/l3c10bound-110012.sl` printed `--goal proved: PASS` and exited 0:
8,328 s wall, 8,125 s user, 4.06 GB peak (the compiled program of
`native-compute`), on a shared 4-core container.

## Timings

Wall time per index over moves 106 to 1,618, from the harness run that
also printed a light fingerprint after every move (about a second of
each move seems to be that fingerprint and the output, judging by the
cheapest indices), against Rocq's extracted msC15 from the same
configuration without fingerprints:

| index | macro | moves | Sleight | Rocq |
|---|---|---|---|---|
| 0 | M9 | 835 | 1,312 s | 10.1 s |
| 6 | WALKN | 59 | 96 s | 4.8 s |
| 20 | CONTACT | 226 | 391 s | 3.2 s |
| 26 | RESUME1J | 56 | 263 s | 7.1 s |
| 37 | FDESC6 | 224 | 403 s | 9.0 s |
| 41 | ABSORB8 | 20 | 624 s | 46.2 s |
| 42 | CHILD9 | 8 | 1,145 s | 34.9 s |
| 39 | BCOVF (cntX) | 7 | 26 s | 42.3 s |
| 40 | CHAIN8V | 1 | 105 s | 10.1 s |

- The CHILD9 at move 1,605 took 841 s (Rocq 17 s). CHAIN8V at 1,619
  (Rocq 65 s) and the two moves after it took about 36 s from Rocq's
  configuration at 1,619 for the last two, and under 700 s with the
  load of the 1.2 GB configuration for the first.
- Reading a 1.2 GB configuration in the harness peaks at about 5.7 GB;
  the goal run reads none.

## Open

- JUNC's proposal (`jx-prop`) is unproven code checked by M9 replay;
  lin3r3's window lemma (`win_rounds`) is not ported, so a junction
  whose result the M9 replay does not pass through would fail rather
  than be proven another way.
- CHILD9 and ABSORB8 seem to be where the Sleight time goes in the
  scripted part; Rocq's closed forms (lin3s8's `fastStep8`, the
  shift-based digit reads of lin3c4_cdiv) are not ported.
