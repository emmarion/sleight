# Notes on BIGJ in `c10-run6` (`bb/l3c10-far.sl`)

These notes are a session's account of the code and its measurements;
they may be wrong in places.

## What the code does

- BIGJ is `c10-big-p`, the first entry of `c10-move-h`, after
  lin3c1_csim10's `bigJC10` and `bigJ10`: where `bigj-ok` holds, one
  `move9` (`c-move9-at`), then a second `move9` and CONTACT
  (`try-contact-at`); the move is the three together where CONTACT
  fires, and the first `move9` alone where it does not.
- `bigj-ok` reads the digit groups `0^a 1^j` off the right side in one
  pass (`bj-go`), counting the digits and finding where they end,
  rather than parsing them to a digit list, encoding that back to runs
  and stripping those from the tape. The two seem to agree: a group
  with `a = 0` after the first is where the encoded runs would merge
  two runs of ones, and `bj-go` rejects it.
- Where CONTACT does not fire, the second `move9`'s result is the next
  move's first `move9`, and the `c-lm` CONTACT read is the next second
  `move9`'s. `c10-run6` carries them from one move to the next as an
  `Ahead` (`AhJump`; `AhLm` carries the next state's `c-lm` alone, for
  the scan or the first `move9`), so each BIGJ move runs one `move9`,
  one `c-lm` and one CONTACT. `lc-of` runs only when BIGJ does not
  fire.
- All have the types they had (`Rch l3 c0 e -> Rs l3 c0` for the
  macros); none uses an axiom. `c10-big`, `try-contact` and
  `c10-run6` keep their signatures.

## Agreement and timings

Shared 4-core container, single runs.

- `bigj-ok` and the code it replaces gave the same answer on each of
  5,000 states: 3,000 moves from `m3_c13.v` (move 87,938; 1,528 BIGJ
  moves, then 1,472 others), and 1,000 each from `m1_c9.v` and
  `m3_c11.v`.
- `bb/l3c10-bstr-h.sl` from `m3_c13.v`: the same configuration after
  3,000 moves as with the code of 713cf305 (`show-fp`), 66.7 s user
  against 158 s; at the start about 33 ms per move against 93 ms. The
  whole of piece 19 (127,969 moves) took 198 s user; the first 1,000
  moves 37 s and the next 1,000 29 s.
- The 24-piece goal, `bb/l3c10bound-110012-bstr.sh` under
  `/usr/bin/time -v`: PASS, exit 0, 10:16 wall, 2,207 s user, 3.45 GB
  peak, against 16:53, 3,764 s and 3.45 GB for 713cf305. Per piece, CPU
  seconds from `ps` every 5 s: 19: 207 (301), 20: 167 (176), 22: 88,
  23: 98, 21: 97; pieces 0 to 18 took 54 to 128 s (63 to 187 s), with
  a sum over all pieces of 2,114 s (3,655 s).
- `bb/l3c10bound.sl` after the full file list through
  `bb/l3c10-run.sl`, `--goal proved`: PASS, exit 0, 76.5 s user,
  0.63 GB peak.

## Where the time goes

- In a BIGJ move, by stack samples, most of the time seems to be the
  collector's, on the lists that `phi-run`, `xg` and `c-lm` build
  anew for each move.
- With the code of 713cf305, `OCAMLRUNPARAM=s=4M` cut 40 moves from
  `m3_c13.v` in the harness from 3.77 s to 2.27 s user, at a larger
  peak.
- Over the whole of piece 19, about half of 171 stack samples were in
  BIGJ, about a fifth in AEND (`ms-loop`) and about a tenth in DEATH's
  `rq-same`.
