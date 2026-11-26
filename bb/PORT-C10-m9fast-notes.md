# Notes on the speed of M9 and its helpers

These notes are a session's account of how the helpers that `c-move9`
(bb/l3c10.sl) and the CHAIN/ABSORB macros lean on are written for speed;
they may be wrong in places. Everything here keeps the proven types: no
macro or helper changes its signature, and nothing uses an axiom.

## What the helpers do

- `decode` (bb/l3dec.sl) reads the digits in one tail-recursive pass
  (`tdg`) and computes rho in closed form: with `V` the base-4 value of
  the digits up to the first primed pair (built in 31-digit chunks and
  joined by `vl-loop`), `S` their sum, `C` the pair costs, `M` the number
  of pairs and `A` the number read, `r = (4^(M-A+1) V - S)/3 + C`, and
  `l = (4^(M+1) - 1)/3` only where `odd-s` needs it (`rho-q`). It carries
  no proof; a run of the old and new decode side by side agreed on every
  L-moment of the first 2·10^6 and 4·10^6 moves of sim9 that were tried.
- `xg` (bb/l3jump.sl) writes the run list of `0 :: bits(X) ++ tail
  bits(T)` onto a given tail, one cell per run, with `Den`, `Xb`, `Tb`
  and `Rp` proven alongside. `c-lm`, `c-apply` and `c-walk` use it in
  place of `xtr`, `push` and `rapp`; `xt-of` gives `XT` back.
- `c-ptk` (bb/l3c10.sl) parses the register straight to tokens:
  `c-pchk` checks the run pairs and finds the tail, `c-pemit` writes the
  tokens. `c-parse` stays for bb/l3c10-desc.sl.
- `rstrip`, `rl-run`, `wk-run` and `sw-run` are tail-recursive. Each
  carries erased facts forward (a `Cat` prefix for `rstrip`, a `WkP` or
  `SwP` path for the walk and the sweep) and turns them into the old
  proof after the tail call, where they cost nothing at run time.
- `phi-run` (bb/l3phi.sl), for FE and FO, turns the word's digit pairs
  straight into tokens (`dge`), with the digit list erased.
- `c-shift` counts the repeated pairs in full only after its window
  checks pass, and builds the periodic registers run by run (`vr-runs`,
  `pw-runs`).
- bb/l3c10h.sl's `tok` reads a number with `str-nat` on its digit slice.

## Measurements

One 4-core container, OCaml 4.14, single runs, user time unless stated.
Before is fbd3a198; after is e90542ab.

| what | before | after | Rocq |
|---|---|---|---|
| sim9, 10^6 moves | 0.70 s | 0.36 s | 1.53 s |
| sim9, 10^7 moves | 32.4 s | 14.0 s | 89.7 s |
| sim9, 10^7 moves, `s=8M` | 28.5 s | 13.1 s | – |
| M9 moves in 22,269–38,513 | 0.27 s | 0.12 s | 0.86 s (`move9` alone) |
| hint stream 22,269–40,035, elapsed | 332 s | 123 s | see below |
| the same, `s=32M`, elapsed | 174 s | 81 s | – |
| CHAIN at move 38,507 (`kmain`) | 19.2 s | 10.7 s | – |

The M9 row is the difference between 11 and 1 repetitions of each M9
move, divided by 10. The hint stream checks every M9 move and every
CHAIN and ABSORB move in situ and applies Rocq's changes for the others;
Rocq's moveC10 took about 779 s over the same moves in an earlier
session's trace (`/tmp/claude-0/rocqsim/trQ`), on what may have been a
faster machine. End configurations equal Rocq's in every row.
