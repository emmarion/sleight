# Notes on porting lin3r3's window rounds for JUNC

These notes are a session's account of what `bb/l3c10-junc.sl` does
and of measurements of it; they may be wrong in places. The Rocq
counterparts are lin3r3_win.v (`win_round`, `win_rounds`),
lin3r3_junc.v (`jres`) and lin3s20_junc.v (`jtry2`, `juncS`) in
busycoq-L3 c8664dd.

## What is there

- `win-round` (erased) seems to be `win_round` for one round: for a
  register `Tp T1 Wu` whose upper tokens `Wu` are all `T0` or `T1`, a
  window run of the machine (`TRun`, from state 1 at the first window
  cell to state 2 on a 1 followed by `0 0`, never leaving the window)
  lifts, for any outer tape `O`, to a run from the L-moment to the
  L-moment with three more 1s on the left. The gadget, the sweep and
  the walk are `l3round.sl`'s `gadget`, `sw-ok` and `wk-ok`; the window
  is framed by `trun-frame`.
- The sweep and walk witnesses over `Wu` come from `Fw`, which
  `fw-of` builds while checking that `Wu` holds no `Tp`; `fw-sw` turns
  it into `Sw (3) Wu (SEnd K)` and `Wk K (Tp) (Tp T1 Wu)` by induction,
  so no part of the proof is computed at run time.
- `jw-loop` runs `K` rounds with `tsim` on one window, the junction's
  cells followed by all `8 K` blank cells at once (Rocq adds 8 per
  round; the machine's run is the same where Rocq's succeeds, since a
  round that stays inside 8 blanks stays inside more).
- `c-junc-w` splits the register's tokens after `a` upper tokens,
  builds the window from the lowest tokens, the tail and the junction
  word (`takep`), takes the blanks with `rest-take-x`, runs
  `jw-loop`, checks that the final window equals the cells of the
  proposed lowest digits, out tail and blanks (`bsame`), and builds the
  configuration that `lm-out` builds, with its denotation.
- `c-junc` (`bb/l3c10-far2.sl`) takes the split, `K`, the lowest
  digits, the tail and the blanks from the existing unproven search
  (`jx-plan`, which is `jx-try` and the parse that `jx-prop` used),
  tries `c-junc-w`, and falls back to `c-certify-c` over `jx-prop`'s
  proposal, as before, when `c-junc-w` answers `RsNo`.
- The macro types stay `Rch l3 c0 e -> Rs l3 c0`; no axiom is used.

Not ported: Rocq's six closed junction lemmas and the canonicity
results (the canonicity test stays an unproven choice inside the
search), and `allb1` (`jx-try` still copies the upper digits once per
split tried). Sleight's `jx-try` already tries the next split only
after the current one fails, which seems to be what `jtry2` fixes in
the extraction. `juncS`'s scheduling has no counterpart here: JUNC is
named by index in the scripts of pieces 22 to 24 and is not in the
dispatcher of the other pieces.

## Measurements

Instrumented copies of the extracted program of
`bb/l3c10bound-110012-bstr.sh`, pieces 22 to 24 only, wall seconds of
the whole `c-junc` call (four junctions: two in piece 22, one each in
23 and 24), on a shared 4-core container:

| piece | junctions | head | here | of which `jx-plan` |
|---|---|---|---|---|
| 22 | 2 | 2.83 | 0.08 | 0.04 |
| 23 | 1 | 2.50 | 0.10 | 0.04 |
| 24 | 1 | 2.09 | 0.44 | 0.20 |

- At head, about 6.8 s of the 7.4 s seem to be the M9 replay of
  `c-certify-c` and the rest `jx-prop`. Against about 2,050 to
  2,600 s of user time for the goal, JUNC seems to be about 0.3% of
  it.
- At head, the replay makes one M9 move per window round, and each
  move parses and compares the whole configuration, so a junction
  seems to cost about `K` times the register's length. Here the
  rounds touch only the window, and what remains linear in the
  register is done a few times per junction: `tdigits`, the
  copy and check of each split tried, the token split, `fw-of`, and
  the output's runs.
- In each of the four junctions `c-junc-w` answers `RsOk`, and with a
  local edit that compared its result with `jx-prop`'s proposal and
  failed the move otherwise, pieces 22 to 24 still answered `ROk`, so
  the configurations seem to be the ones the replay produced.

Uninstrumented compiled programs, one piece at a time, head's (the
extraction of 52565672, whose code 1d4fef80 shares) and this one's
alternately, on the same container under a load average of
about 8 to 10 from other work:

| piece | head user s | here user s |
|---|---|---|
| 22 | 114.5 | 114.1 |
| 23 | 88.6 | 88.0 |
| 24 | 92.4 | 90.5 |

The differences are of the size of the noise between runs here, so
they seem to say only that nothing got slower.

`bb/l3c10bound-110012-bstr.sh` under `/usr/bin/time -v`, head (from
`git archive` of 1d4fef80) and then this code, back to back on the
same container under that load: head PASS, exit 0, 32:51 wall,
2,626 s user, 3.44 GB peak; here PASS, exit 0, 33:47 wall, 2,666 s
user, 3.45 GB peak. `bb/l3c10bound.sl` after that script's file list
without its goal file, with `--goal proved`: PASS, exit 0, 117 s
wall, 111 s user, both at head and here; the 491 warnings are the same
apart from line numbers in `bb/l3c10-far2.sl`.
