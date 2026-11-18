# Round 6 review notes: BUGS.md text added since 4bb81cc

Scope: `git diff 4bb81cc -- BUGS.md` (entries 23-26 and the additions
to 13, 18, and 19). All of DESIGN.md was read first. Every reproduction
was re-run with `_build/default/bin/main.exe` and `_build/release/slc`;
`self/`, `lib/`, `bin/`, and `std/` are unchanged since `5fba336`, and
both binaries are newer than their sources. Outputs are in the session
scratchpad, not the repo.

## Errors found and fixed

1. Entry 18: "both compilers overflow the default 8 MB stack on it" left
   out the binary `slc --build` makes, which also dies with `Stack
   overflow` (exit 2) at 8 MB; the reference dies with SIGSEGV (139) and
   `slc --interpret` with `Stack overflow` (2). `slc --build` itself
   compiles it at 8 MB. Now names all three.
2. Entry 23: "`show-at` ... starts at a depth of 100000" put the seed in
   `show-at`; its callers seed it (`self/elab.sl:4730` in `show-typed`,
   `self/interp.sl:15` in `final-text`). Reworded with the two lines.
3. Entry 24: "`show-at`'s 100000 ... is not mentioned there" was stated
   flatly, though README:256's "1000000 or 100000" for "the interpreter
   and the generated printer" could be read as covering it. Hedged to
   "seems not to be".
4. Entry 25: "compiled and (for the first) under `--interpret`"
   underclaimed: `02_bfalse`, `04_lit`, and `05_lit_missing` all give the
   same output under `--interpret` as compiled. Now "compiled and under
   `--interpret`".
5. Entry 25: did not mention that `self/README.md:301-302` already says
   `slc` "may report a few more [errors] that follow from it"; the false
   messages found do not follow from the first error. Added the quote,
   without a verdict.
6. Entry 26: "`lib/ffi.ml:89` maps [the three names] to
   `Ffi_core.array_blit_imm` (`lib/ffi.ml:117-119`)" had the citations
   swapped: `:117-119` map the names to `blit_imm`, and `:89` defines
   `blit_imm`, which calls `Ffi_core.array_blit_imm`. Fixed, with an
   Oxford comma added to the list.
7. Entry 26: "in the interpreter every element is a heap-allocated
   `VWord`" overclaimed: that holds for this reproduction's `U62`s, and
   was not checked for every type an `Imm` can cover. Narrowed to "such
   an element, a `U62` in the reproduction below".
8. Entry 26: "§31 lets a run crash only 'where the host cannot represent
   what is asked of it'" put an "only" in DESIGN.md's mouth; §31 says a
   real run "may crash where the host cannot represent what is asked of
   it". Reworded to quote that and say the program seems not to approach
   it (the same kind of error as round 5's fix 6 to entry 23).
9. Entry 26: "Only `array-blit-imm` was run from Sleight" is out of
   date. `proposals/self-formal/proto/review6/08_blit_many_imm_interp.sl`
   (from the 04/08 round-6 reviewer) was re-run here: SIGSEGV in 2 of 2
   runs, "runtime error: not an extern integer: _" under
   `OCAMLRUNPARAM=s=4k`, and `0` under `slc --interpret`. Its `array-blit`
   control and its `--build` were not re-run here. The entry now says
   this and that `array-move-imm` was not run.

## Confirmed without change

- Entry 13: reference `2:45` "omit it or write `(absurd Zero)`", slc
  (emit and `--interpret`) `2:44` "omit it or write `absurd`"; column 44
  is `((Zero)`, 45 is `(Zero)`. README:304-309 says what is quoted.
- Entry 18: reference and the `--build` binary print `confine ok` /
  `stat cwd ok`; `slc --interpret` prints `confine ok` / `stat cwd
  refused`; with 999999 pads `slc --interpret` prints `stat cwd ok`; all
  exit 0. `heap-strs-fuel` is `self/eval.sl:1018`; `heap-strs`,
  `heap-pairs`, and `heap-jobs` each return `Nil` on `Zero` fuel. The
  list holds 1000001 entries, one more than the fuel. §31 quote exact.
- Entry 19: with `rf_b.sl` or `01_late_error.sl` second, the reference
  prints `effect` and exits 0; slc emit, `--interpret`, and `--build`
  exit 1 with the second file's error, and `--build` writes no binary.
- Entry 23: all four files re-run, emit and `--interpret` alike for
  `match` and `dump`: 49,999 `Cons _ 0` then `Cons _ _ _)`, against
  50002 and `Nil _)` from the reference and the `show_at_fn` binary. The
  arithmetic checks: element k's `show-at` gets 100000 - 2k, and its
  head needs 100000 - 2k >= 3, so elements 0-49998 print. §45, §28, §31,
  and §54 quotes exact.
- Entry 24: README:254-258, 385-386, 463-465, 61-62, and 128 say what is
  quoted; `core.sl:3614` (1000000000 in `MkMacros`'s `fuel` field),
  MANUAL.md:162, `emit.sl:4`, `emit.sl:1380`, `runtime.ml:18`,
  `elab-main.sl:752`, and `:509` are as cited. The only `1000000` in
  `self/` is `eval.sl:1018`.
- Entry 25: outputs as quoted; `--first-error` prints the first error and
  `slc: stopped at the first error (--first-error)`. `elab-main.sl:2209-2216`
  and `:672-678` take `env-set-tokens` when `env-failed` holds;
  `eval.sl:51` maps `BToken` to `Some 0`. `BTrue` is `Bool`'s first
  constructor (`lib/prelude.sl:1254`). §27 and §28 quotes exact.
- Entry 26: three runs SIGSEGV (139); `OCAMLRUNPARAM=s=4k` gives the
  quoted message; an `array-blit` variant (scratchpad) prints `0`;
  reference `--build` dies with 139 and writes nothing; `slc --interpret`
  prints `0`; `self/core.sl:482` is as cited; `lib/ffi_core.ml:318`
  binds `blit_words` to `caml_blit_bytes`.
- Numbering untouched; no entry states a decision.

## Unsure

- §42 says an extern implementation and its model "either may crash
  where the other does not (§31)". A reader might take that as
  permitting entry 26's crash, or (through the §31 reference) as bound
  by §31's condition. Not raised in the entry. A `--no-extern` run of
  `blit_imm_interp.sl` overflowed the 8 MB stack; one under `ulimit -s
  unlimited` had not finished when this was written.
- Entry 19's closing "Which order is wanted" now also covers the
  acceptance difference. §71's "nothing is printed, applied or written
  after elaboration" might be read as placing the driver after the whole
  unit is elaborated; DESIGN.md seems to say nothing more direct. Left
  alone.
- Entry 19's "`slc`, compiled or under `--interpret`" (matching the
  older text) leaves "compiled" ambiguous between slc's emit mode and
  `--build`; all three behave as stated.
- Entry 24 is drift in `self/README.md` rather than an implementation
  defect, which is what BUGS.md's preamble says the file holds (round 5
  note 8, still open).
