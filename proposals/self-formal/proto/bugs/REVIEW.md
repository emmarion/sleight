# Review of BUGS.md entries 23-25 and the extensions to 13, 18, and 19

Adversarial review of the text added in `30304d4` (`git diff 4bb81cc --
BUGS.md`). Every reproduction was re-run with the reference
`_build/default/bin/main.exe` and `_build/release/slc` (whose sources,
`self/`, `lib/`, `bin/`, and `std/`, are unchanged since `5fba336`).
Outputs are in the session scratchpad, not the repo.

1. Entry 13 extension: confirmed. `aftererr/17_type_error_first.sl`
   gives `2:45: ... write \`(absurd Zero)\`` from the reference and
   `2:44: ... write \`absurd\`` from `slc` (emit and `--interpret`),
   both exit 1. `self/README.md:304-309` says what the entry quotes.
2. Entry 18 extension: confirmed. Reference and the `--build` binary
   print `confine ok` / `stat cwd ok`, `slc --interpret` prints
   `confine ok` / `stat cwd refused`, all exit 0; with `pad 999999`,
   `slc --interpret` prints `stat cwd ok`. `self/eval.sl:1018` is
   `heap-strs-fuel`; it feeds `heap-strs`, `heap-pairs` (through
   `heap-jobs`), and `heap-jobs` at `:1055`, `:1146`, and `:1159`.
   The §31 quote is exact.
3. Entry 18, fixed: the run needs `ulimit -s unlimited`; at the
   default 8 MB stack `slc --interpret` dies with `Stack overflow`
   (exit 2) and the reference with SIGSEGV (exit 139). The entry did
   not say so; it does now.
4. Entry 23: confirmed for all four files. The `--interpret` outputs
   hold 49,999 `Cons _ 0` and end `Cons _ _ _)`; the reference's (and
   the `show_at_fn` binary's) hold 50002 and end `Nil _)`. Exit codes:
   0 for `final` and `fn`, 1 for `match` and `dump`, on both sides.
   `show-typed` (`elab.sl:4727`), `entry-value` (`:4888`), and
   `final-text` (`interp.sl:15`) each start `show-at` at 100000.
5. Entry 23, fixed: the cited range `elab.sl:4680-4717` stopped at
   `shown-field`'s decrement; `shown-field` runs to `:4725`, so the
   range is now `4680-4725`.
6. Entry 23, fixed: "§45, which prints `_` only for" put an "only"
   in DESIGN.md's mouth that its text does not say (it lists the `_`
   cases after "Any other value prints by its type"). Reworded to
   "whose cases that print `_` are". Both quotes are exact substrings.
   The §28 quote is exact; §54 does defer `dump-context` to MANUAL.md.
7. Entry 23's "the emitted OCaml printer seems to have no depth bound"
   does not contradict entry 24's `show-fuel` (`emit.sl:4`): that fuel
   bounds `show-type`, which generates one printer per type at compile
   time (`emit.sl:1380`), not the depth of a printed value.
8. Entry 24: each bullet checked against the code. `core.sl:3614`
   holds 1000000000 (in `empty-env`'s `MkMacros`), and MANUAL.md:162
   says slc's fuel is 1000000000. `show_any` is `runtime.ml:18`.
   `elab-expr-demand` is `elab-main.sl:752` with `sugar` fourth among
   the `subterm`s; `env-expand` starts at `:509`. The reference runs
   macros (`tests/macro_body.sl` passes). README `:61-62` and `:128`
   say what is quoted. Open question for the owner, not changed: this
   entry is documentation drift in `self/README.md` rather than a
   defect in the implementation, which is what BUGS.md's preamble says
   the file holds.
9. Entry 24, fixed: Oxford comma in "`fuel`, `callbacks`, and a `hop-`
   index". Entry 18 likewise for "`heap-pairs`, and `heap-jobs`".
10. Entry 25: confirmed. `02_bfalse`, `04_lit`, and `17` print the
    quoted false second message under emit and `--interpret`;
    `05_lit_missing` prints only `first`; the reference prints only the
    first error; all exit 1; `--first-error` prints the first error
    plus `slc: stopped at the first error (--first-error)`. The cited
    lines `elab-main.sl:2209-2216` and `:672-678` take `env-set-tokens`
    when `env-failed` holds, and `eval.sl:51` maps `BToken` to `Some 0`.
    The §27 and §28 quotes are exact. `10-slc-after-error.md` does
    report the `Hypothetical` and ungated-macro cases.
11. Entry 25, fixed: "DESIGN.md does not say whether more than one
    error is reported" hedged to "seems not to say" (rule 1); §4 says
    warnings "do not stop elaboration", which a reader might take as
    implying errors do.
12. Entry 19 extension: confirmed for both second files. The reference
    prints `effect` and exits 0. `slc --interpret`, emit, and `--build`
    exit 1 with the second file's error (for `rf_b.sl`, preceded by a
    "never closed" warning and a `bin/shape` note), and `--build`
    writes no binary.
13. Numbering (rule 15) is undisturbed: 1, 13, 18-25, nothing moved.
    No entry states a design decision; each defers with "is not
    decided here" or "Which answer is wanted is not decided here".
    Pre-existing lists in entry 18 without Oxford commas (`sub`, ...,
    `nat-mod` and `str-split`; the `Er...` list) were left alone, as
    not part of this change.
