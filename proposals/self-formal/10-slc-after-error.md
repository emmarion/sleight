# 10. What slc does with run-position forms after the first error

Written by an agent at the coordinator's request, as a follow-up to
01-spec-shape.md §3.7 and its review notes. Nothing in it is approved,
and nothing here is a design decision (CLAUDE.md rules 1, 11). Where
this file and DESIGN.md disagree, DESIGN.md is right. Code citations
are to the tree at commit `5fba336`; the readings of slc's source are
this agent's and may be wrong in detail. Every message quoted below was
observed by running the tests; a behaviour marked as read was not.

Implementations: the reference is `_build/default/bin/main.exe`; slc is
`_build/release/slc` (built after the last change to `self/`), run as
`slc --interpret`, as `slc` with no flag (which writes the OCaml to
standard output when there is no error), and as `slc --build`. On every
test below the three slc modes printed byte-identical output and the
same exit code, so they are not distinguished further.

## 1. Summary

- DESIGN.md says nothing explicit about reporting more than one error
  (01 §3.7). Two texts come near. §4's "Warnings go to standard error
  and do not stop elaboration" may be read as implying that an error
  does stop it; on that reading slc's going on is itself a difference
  from DESIGN.md. And §54 says that `dump-context` "stops elaboration
  with a report of the context", while slc goes on after that report
  too: on `tests/dump_context.sl` it prints two more errors and a
  warning after the report, where the reference prints the report
  alone. The reference stops at the first error. slc records errors and
  goes on (self/README.md, "Errors are values"), and `--first-error`
  only cuts the report short (self/main.sl:45). Apart from those two
  texts, everything below is a difference from the reference, not from
  DESIGN.md, except where a message slc prints is false.
- After an error, slc does not run run-position code through its
  evaluator for `let`s, calls, constructor applications, run-position
  `match`es, `coerce`, or `let-match`, and does not compile or run a
  `native-compute` (`proto/review7/10_*.sl` for the last three). Macro
  expansion is not gated: a macro bound before the error still runs, at
  compile time, after it, and the macro-world primitives it calls answer
  as before (`gensym` and `read-file` were run), except that `resolve`
  answers `RHypothetical` for a binder that holds the token
  (`proto/review7/10_macro_prims.sl`).
- A nullary `(Zero)` bound after the error is `Settled`, but it seems
  not to hold the value `(Zero)`. A run-position
  `let` whose right-hand side needed no hoisted temporaries gets its
  binders set to the erased token (`env-set-tokens`), and slc's
  discriminant read takes a token as the word 0 (`self/eval.sl:51`). So
  the binder reads as the `Nat` 0, a `String` as `(SNil)`, or, for a
  tagged enum, as its first fieldless constructor, whatever the
  right-hand side was. `(Zero)` reads as `0` only by coincidence. Other
  kinds of type were not surveyed; one single-constructor case is in
  the review notes.
- That gives false messages: after an error, `(let ((many x)) (BFalse))`
  followed by `(comptime-match many x (BFalse))` reports "expected
  `BFalse`, got `(BTrue)`"; `x` bound to `3`, to `(Succ y)`, to a call,
  or to a variable holding `1` is reported as `0`. It also hides errors:
  `(comptime-match many x (BTrue))` on that `BFalse` binder, and
  `(comptime-match many x (Zero))` on `x` bound to `3`, pass silently.
  Where the binder is left `Hypothetical` (a right-hand side that needed
  temporaries, or the fields of a `let-match`), slc reports that the
  scrutinee is not `Settled`, which DESIGN.md §27-§29 would, in this
  agent's reading, make it. A string binder is not left `Hypothetical`:
  it holds the token too (`comptime-match` reads it as `(SNil)`), but
  the check on the message of `compile-warn` and `compile-error` words
  any stored value that is not a string as "is `Hypothetical`"
  (`elab.sl:2585-2587`; `14_string_msg.sl`,
  `proto/review7/10_string_token.sl`).
- No test changed acceptance: slc exits 1 once its message list holds
  an error (`self/main.sl:139-143`), and every test exits 1 on both
  implementations. The defects, if they are taken as such, seem to be
  in the second and later messages only; §4 says how far that was
  checked. BUGS.md 25 records them.

## 2. The traced code path

All under `self/`. "Failed" means `env-failed` (`core.sl:2533`), which
is true once any `SaidError` is in the environment's message list. No
writer of the list was seen to drop a `SaidError` (§4 says which were
read), so once failed, always failed, as far as was checked.

**The gates.** Four places test `(env-run-pos …)` together with
`(not $ env-failed …)` before running code at compile time, as 01
says:

- `elab-main.sl:539`, `hoist-temp`: a hoisted temporary (an argument
  that is not already a variable, say) is run at once in run position.
  When failed, it is instead kept as an `SLet` frame on the context,
  so the context it returns is non-empty.
- `elab-main.sl:545`, `run-form`: the end of `elab-expr-demand`
  (called at `:1168`) runs a whole run-position expression and turns
  its code into constants. When failed, it returns the code unrun.
- `elab-main.sl:739`, in `call-returns`: a call, a primitive, or a
  `world-do` in run position is run and its results set `Settled`. When
  failed, the call code is returned unrun.
- `elab-main.sl:2152`, `let-match`: the `run` flag; when false the
  statement takes the hypothetical path (`:2168` on), so its fields are
  `Hypothetical` (`proto/review7/10_letmatch.sl`: a later
  `comptime-match` on a field says it needs a `Settled` scrutinee).

Two tests of `env-failed` alone also keep code from running at compile
time: `native-compute` (`elab-main.sl:869`) gives error results without
compiling or running anything (`proto/review7/10_native.sl`: a later
`comptime-match` on its binder reports "scrutinee is not a datatype
value" and "got `_`"), and a file's final expression is not run by
`env-run-final` (`:3393`). Read only: `:2537`, `:2560`, and `:2565`
stop elaborating a `settled-ty-apply` or `settled-val-apply` once
failed.

Two more places, not among 01's four, make their own `env-failed` test
before running a binder's code with `env-run-let`, and decide what the
binder holds when they do not run it:

- `elab-main.sl:2209-2216`, `elab-let`. If the right-hand side's
  context `ctx3` is non-empty (some temporary was left unrun by
  `:539`), `env3` is `env2` and the binders stay as `bind-let` made them,
  `Hypothetical`. If `ctx3` is empty, `run` is true, and the inner
  environment is failed, the binders are set by `env-set-tokens`
  (`eval.sl:1640-1643`), which gives each a `Settled` state holding a
  fresh `BToken` block (`set-state-closed`, `core.sl:2439`;
  `heap-set-closed`, `core.sl:2433-2437`). The same branch (`:2216`)
  is taken, failed or not, by a `let` with no non-erased binder
  (`pos-mult expect` is then `Erased`), whose results DESIGN.md §27
  makes "`Settled` with the token of §5".
- `elab-main.sl:672-678`, `open-bind`, does much the same for the
  anonymous entry of an `open-adt` or `open-absurd`, with one difference
  read but not tested: there a non-empty context (`:675`) also gives
  the token, failed or not, where `elab-let` leaves the binder
  `Hypothetical`. An erased open (`:673`) gets the token too.

slc already treats this token as a stand-in in one place:
`resolve-answer` (`eval.sl:1335`, using `stand-in`, `eval.sl:1321-1324`)
answers as for a `Hypothetical` entry when the environment is failed
and a non-erased entry (`mult-is-many` holds for `many` and `unique`,
`core.sl:187-188`) holds a `BToken`. In
`proto/review7/10_macro_prims.sl` it answers `RHypothetical` for a
`let` binder after the error, where the reference without the error
answers `RSettled`; `tests/macro_resolve_after_error_bad.sl` reaches it
too, and slc's second message there, the macro's own "not settled", is
false in the same way. `comptime-match` and `show-typed` have no such
test, and `message-of` (`elab.sl:2578-2587`) words a token as
`Hypothetical` without one. This suggests the token is meant as a "not
run" marker, but that was not confirmed.

**Forwarding does not repair it.** After `env-set-tokens`,
`forward-binders` (`elab.sl:999-1004`) calls `forward-binder`
(`core.sl:3039-3045`) for a right-hand side whose term is a variable
`y`. For a `many` binder in run position this is `minted-from`
(`core.sl:3029-3037`), which builds `SSettled v m` with `v` taken from
the destination (the token) and only `m` from the source. So
`(let ((many x)) y)`, with `y` `Settled` to `1` before the error, leaves
`x` holding the token.

**How the token is read.** `comptime-match` (`elab.sl:4733`) checks
`is-settled` (`:4755-4758`); a token entry passes. It then calls
`env-destruct` (`eval.sl:1627-1631`) → `destruct` (`eval.sl:433-439`)
→ `dispatch` (`eval.sl:398-410`), which first asks `word-of-block`
(`eval.sl:44-52`). That has the case `((BToken _) (Some _ 0))`. For an
`extern`-backed type the word 0 is decoded by `ext-destruct`, as `Zero`
for `Nat` and as `SNil` for `String`; for a tagged enum,
`fieldless-index` maps it to the first fieldless constructor (`BTrue`
in `Bool`, `None` in `Maybe`). `headed-by` (`eval.sl:441-442`) then
compares indices, and the mismatch message (`elab.sl:4784`) prints the
value with `show-typed` (`elab.sl:4727-4731`), which renders the token
through the same reading: `0` for `Nat`, `(SNil)` for `String`,
`(BTrue)` for `Bool`, `(None _)` for `Maybe`. For a `Hypothetical`
entry `settled-ref` is `None` and `show-typed` prints `` `?` ``, after
the separate "needs a Settled scrutinee" error at `:4758`, so such a
`comptime-match` prints two errors. When the read passes, the pattern
is then forced onto the scrutinee; in 03 that equates `x`, whose rule
is `(BFalse)`, with `(BTrue)`, and `elab.sl:4790-4791` drops the
resulting "internal: the verified value contradicts the facts in
force" message once failed, so 03 prints nothing (read, not tested).

**Why `(Zero)` and not `(Succ (Zero))`.** `(Zero)` has no arguments, so
the constructor application (`elab-main.sl:1141-1158`) hoists nothing,
`run-form` refuses at `:545`, `ctx3` is empty, and the binder gets the
token. In `(Succ (Zero))` the argument `(Zero)` is hoisted through
`hoist-argument` (`:690-698`) and `hoist-temp`, which refuses at `:539`
and leaves a frame, so `ctx3` is non-empty and the binder is
`Hypothetical` (`proto/review4/01_after_error_succ.sl`). `(Succ y)`,
with `y` already a variable, hoists nothing and gets the token
(`07_succ_var.sl`), as does a call `(f y)` (`08_call_var.sl`). A
literal `3` also gets the token (`04_lit.sl`), and so do a string
literal `"abc"` and a `Settled` string variable
(`proto/review7/10_string_token.sl`: `comptime-match` reads both as
`(SNil)`). `14_string_msg.sl`'s "`s` is `Hypothetical`" is
`message-of`'s wording for that token (`elab.sl:2585-2587`), not the
binder's state.

**What still runs.** `expand` (`elab-main.sl:555`) and the macro call
it makes have no `env-failed` test, so a macro bound before the error
is still expanded after it (`11_macro_rhs.sl`, `15_macro_alias.sl`; a
self-expanding macro bound before the error still hits "more than 10000
macro expansions"). Of the macro-world primitives (`macro-prim`,
`eval.sl:1540` on) only `resolve` tests `env-failed`; `gensym` and
`read-file` answered after the error as without it
(`proto/review7/10_macro_prims.sl`). A `def-fns` after the error still
closes its group (`elab-main.sl:2267-2272`, `env-close-group`), so its
functions are `Settled`: `resolve` answers `RSettled` for one
(`10_macro_prims.sl`); only calls of them do not run. In
`proto/review2/after_error_call.sl` the binder of such a call is
`Hypothetical` because its argument `(Zero)` is hoisted, as in
`(Succ (Zero))` above; with a variable argument the binder of a call
gets the token (`08_call_var.sl`, whose `f` is bound before the
error). Reading a value that was `Settled` before the
error is unaffected: `comptime-match` on it, and on the fields that
binds, reads the real value (`16_pre_error_field.sl`), and `compile-error
s` with such an `s` prints its text.

## 3. Test matrix

Sources are under `proto/aftererr/`. The reference prints only its
first message on every test, and every test exits 1 on every
implementation. The slc column is what slc prints after the first
message, which is `first` and agrees with the reference except in test
17. "False?" judges the message against what DESIGN.md §27-§29 would
make the value had the run-position form run.

| Test | After the error | slc's later messages | False? |
|---|---|---|---|
| 01_zero_ok | `x` = `(Zero)`; `comptime-match` `Zero` | none | no (coincidence) |
| 02_bfalse | `x` = `(BFalse)`; `comptime-match` `BFalse` | expected `BFalse`, got `(BTrue)` | yes |
| 03_bfalse_missing | `x` = `(BFalse)`; `comptime-match` `BTrue` | none | missing error |
| 04_lit | `x` = `3`; `comptime-match` `Succ` | expected `Succ`, got 0 | yes |
| 05_lit_missing | `x` = `3`; `comptime-match` `Zero` | none | missing error |
| 06_var | `y` = 1 before; `x` = `y`; `Succ` | expected `Succ`, got 0 | yes |
| 07_succ_var | `y` = 0 before; `x` = `(Succ y)`; `Succ` | expected `Succ`, got 0 | yes |
| 08_call_var | `x` = `(f y)`, `f` = `Succ`; `Succ` | expected `Succ`, got 0 | yes |
| 09_match | `x` = run-position `match` giving `BFalse` | expected `BFalse`, got `(BTrue)` | yes |
| 10_two_binders | `a b` = `(values (BFalse) 5)` | got `(BTrue)`; got 0 | yes (both) |
| 11_macro_rhs | `x` = `(m)`, `m` expands to `(BFalse)` | expected `BFalse`, got `(BTrue)`; then the `compile-warn` | yes |
| 12_succ_hoisted | `x` = `(Succ (Zero))`; `Succ` | needs a Settled scrutinee; expected `Succ`, got `?` | yes (both) |
| 13_inline | `comptime-match many (Succ (Zero)) (Succ _)` | the same two | yes (both) |
| 14_string_msg | `s` = `"abc"`; `compile-warn s`, `compile-error s` | `s` is `Hypothetical` (twice) | yes (both): by §27-§29 `s` would be `Settled`, and in slc it is `Settled` too, holding the token, which `message-of` words as `Hypothetical` |
| 15_macro_alias | `m` bound before; `m2` = `m` after; `(m)`, `(m2)` | `Zero` is not a statement (from `(m)`); `m2` is a macro, expanded only where its head is constant-known | first no; second yes: `m2` is `Settled` in slc too but holds the token, while by §29 site 3 it would forward `m`'s value and §6 would expand it |
| 16_pre_error_field | `y` = 2 before; `comptime-match y (Succ p)`, `p` `Zero` | expected `Zero`, got 1 | no |
| 17_type_error_first | first error is a refuted branch, not `compile-error` | expected `BFalse`, got `(BTrue)`; `end` | the second, probably: it asks what an ill-formed `let` would have computed (`BFalse`, as `y` is `(Succ (Zero))`) |

Notes on the table:

- 01 and 03 together show that what the binder reads as is not
  computed: 01 reads `(Zero)` where `(Zero)` was written, and 03 reads
  `(BTrue)` where `(BFalse)` was. The token reads as the first fieldless
  constructor whatever was written.
- In 13 there is no `let`: `comptime-scrutinee` (`elab-main.sl:1185-
  1195`) elaborates the form, `run-form` refuses, and `settled-from`
  (`elab.sl:2879-2884`) finds no variable code to copy, so the entry is
  `Hypothetical`.
- 17's first message differs from the reference's in wording ("write
  `absurd`" against "write `(absurd Zero)`") and column (44 against 45).
  That is outside this file's question. self/README.md says the first
  message is the reference's on every error test (of the test suite)
  and already allows the column to differ; the wording difference is
  not covered by that, so it may be worth a look.
- With `--first-error`, slc prints only its first message (`first`, or
  17's refuted branch) and the trailer
  (`slc: stopped at the first error (--first-error)`) on every test that
  has a second message, so none of the false messages is shown.

Review tests under `proto/review7/`, each with a `(compile-error
"first")` before the forms shown, in the same columns:

| Test | After the error | slc's later messages | False? |
|---|---|---|---|
| 10_letmatch | `y` = 1 before; `let-match many y (Succ p)`; `comptime-match` `p` `Zero` | needs a Settled scrutinee; expected `Zero`, got `?` | yes (both) |
| 10_coerce | `y` = 1 before; `x` = `(coerce y (coercible-refl (Shared) y))`; `Succ` | expected `Succ`, got 0 | yes |
| 10_settled_value | `y` = `(BFalse)` before; `v` = `settled-value` of `(settled-of many y)`; `BFalse` | expected `BFalse`, got `(BTrue)` | yes |
| 10_native | `f` gives `(BFalse)`, bound before; `x` = `(native-compute f)`; `BFalse` | scrutinee is not a datatype value; expected `BFalse`, got `_` | yes (both) |
| 10_string_token | `s` = `"abc"`, `t` = a pre-error `"abc"`; `SCons` on each; `compile-warn t` | got `(SNil)` (twice); `t` is `Hypothetical` | yes (all three) |
| 10_macro_prims | a pre-error macro's `resolve` on a later `def-fns` name, a later `let` binder, and a pre-error binder; its `gensym` and `read-file` | `RSettled`, `RHypothetical`, `RSettled`; both primitives answered | the `RHypothetical` |

## 4. Are reported messages false?

[A] Yes, in this agent's reading, for every "yes" row above: each one
states a fact about the program (a value's constructor, its number, or
that it is `Hypothetical`) that DESIGN.md §27 ("its results become
`Settled` with the resulting values"), §28, and §29 site 1 (site 3
for 06 and 15's second) contradict. As a check on the "computed value"
column, each reproducer was also run on the reference with the
`compile-error "first"` line removed (15 also without `(m)`): every
`comptime-match` of a "yes" row passed, 03 and 05 failed with the error
slc omits, 14 printed `abc` twice, and `(m2)` expanded.
The first message is never affected, and acceptance is never affected,
since slc fails on the first error whatever follows. DESIGN.md does not
require a second message at all, so the reading that these are defects
rests on a message being false, not on its being extra. Two further
kinds of difference were seen that are not false messages: errors that
do not appear (03, 05), which DESIGN.md cannot require since it
requires no second message, and genuine later errors that the reference
would not reach (15's first).

[A] One case looked for and not found: a later error that slc would
have to report and does not, in a way that could make a program
accepted. Since `env-failed` is monotone and decides the exit code,
this agent does not see how one could arise, but did not prove it.

## 5. Suggested follow-ups

These are options for the owner, not recommendations to adopt.

1. Make the post-error state honest. Either leave a `let`'s binders
   `Hypothetical` when the gate refuses (the `ctx3`-non-empty branch
   already does), or give them a distinct "not run" state, and have
   `comptime-match`, head dispatch, and the `compile-error` message
   check say nothing about such an entry. That would remove every "yes"
   row; the cost is losing whatever the token assignment at
   `elab-main.sl:2216` (and `:678`) is there to protect, which was not
   investigated. A "not run" test of the kind `resolve-answer` already
   makes (`eval.sl:1335`) may be a starting point.
2. Alternatively, keep running run-position code after an error, as
   the reference would if it continued. That would make the later
   messages true, but slc would then run user code at compile time
   after a known error, including loops bounded only by fuel.
3. Stop at the first error by default and keep the current behaviour
   behind a flag; this matches the reference but discards slc's design
   choice in self/README.md.
4. Separately from any of these, `word-of-block` reading a `BToken` as
   the word 0 (`eval.sl:51`) may deserve a look on its own: this file
   found it reachable only after an error, through `env-set-tokens`, but
   did not check every other caller.

## Review notes

An adversarial review re-ran all 17 reproducers on the reference and
on slc (`--interpret` and compiled; byte-identical, exit 1 everywhere)
and opened every cited line. Every quoted message and every line
citation matched; `self/` is unchanged from `5fba336` to the review's
HEAD. Errors found and changes made:

1. The summary said the nullary `(Zero)` "does not" get a `Settled`
   value. Its binder is `Settled` (the token's state is `SSettled`);
   what it lacks is the value `(Zero)`. Reworded, and the quote of 01
   corrected to its own words ("is still `Settled`").
2. "The first fieldless constructor of its type" was stated for every
   type. `dispatch` (`eval.sl:398-410`) reads a token that way only for
   a tagged enum, and as the number for an `extern` type. Narrowed. A
   single-constructor type behaves differently: after the error,
   `(let ((many x)) (MkPair (Nat) (Nat) 1 2))` then
   `(comptime-match many x (MkPair _ _ a b))` passes, and
   `(comptime-match many a (Succ _))` reports "expected `Succ`, got
   `_`", another false message (not traced). `(Cons (Nat) 1 n)` with
   `n` bound before the error reads as `(Nil _)`, and
   `(Some (Nat) 4)` as `(None _)`, consistent with the narrowed text.
3. The summary attributed every `Hypothetical` binder to hoisted
   temporaries, while §2 says the string-literal case (14) was not
   traced. Aligned.
4. `open-bind` was said to do "the same" as `elab-let`; at `:675` a
   non-empty context gives the token rather than `Hypothetical`.
   Noted (read only).
5. Missed in §2: `resolve-answer` (`eval.sl:1335`) with `stand-in`
   (`eval.sl:1321-1324`) already treats a `BToken` in a failed
   environment as `Hypothetical`. Added, and mentioned in follow-up 1;
   it bears on what the token assignment "protects".
6. `proto/review2/after_error_call.sl` was cited as showing that calls
   do not run. Its binder is `Hypothetical` because the argument
   `(Zero)` is hoisted, the same mechanism as `(Succ (Zero))`; the
   "functions are `Settled`" part is from reading only. Reworded.
7. Table row 15 said `m2` "would be `Settled`", implying it is not.
   It is `Settled` in slc (holding the token; the message is the plain
   one of `macro-refused`, `elab.sl:2801-2806`, not the `Hypothetical`
   one). Reworded.
8. Row 17's "yes" rests on what an ill-formed `let` would have
   computed. Hedged.
9. Note on 17: self/README.md already says the column may differ, and
   "every error test" refers to its test suite. Corrected.
10. §4 cited only §29 site 1; 06 and 15 rest on site 3. Added, along
    with the no-first-error reference runs that support the "computed
    value" judgements.

Confirmed and left as is: the four gates and their lines; `env-failed`
(`core.sl:2533`) ignores warnings; the writers of `env-set-said` seen
(`core.sl:2806`, `:2808`, `:4133`, `elab-main.sl:3285`) drop no
`SaidError`; exit 1 comes from `main.sl:143`; the self-expanding macro
after the error still reports "more than 10000 macro expansions";
`(let ((many t)) s)` with `s` a `Settled` string leaves `t`
`Hypothetical`; `compile-error s` on a pre-error `s` prints its text;
with `--first-error` exactly the 14 tests with a second message print
the trailer.

Unsure:

- Acceptance: monotonicity was checked only for the `env-set-said`
  writers above. An `Env` that is elaborated speculatively and then
  discarded was not looked for; it could not make a program accepted
  through this mechanism as far as the reviewer can see, but that was
  not proved.
- Whether every run-position form is gated: `coerce`, and special forms
  that the elaborator evaluates itself (`gensym`, `read-file`, and the
  `settled-*` family), were not checked after an error.
- Why a string literal and a `Settled` string variable leave the binder
  `Hypothetical` while a `Nat` variable gets the token remains
  untraced.

## Round 6 review notes

A sixth reviewer read the brief, CLAUDE.md, all of DESIGN.md, 01 §3.7
and its Coordinator note, BUGS.md 25, and self/README.md's "Errors are
values"; re-ran all 17 reproducers on the reference, `slc --interpret`,
and slc with no flag (the two slc modes byte-identical on all 17, exit 1
everywhere, every message in the table as quoted); re-ran `--first-error`
(the trailer on exactly the 14 tests with a second message), the
no-first-error reference runs of §4 (as stated, and 15 without `(m)`
prints `_`), `proto/review2/after_error_call.sl`,
`proto/review4/01_after_error_succ.sl`, review note 2's `MkPair`,
`Cons`, and `Some` cases, a forwarded `Settled` string, `compile-error`
on a pre-error string, and a self-expanding macro after the error (all
as stated); confirmed that `self/` is unchanged from `5fba336` to HEAD;
and opened every cited line.

1. §1 said DESIGN.md "says nothing" about more than one error and
   called everything a difference from the reference only. 01 §3.7
   says "nothing explicit" and notes that §4's warning sentence may be
   read as implying that an error stops elaboration, which would make
   slc's going on a difference from DESIGN.md too. Reworded to carry
   that reading.
2. §1 quoted 01 §3.7 as saying the `(Zero)` binder "is still
   `Settled`" by an untraced path, and follow-up 5 asked 01 to replace
   that sentence. 01 §3.7 now gives this file's account (its
   Coordinator note 1), so both were stale. The quote is dropped and
   follow-up 5 removed; §1 now points to BUGS.md 25, which records the
   defect.
3. `heap-set-closed` was cited as `core.sl:2430-2437`; it is
   `:2433-2437` (2430 ends the previous function). Fixed.
4. §2 said the binders "stay as `bind` made them"; the function is
   `bind-let` (`elab-main.sl:2206`). Fixed.
5. Unsure list: a three-item list lacked its conjunction. Fixed.

Unsure:
- The review notes' monotonicity check lists four writers of
  `env-set-said`; there are four more (`core.sl:3428`,
  `elab-main.sl:3356`, `:3358`, `elab.sl:935`). Each read here prepends
  to the existing list, but none was traced further, and an `Env`
  rebuilt from an older one was still not looked for.
