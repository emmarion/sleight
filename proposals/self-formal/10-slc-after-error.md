# 10. What slc does with run-position forms after the first error

Written by an agent at the coordinator's request, as a follow-up to
01-spec-shape.md §3.7 and its review notes. Nothing in it is approved,
and nothing here is a design decision (CLAUDE.md rules 1, 11). Where
this file and DESIGN.md disagree, DESIGN.md is right. Code citations
are to the tree at commit `5fba336`; the readings of slc's source are
this agent's and may be wrong in detail, though every behaviour quoted
below was observed by running the tests.

Implementations: the reference is `_build/default/bin/main.exe`; slc is
`_build/release/slc` (built after the last change to `self/`), run both
as `slc --interpret` and compiled (`slc` with no flag). On every test
below the two slc modes printed byte-identical output and the same exit
code, so they are not distinguished further.

## 1. Summary

- DESIGN.md says nothing about reporting more than one error (01 §3.7;
  §4's "Warnings go to standard error and do not stop elaboration" is
  the nearest text). The reference stops at the first error. slc
  records errors and goes on (self/README.md, "Errors are values"),
  and `--first-error` only cuts the report short (self/main.sl:45).
  Everything below is therefore a difference from the reference, not
  from DESIGN.md, except where a message slc prints is false.
- After an error, slc does not run run-position code through its
  evaluator for `let`s, calls, constructor applications, run-position
  `match`es, or `let-match`. Macro expansion is not gated: a macro bound
  before the error still runs, at compile time, after it.
- The nullary `(Zero)` that 01 says "still gets a `Settled` value" does
  not, it seems. A run-position `let` whose right-hand side needed no
  hoisted temporaries gets its binders set to the erased token
  (`env-set-tokens`), and slc's discriminant read takes a token as the
  word 0 (`self/eval.sl:51`). So the binder reads as the first fieldless
  constructor of its type, or as the `Nat` 0, whatever the right-hand
  side was. `(Zero)` reads as `0` only by coincidence.
- That gives false messages: after an error, `(let ((many x)) (BFalse))`
  followed by `(comptime-match many x (BFalse))` reports "expected
  `BFalse`, got `(BTrue)`"; `x` bound to `3`, to `(Succ y)`, to a call,
  or to a variable holding `1` is reported as `0`. It also hides errors:
  `(comptime-match many x (BTrue))` on that `BFalse` binder, and
  `(comptime-match many x (Zero))` on `x` bound to `3`, pass silently.
  Where the right-hand side did need temporaries, the binder is
  `Hypothetical`, and slc reports that the scrutinee or message is not
  `Settled`, which DESIGN.md §27-§29 would make it.
- No test changed acceptance: the first error already makes slc exit 1
  (`self/main.sl:139-143`), and every test exits 1 on both
  implementations. The defects, if they are taken as such, are in the
  second and later messages only.

## 2. The traced code path

All under `self/`. "Failed" means `env-failed` (`core.sl:2533`), which
is true once any `SaidError` is in the environment's message list; the
list only grows, so once failed, always failed.

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
- `elab-main.sl:739`, in `call-returns`: a call, primitive or `world-do`
  in run position is run and its results set `Settled`. When failed,
  the call code is returned unrun.
- `elab-main.sl:2152`, `let-match`: the `run` flag; when false the
  statement takes the hypothetical path (`:2168` on), so its fields are
  `Hypothetical`.

Two more places, not listed in 01, decide what a binder holds when the
gates have refused to run:

- `elab-main.sl:2209-2216`, `elab-let`. If the right-hand side's
  context `ctx3` is non-empty (some temporary was left unrun by
  `:539`), `env3` is `env2` and the binders stay as `bind` made them,
  `Hypothetical`. If `ctx3` is empty, `run` is true, and the inner
  environment is failed, the binders are set by `env-set-tokens`
  (`eval.sl:1640-1643`), which gives each a `Settled` state holding a
  fresh `BToken` block (`set-state-closed`, `core.sl:2439`;
  `heap-set-closed`, `core.sl:2430-2437`).
- `elab-main.sl:672-678`, `open-bind`, does the same for the anonymous
  entry of an `open`.

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
`extern`-backed type such as `Nat` the word 0 is decoded by
`ext-destruct` as `Zero`; for a fieldless-tagged enum, `fieldless-index`
maps it to the first fieldless constructor (`BTrue` in `Bool`, `None`
in `Maybe`). `headed-by` (`eval.sl:441-442`) then compares indices, and
the mismatch message (`elab.sl:4784`) prints the value with
`show-typed` (`elab.sl:4727-4731`), which renders the token through the
same reading: `0` for `Nat`, `(BTrue)` for `Bool`, `(None _)` for
`Maybe`. For a `Hypothetical` entry `settled-ref` is `None` and
`show-typed` prints `` `?` ``, after the separate "needs a Settled
scrutinee" error at `:4758`, so such a `comptime-match` prints two
errors.

**Why `(Zero)` and not `(Succ (Zero))`.** `(Zero)` has no arguments, so
the constructor application (`elab-main.sl:1141-1158`) hoists nothing,
`run-form` refuses at `:545`, `ctx3` is empty, and the binder gets the
token. In `(Succ (Zero))` the argument `(Zero)` is hoisted through
`hoist-argument` (`:690-698`) and `hoist-temp`, which refuses at `:539`
and leaves a frame, so `ctx3` is non-empty and the binder is
`Hypothetical` (`proto/review4/01_after_error_succ.sl`). `(Succ y)`,
with `y` already a variable, hoists nothing and gets the token
(`07_succ_var.sl`), as does a call `(f y)` (`08_call_var.sl`). A
literal `3` also gets the token (`04_lit.sl`); a string literal `"abc"`
leaves the binder `Hypothetical` (`14_string_msg.sl`), presumably
because the literal is bound through a temporary, and `(let ((many t))
s)` with `s` a `Settled` string also left `t` `Hypothetical` in an
ad-hoc run. Neither of those two was traced.

**What still runs.** `expand` (`elab-main.sl:555`) and the macro call
it makes have no `env-failed` test, so a macro bound before the error
is still expanded after it (`11_macro_rhs.sl`, `15_macro_alias.sl`; a
self-expanding macro bound before the error still hits "more than 10000
macro expansions"). A `def-fns` after the error still closes its group
(`elab-main.sl:2267-2272`, `env-close-group`), so its functions are
`Settled`; only calls of them do not run (`proto/review2/
after_error_call.sl`). Reading a value that was `Settled` before the
error is unaffected: `comptime-match` on it, and on the fields that
binds, reads the real value (`16_pre_error_field.sl`), and `compile-error
s` with such an `s` prints its text.

## 3. Test matrix

Sources are under `proto/aftererr/`. "ref" is the reference's full
output; every one exits 1 on every implementation. The slc column is
what slc prints after the first message, which is `first` and agrees
with the reference except in test 17. "False?" judges the message
against what DESIGN.md §27-§29 would make the value had the
run-position form run.

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
| 14_string_msg | `s` = `"abc"`; `compile-warn s`, `compile-error s` | `s` is `Hypothetical` (twice) | yes (both): by §27-§29 `s` would be `Settled` |
| 15_macro_alias | `m` bound before; `m2` = `m` after; `(m)`, `(m2)` | `Zero` is not a statement (from `(m)`); `m2` is a macro, expanded only where its head is constant-known | first no; second yes, by §29 site 3 `m2` would be `Settled` |
| 16_pre_error_field | `y` = 2 before; `comptime-match y (Succ p)`, `p` `Zero` | expected `Zero`, got 1 | no |
| 17_type_error_first | first error is a refuted branch, not `compile-error` | expected `BFalse`, got `(BTrue)`; `end` | yes (the second) |

Notes on the table:

- 01 and 03 together show that `(Zero)` and `(BTrue)` are not computed:
  the token reads as constructor 0 whatever was written.
- In 13 there is no `let`: `comptime-scrutinee` (`elab-main.sl:1185-
  1195`) elaborates the form, `run-form` refuses, and `settled-from`
  (`elab.sl:2879-2884`) finds no variable code to copy, so the entry is
  `Hypothetical`.
- 17's first message differs from the reference's in wording ("write
  `absurd`" against "write `(absurd Zero)`") and column (44 against 45).
  That is outside this file's question; self/README.md says the first
  message is the reference's "on every error test", so it may be worth
  a look.
- With `--first-error`, slc prints only `first` and its trailer
  (`slc: stopped at the first error (--first-error)`) on every test that
  has a second message, so none of the false messages is shown.

## 4. Are reported messages false?

[A] Yes, in this agent's reading, for every "yes" row above: each one
states a fact about the program (a value's constructor, its number, or
that it is `Hypothetical`) that DESIGN.md §27 ("its results become
`Settled` with the resulting values"), §28, and §29 site 1 contradict.
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
   investigated.
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
5. For 01: replace "A nullary `(Zero)` bound after an error is still
   `Settled` … by a path in slc's source that was not traced" with this
   file's account (the binder holds the token, read as 0).
