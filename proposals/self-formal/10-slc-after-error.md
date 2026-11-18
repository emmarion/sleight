# 10. What slc does with run-position forms after the first error

Written by an agent at the coordinator's request, as a follow-up to
01-spec-shape.md §3.7 and its review notes. Nothing in it is approved,
and nothing here is a design decision (CLAUDE.md rules 1, 11). Where
this file and DESIGN.md disagree, DESIGN.md is right. Code citations
are to the tree at commit `5fba336`; the readings of slc's source are
this agent's and may be wrong in detail. Every message quoted below as
printed was observed by running the tests; a behaviour marked as read
was not.

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
  DESIGN.md, except where a message slc prints, or an answer `resolve`
  gives a macro, is false.
- After an error, slc does not run run-position code through its
  evaluator for `let`s, calls (primitives such as `settled-value`
  included), constructor applications, run-position `match`es,
  `coerce`, or `let-match`, and does not compile or run a
  `native-compute` (`proto/review7/` tests `settled-value`, `coerce`,
  `let-match`, and `native-compute`; `proto/aftererr/` the rest). Macro
  expansion is not gated: a macro bound before the error still runs, at
  compile time, after it, and the macro-world primitives it calls answer
  as before (`gensym` and `read-file` were run), except that `resolve`
  answers `RHypothetical` for a binder that holds the token
  (`proto/review7/10_macro_prims.sl`), so the prelude's `unary` and
  `prove-literal-lt` refuse such a binder as not a constant
  (`10_literal_macros.sl`).
- A nullary `(Zero)` bound after the error is `Settled`, but it seems
  not to hold the value `(Zero)`. A run-position `let` whose right-hand
  side needed no hoisted temporaries gets its binders set to the erased
  token (`env-set-tokens`), and slc's discriminant read takes a token as
  the word 0 (`self/eval.sl:51`). So a `Nat` binder reads as 0, a
  `String` binder as `(SNil)`, and a binder of a tagged enum as the
  enum's first fieldless constructor, whatever the right-hand side was.
  `(Zero)` reads as `0` only by coincidence. Other kinds of type were
  not surveyed; one single-constructor case is in the review notes.
- That gives false messages: after an error, `(let ((many x)) (BFalse))`
  followed by `(comptime-match many x (BFalse))` reports "expected
  `BFalse`, got `(BTrue)`"; `x` bound to `3`, to `(Succ y)`, to a call,
  or to a variable holding `1` is reported as `0`. It also hides errors:
  `(comptime-match many x (BTrue))` on that `BFalse` binder, and
  `(comptime-match many x (Zero))` on `x` bound to `3`, pass silently,
  and some messages are dropped once an error is recorded, among them
  the error for a pre-error macro whose run crashes after the error
  (§2, "What is not reported"). Where the binder is left
  `Hypothetical` (a right-hand side that needed temporaries, or the
  fields of a `let-match`), slc reports that the scrutinee is not
  `Settled`, which DESIGN.md §27-§29 would, in this agent's reading,
  make it. The string binders tested, of a literal and of a `Settled`
  string variable, are not left `Hypothetical`: they hold the token
  too, which `comptime-match` reads as `(SNil)`, but the check on the
  message of `compile-warn` and `compile-error` words any stored value
  that is not a string as "is `Hypothetical`" (`elab.sl:2585-2587`;
  `14_string_msg.sl`, `proto/review7/10_string_token.sl`).
- No test changed acceptance: slc exits 1 once its message list holds
  an error (`self/main.sl:139-143`), and every test exits 1 on both
  implementations. The defects, if they are taken as such, seem to be
  in the second and later messages only; §4 says how far that was
  checked. BUGS.md 25 records the defect, with some of these cases, and
  points here for the rest.

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
failed. `settled-type`, `settled-erase`, `settled-mult`, and
`settled-value` are elaborated as primitive calls
(`elab-main.sl:1075-1081`, `elab-prim-call` at `:2482-2513`), so the
gate at `:739` keeps them from running in run position: in
`proto/review7/10_settled_value.sl`, whose handle is bound before the
error, the binder of a `settled-value` after it holds the token.

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
answers `RSettled`; `tests/macro_resolve_after_error_bad.sl`, run
after `std/macro.sl` as its header asks, reaches it too, and slc's
second message there, the macro's own "not settled", is false in the
same way. The prelude's `unary` and `prove-literal-lt` read a name
through `resolve` (`constant`, `lib/prelude.sl:2494-2499`), so after
the error they refuse a binder bound after it with their usage message
("takes two constants of type `Nat` or `Char`" and its `unary` form),
while a literal or a binder bound before the error still serves
(`proto/review7/10_literal_macros.sl`). `comptime-match` and
`show-typed` have no such test, and `message-of` (`elab.sl:2578-2587`)
words a token as `Hypothetical` without one. This suggests the token is
meant as a "not run" marker, but that was not confirmed. ASSUMPTIONS.md
32, a session's choice, has the token stand in only where elaboration
needs a `Settled` for an erased entry; its use for non-erased binders
after an error is outside that.

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
is `(BFalse)`, with `(BTrue)`, and once failed `elab.sl:4790-4791`
records nothing for the contradiction, where it would otherwise record
an error beginning "internal: the verified value contradicts the facts
in force", so 03 prints nothing. `proto/review7/10_contra_dropped.sl`
shows this path on `Maybe`: after the error, a `comptime-match` with
pattern `(None t1)` on an `x1` whose rule is `(Some (Nat) 4)` prints
nothing, and a later `dump-context` shows `t1` `Hypothetical` with no
rule, where the same match on an `x2` that is `(None (Nat))` leaves
`t2` `Settled` and `is (Nat)`. Its report also gives `x1` as
`is (Some (Nat) 4)` and `= (None _)`.

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
error). A macro bound after the error holds the token too and is
refused as not constant-known (`proto/review2/after_error_macro.sl`),
as `m2` is in 15: in `proto/review7/10_macro_after.sl` the refusal is
the plain one, so the entry is `Settled` (`elab.sl:2800-2806`), and
`resolve` answers `RHypothetical` for it, which for a `Settled` entry
only the token test gives. A direct read of an entry that was
`Settled` before the error is unaffected: `comptime-match` on it, and
on the fields it binds, reads the real value
(`16_pre_error_field.sl`), `(compile-error s)` with such an `s` prints
its text, and `resolve` answers `RSettled` for it
(`10_macro_prims.sl`). Code that would compute from such an entry is
not run: `x` bound to such a `y` holds the token (06).

**What is not reported.** Besides `elab.sl:4791`, some `env-failed`
tests drop a message once failed. `env-fail` (`core.sl:2802-2806`)
drops a new error whose text repeats one already recorded or contains
`<error: ` (read only). `env-with-heap` (`core.sl:2815-2819`), the
only place that builds a "compile-time evaluation failed" error,
records none. So in `proto/review7/10_macro_crash.sl`, under
`--eval-fuel 100`, a pre-error macro that runs out of fuel when
expanded after the error is reported by nothing; without the error,
that message is the only one slc gives for the crash. The "unnecessary
`(predates _)`" warning, and its `(subterm _)` form (`unneeded`,
`elab.sl:4344-4354`), and the "`;! suppress warn` ... silenced
nothing" warning (`end-file`, `elab-main.sl:3280-3285`) are skipped
(`proto/review7/10_unreported.sl` shows both kinds), and so, read only,
are the `--warn-unused` warnings (`report-unused`, `:3343-3349`) and
the closing of the goal (`main.sl:140`).

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
| 15_macro_alias | `m` bound before; `m2` = `m` after; `(m)`, `(m2)` | `Zero` is not a statement (from `(m)`); `m2` is a macro, expanded only where its head is constant-known | first no; second yes: `m2` is `Settled` in slc too but holds the token, while by §29 site 3 it would forward `m`'s value and §19 would dispatch it as a macro (§6, §62) |
| 16_pre_error_field | `y` = 2 before; `comptime-match y (Succ p)`, `p` `Zero` | expected `Zero`, got 1 | no |
| 17_type_error_first | first error is a refuted branch, not `compile-error` | expected `BFalse`, got `(BTrue)`; `end` | the first of these, probably: it asks what an ill-formed `let` would have computed (`BFalse`, as `y` is `(Succ (Zero))`) |

Notes on the table:

- 01 and 03 together show that what the binder reads as is not
  computed: 01 reads `(Zero)` where `(Zero)` was written, and 03 reads
  `(BTrue)` where `(BFalse)` was. In both, the token reads as the
  type's first fieldless constructor, whatever was written.
- In 13 there is no `let`: `comptime-scrutinee`
  (`elab-main.sl:1185-1195`) elaborates the form, `run-form` refuses,
  and `settled-from` (`elab.sl:2879-2884`) finds no variable code to
  copy, so the entry is `Hypothetical`.
- 17's first message differs from the reference's in wording ("write
  `absurd`" against "write `(absurd Zero)`") and column (44 against 45).
  That is outside this file's question. self/README.md says the first
  message is the reference's on every error test (of the test suite)
  and already allows the column to differ; the wording difference is
  not covered by that, so it may be worth a look. So may another one
  seen here: with its `compile-error "first"` removed, 10_macro_crash
  (below) gives "compile-time evaluation failed: out of fuel" on slc
  and "macro `m` failed: out of fuel" on the reference.
- With `--first-error`, slc prints only its first message (`first`, or
  17's refuted branch) and the trailer
  (`slc: stopped at the first error (--first-error)`) on every test in
  both tables that has a second message, so none of the false messages
  is shown.

Review tests under `proto/review7/`, each with a
`(compile-error "first")` before the forms shown, in the same columns
(10_macro_crash is run with `--eval-fuel 100` on both
implementations):

| Test | After the error | slc's later messages | False? |
|---|---|---|---|
| 10_letmatch | `y` = 1 before; `let-match many y (Succ p)`; `comptime-match` `p` `Zero` | needs a Settled scrutinee; expected `Zero`, got `?` | yes (both) |
| 10_coerce | `y` = 1 before; `x` = `(coerce y (coercible-refl (Shared) y))`; `Succ` | expected `Succ`, got 0 | yes |
| 10_settled_value | `y` = `(BFalse)` and `h` = `(settled-of many y)` before; `v` = `(settled-value _ _ h)`; `BFalse` | expected `BFalse`, got `(BTrue)` | yes |
| 10_native | `f` gives `(BFalse)`, bound before; `x` = `(native-compute f)`; `BFalse` | scrutinee is not a datatype value; expected `BFalse`, got `_` | yes (both) |
| 10_string_token | `s` = `"abc"`, `t` = a pre-error `"abc"`; `SCons` on each; `compile-warn t` | got `(SNil)` (twice); `t` is `Hypothetical` | yes (all three) |
| 10_macro_prims | a pre-error macro's `resolve` on a later `def-fns` name, a later `let` binder, and a pre-error binder; its `gensym` and `read-file` | `RSettled`, `RHypothetical`, `RSettled`; both primitives answered | the `RHypothetical` |
| 10_literal_macros | `b` = 7 before, `a` = 7 after; `prove-literal-lt` on `3 5`, `b 9`, and `a 9`; `unary a` | on `a` only: the usage message of each, and after `prove-literal-lt`'s, "the enclosing `let` expects 1 value, got 0"; then the `compile-warn` | yes (the usage messages, and the count that follows from the first) |
| 10_contra_dropped | `x1` = `(Some (Nat) 4)`, matched `(None t1)`; `x2` = `(None (Nat))`, matched `(None t2)`; `dump-context` | only the report: `t1` `Hypothetical`, `t2` `Settled`; `x1` `is (Some (Nat) 4)` and `= (None _)` | missing error; the report's `= (None _)` |
| 10_macro_crash | a pre-error macro whose run runs out of fuel; `compile-warn` | the `compile-warn` only | missing error |
| 10_unreported | an empty `;! suppress warn` region; an unneeded `(predates _)`; `compile-warn` | the `compile-warn` only | two missing warnings |
| 10_macro_after | a pre-error `resolve` probe on `m`, a macro bound after the error; `(m)` | `RHypothetical`; `m` is a macro, expanded only where its head is constant-known | yes (both) |

## 4. Are reported messages false?

[A] Yes, in this agent's reading, for every "yes" row above, and for
the false items two other rows name (10_macro_prims's `RHypothetical`
and 10_contra_dropped's `= (None _)`): each one states a fact about the
program (a value's constructor or number, that it is not `Settled` or
not a datatype value, that a head is not constant-known, that an
argument is not a constant, or what `resolve` finds) that DESIGN.md §27
("its results become `Settled` with the resulting values"), §28, and
§29 site 1 (site 3 for 06, 10_string_token's `t`, and 15's second)
contradict, with §64 for `settled-value`, §72 for `native-compute`, §65
for `resolve`, and §45 and §49 for what `prove-literal-lt` and `unary`
take. As a check on the "False?" column, each reproducer was also run on
the reference with the `compile-error "first"` line removed (15 also
without `(m)`): every `comptime-match` of a "yes" row passed (17 aside,
which has no such line and stops at its refuted branch), 03, 05,
10_contra_dropped, and 10_macro_crash failed with the error slc omits,
14 printed `abc` twice, 10_string_token printed it once, `(m2)`
expanded, `resolve` answered `RSettled` all three times in
10_macro_prims and once in 10_macro_after, whose `(m)` then expanded,
10_literal_macros printed only its `compile-warn`, and 10_unreported
gave both warnings.
slc, run on the same files, printed what the reference did on every
one but 17, 10_contra_dropped, and 10_macro_crash: in each, an error
still comes before later forms, so slc goes on, and in 10_macro_crash
it words the crash differently (§3's notes).
The first message seems never to be affected, since every message
before it is recorded with no gate shut, and acceptance seems never to
be affected: once an error is recorded, slc's exit code is 1 whatever
follows, when it runs to the end (below). DESIGN.md does not require a
second message at all, so the reading that these are defects rests on a
message being false, not on its being extra. Three further kinds of
difference were seen that are not counted as false messages here:
messages that do not appear (03, 05, 10_contra_dropped, 10_macro_crash,
and 10_unreported's two warnings), which DESIGN.md seems not to require
since it requires no second message; genuine later messages that the
reference would not reach (15's first, and each later `compile-warn` or
`compile-error`); and a message that follows from the first error at
the same form. In `proto/review2/03_untaken_ce.sl`, where a branch's
body is `(compile-error "untaken")`, slc adds "the enclosing `match`
expects 1 return value, got 0" and the reference prints `untaken`
alone; self/README.md allows such messages ("may report a few more that
follow from it"). It states no value, and whether it is false turns on
the size of a `compile-error` used as an expression, which DESIGN.md
does not state: §4 lets the form "stand anywhere a form may", §54 makes
it "also usable as an expression", and §27 lists it among the
statements, which produce no values.

[A] One case looked for and not found: a later error that slc would
have to report and does not, in a way that could make a program
accepted. No gate shuts until an error is recorded, and `env-failed`
decides the exit code (`main.sl:143`), so acceptance could change only
if a recorded `SaidError` were later dropped. None of the eight calls
of `env-set-said` drops one (`core.sl:2806`, `:2808`, `:3428`, `:4133`;
`elab-main.sl:3285`, `:3356`, `:3358`; `elab.sl:935`), nor does
`env-warn` (`core.sl:2549-2550`), which prepends a warning. Every other
`MkEnv` that `self/` builds, apart from the first, empty one, carries
the list of the `Env` it rebuilds, except `env-restore`, `env-hide`, and
`env-discard` (`core.sl:2844-2895`), which rebuild an `Env` from two
and keep the newer one's list. One elaboration whose `Env` is then
discarded was found: `apply-answer` (`elab-main.sl:467-507`) checks a
`settled-ty-apply` or `settled-val-apply` quietly on a copy of the
`Env` it is given and goes on from that `Env`, so it drops only the
messages of its own check. Other places that go back to an earlier
`Env` were not searched for. So this agent does not see how a dropped
error could arise, but did not prove that none does.

## 5. Suggested follow-ups

These are options for the owner, not recommendations to adopt.

1. Make the post-error state honest. Either leave a `let`'s non-erased
   binders `Hypothetical` when the environment is failed (the
   `ctx3`-non-empty branch already does), or give them a distinct "not
   run" state, and have `comptime-match`, head dispatch, `dump-context`,
   and the `compile-error` message check say nothing about such an
   entry. That would remove every "yes" row whose message comes from
   one of those checks, but not the items that rest on `resolve`'s
   answer (10_macro_prims, 10_literal_macros, and 10_macro_after's
   `RHypothetical`), and it would not bring
   back the messages that are dropped (§2, "What is not reported"). A
   `let` with no non-erased binder takes the same branch
   (`elab-main.sl:2216`), and its token is what §27 gives it, so the
   change would leave that case alone; what else the token assignment
   there (and at `:673-678`) is there to protect was not investigated.
   A "not run" test of the kind `resolve-answer` already makes
   (`eval.sl:1335`) may be a starting point.
2. Alternatively, keep running run-position code after an error, as
   the reference would if it continued. That would make most later
   messages true, though code whose own check failed, such as 17's
   `let`, would then run too, with results that DESIGN.md, in this
   agent's reading, does not define. slc would run all compile-time
   code after a known error, as it already runs macro expansions,
   including loops bounded only by fuel.
3. Stop at the first error by default and keep the current behaviour
   behind a flag; by default this matches the reference, and it
   reverses the default that self/README.md's "Errors are values"
   describes.
4. Separately from any of these, `word-of-block` reading a `BToken` as
   the word 0 (`eval.sl:51`) may deserve a look on its own: this file
   reached it only after an error, through `env-set-tokens`, and did
   not check whether other paths reach it.

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

## Round 7 review notes

Two passes of a seventh review. The first was interrupted after
editing the body and adding `proto/review7/10_coerce.sl`,
`10_letmatch.sl`, `10_macro_prims.sl`, `10_native.sl`,
`10_settled_value.sl`, and `10_string_token.sl`, before writing notes;
items 1 to 7 record its changes, and items marked "(interrupted pass)"
its errors. The second pass treated those changes as unreviewed. It
re-ran every `proto/aftererr/` test, the after-error tests of
`proto/review2/` and `proto/review4/`, and every `proto/review7/10_*`
test on the reference and on slc under `--interpret`, with no flag,
and with `--build` (the three slc modes byte-identical, exit 1
everywhere); the no-first-error variants of §4; `--first-error` on
each; `tests/dump_context.sl`; `tests/macro_resolve_after_error_bad.sl`;
and `proto/review2/03_untaken_ce.sl`. It confirmed that `self/` is
unchanged from `5fba336` to HEAD and to `origin/main`, and opened every
cited line. Every message in both tables reproduces. New tests:
`10_contra_dropped.sl`, `10_literal_macros.sl`, `10_macro_after.sl`,
`10_macro_crash.sl` (run with `--eval-fuel 100`), and
`10_unreported.sl`; `10_settled_value.sl` now binds its handle before
the error.

The interrupted pass's changes, checked and kept unless an error item
below says otherwise:

1. The header now separates observed messages from behaviours marked
   as read, and `--build` is a third slc mode. The three modes agree
   on every test cited.
2. §1 names §54's "stops elaboration with a report of the context" as
   a second text near the question. Re-run: on `tests/dump_context.sl`
   the reference prints the report alone and slc adds two errors (one
   with a note) and a warning.
3. `coerce`, `let-match`, and `native-compute` are not run after the
   error (`10_coerce`, `10_letmatch`, `10_native`;
   `elab-main.sl:869`), nor is a file's final expression (`:3393`;
   `env-run-final` runs code, `elab-main.sl:448-451`), and
   `settled-ty-apply` and `settled-val-apply` stop elaborating
   (`:2537`, `:2560`, `:2565`).
4. Of the macro-world primitives only `resolve` tests `env-failed`;
   `gensym` and `read-file` answer as before, `resolve` answers
   `RHypothetical` for a token-holding binder, and a `def-fns` after
   the error is `Settled` (`10_macro_prims`). The claim about
   `tests/macro_resolve_after_error_bad.sl` holds only with
   `std/macro.sl` first, as its header asks (alone it fails at
   `def-macro`); that is now said.
5. String binders hold the token: `10_string_token`'s
   `comptime-match` reads each as `(SNil)` with no "needs a Settled
   scrutinee", and "is `Hypothetical`" is `message-of`'s wording for a
   token (`elab.sl:2585-2587`). This supersedes the first review notes'
   item 3, their "Confirmed and left as is" entry on
   `(let ((many t)) s)`, and their unsure point on string binders, and
   the sixth review's re-run of "a forwarded `Settled` string" ("all as
   stated"); the interrupted pass had not marked them.
6. The `elab-let` token branch (`:2216`) also serves a `let` with no
   non-erased binder (`pos-mult`, `core.sl:207-210`), which §27 gives
   the token; `open-bind` serves `open-adt` and `open-absurd` (callers
   at `elab-main.sl:682` and `:2089`).
7. §4's basis for the "False?" column, its no-first-error runs, the
   "seems" on the first message and on acceptance, and the monotonicity
   paragraph.

Errors found, and changes:

8. (interrupted pass) "None of the eight writers of the list" missed
   `env-warn` (`core.sl:2549-2550`), which prepends a warning through
   `MkEnv` rather than `env-set-said`; a scan of every `MkEnv` built in
   `self/` found no other writer. Fixed.
9. (interrupted pass) Follow-up 1 claimed its change would remove
   every "yes" row, but 10_macro_prims's `RHypothetical` rests on
   `resolve`'s answer, which none of the named checks gives; and "when
   the gate refuses" took in the erased `let` of item 6. Narrowed to a
   failed environment, with both cases named.
10. (interrupted pass) The header said every quoted message was
    observed, beside a quoted "internal: ..." text that is never
    printed. Now "as printed", and §2 calls that text what the code
    would otherwise record.
11. (interrupted pass) §1's "except where a message slc prints is
    false" left out `resolve`'s answer, which §4 counts as false.
    Extended.
12. (earlier rounds) Row 17's "the second, probably" could be read as
    slc's second later message, `end`, a genuine error; the false one
    is the first. Fixed.
13. (earlier rounds) "Reading a value that was `Settled` before the
    error is unaffected" was too broad: 06, 07, 08, `10_coerce`, and
    `10_settled_value` read such values through code that is not run
    and get the token. Narrowed to direct reads.
14. (earlier rounds) Follow-up 2 set running code "at compile time
    after a known error" against the present behaviour, though macro
    expansions already run then, and its "would make the later messages
    true" overlooked code whose own check failed (17's `let`). Follow-up
    3's "discards" is "reverses the default", since the option keeps the
    behaviour behind a flag. Follow-up 4 claimed a search ("found it
    reachable only after an error") that was not made. Reworded.
15. (earlier rounds) The note on 01 and 03 said the token reads as the
    first fieldless constructor "whatever was written", for any type;
    the first review notes' `MkPair` case differs. Scoped to those
    types. Row 15 cited §6 for macro expansion, which is §19's (with
    §6 and §62). "BUGS.md 25 records them": it records some cases and
    points here. Also a code span split across lines, and "the fields
    that binds". Fixed.
16. (earlier rounds, gap) After the first error slc also drops
    messages. A crash in a later expansion is reported by nothing,
    since `core.sl:2819`, the only builder of "compile-time evaluation
    failed", records nothing once failed (`10_macro_crash`); the
    "unnecessary `(predates _)`" and "silenced nothing" warnings are
    skipped (`10_unreported`); and, read only, `env-fail` drops repeated
    texts and those containing `<error: `, and `--warn-unused` and the
    goal's closing are skipped. Added as "What is not reported", rows,
    and §4. Without the error the two implementations word that crash
    differently; §3's notes record it beside 17's wording.
17. (earlier rounds, gap) The prelude's `unary` and `prove-literal-lt`
    read names through `resolve` (`lib/prelude.sl:2494-2499`), so after
    the error they refuse a binder bound after it with a false usage
    message (`10_literal_macros`; without the error both pass on both
    implementations). Added, with §45 and §49.
18. (earlier rounds, gap) `proto/review2/after_error_macro.sl`, which
    01 §3.7 cites, was not used here. A macro bound after the error is
    `Settled` and holds the token (`10_macro_after`: the plain refusal,
    and `RHypothetical` from `resolve`). Added.
19. Strengthened: §4's "not looked for" speculative `Env` now names
    `apply-answer` (`elab-main.sl:467-507`), which checks quietly on a
    copy and goes on from the `Env` it was given; `10_settled_value`
    now isolates `settled-value`, which the gate at `:739` covers as a
    primitive call (`elab-main.sl:1075-1081`, `:2482-2513`); and the
    "read, not tested" contradiction path is tested by
    `10_contra_dropped`, whose report also shows `dump-context` reading
    the token (`= (None _)`), so follow-up 1 lists `dump-context`.
    ASSUMPTIONS.md 32, a session's choice, is cited beside the "not run"
    marker reading.
20. From a coordinator's note relaying another reviewer:
    `proto/review2/03_untaken_ce.sl` reproduces (slc adds "the
    enclosing `match` expects 1 return value, got 0"; the reference
    prints `untaken` alone; `--first-error` hides it). Added to §4 as a
    third kind of difference, with whether it is false left open:
    DESIGN.md mentions `compile-error` only in §4, §27, and §54, and
    none gives its size as an expression.

Elsewhere, not edited, as read during this review: 01 §3.7 says a
string literal or a `Settled` string variable leaves the binder
`Hypothetical`; 00-summary.md item 22 ("string binders aside,
untraced"), item 20 (§4 only), and its unverified entry on string
binders and on `coerce`, `gensym`, `read-file`, and the `settled-*`
forms are stale against this file; and BUGS.md 25 reads the token as
"its type's first fieldless constructor" for every type, calls 17's
message "the same false message" without this file's "probably", and
does not mention §54.

Unsure:
- 03 itself was not seen taking the contradiction path;
  `10_contra_dropped` shows it on `Maybe`, and 03 prints nothing either
  way.
- Places other than `apply-answer` that go back to an earlier `Env`
  were not searched for, so the monotonicity argument is still not a
  proof.
- Whether `dump-context`'s `= (None _)` in `10_contra_dropped` is false
  by the column's standard: without the first error the report is
  never reached, since the `(None t1)` match fails first.
- `open-bind`'s token for a non-empty context, failed or not (`:675`),
  is still read only.
- No timing claim is made here, and none was re-run.
