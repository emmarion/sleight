# 01. The shape of the formal spec: the static side, and where it starts

Written by an agent overnight at the owner's request. It is a proposal
and an agent's reading of DESIGN.md and the code; nothing in it is
approved, and nothing here is a design decision (CLAUDE.md rules 1, 11).
Where this file and DESIGN.md disagree, DESIGN.md is right.

Tags used below: **[D]** DESIGN.md says it (quoted); **[C]** the code
does it (file:line, or a test under `proto/spec-shape/` or a
`proto/review*/` directory, run with
`_build/default/bin/main.exe`, the reference, and with an slc built by
`self/release.sh` and run as `slc --interpret`); **[O]** an owner
statement from the brief; **[A]** this agent's reading or proposal.

## 1. Summary

- [A] DESIGN.md's elaboration cannot, as far as this reading goes, be
  stated as a typing relation separate from evaluation. Head dispatch,
  `comptime-match`, macros, the literal lemmas, and `native-compute` all
  read run results. The fact engine of §7 is free of evaluation ("The
  engine of §7 reads no stored value", §29). The proposal is three layers: a pure fact engine, then a
  run relation that reads the fact engine and the scope, then an
  elaboration relation that has run premises. A store Σ is threaded
  through all of elaboration, and the scope Γ is restored when a scope
  ends.
- [A] Recommended start is source bytes: a small reader *function* in
  front of a relation over DESIGN.md §63's `Raw`. The spec's parameters
  are the file names and bytes, a few flags, a file-system oracle for
  `read-file`, the FFI table's names and arities, the prelude text, and,
  under decision 6's recommendation, a `slot-eq` oracle.
- [A] Owner statement 3, that every program's source code is either
  accepted or rejected as an error, looks
  provable only relative to a termination hypothesis H (statement 4),
  or with fuel, an exhausted fuel being either a third outcome or a
  rejection (02's C4 takes the latter). Even under H, the 10000-expansion
  limit of §62 is needed, because each macro run halts but nothing else
  bounds how many expansions happen.
- [C/A] Three things DESIGN.md leaves free or unstated look able to
  affect acceptance: a program's acceptance depends on what `slot-eq`
  answers at compile time (tested: one program is accepted by both
  implementations and refused by both under `--no-native`, §3.8), the
  order of elaboration is visible through gensym numbers (tested; that
  it can decide acceptance is inferred from a program that both accept
  because a macro call gets number 1, §3.6), and a crash at compile time
  (out of fuel) rejects in both implementations (tested). The first two
  need an owner decision before the spec can be functional
  (deterministic); the third concerns the agreement theorem rather than
  the spec, whose machine does not crash (§31). A fourth, when the
  driver runs a file's `Program` final relative to the files after it,
  makes the two implementations disagree on acceptance (tested; section
  5 item 14).
- [A] Rejection: a positive `Fails` as the `Err` outcome of one total
  relation (mini/'s shape). Malformed syntax becomes a positive error,
  not "no derivation" as in mini/. Exclusivity of accept and reject then
  follows from the relation being functional.
- [A] Staging: fix the judgment's *shape* first (Σ, positions, errors,
  run mode), then add rules. The order is reader, then mini/ recast in
  that shape, then `Settled` and the round trip, then erasure, then
  macros with extern models and the prelude, then slots and cells, then
  sugar.

## 2. Decisions for the owner

Each one says what it needs, the agent's recommendation if any, and what
depends on it.

1. **Where does the spec start?** Bytes, `Raw`, or a core language.
   *Recommended:* bytes. Reading is a small structurally recursive
   function (`read : files → Items | ReadErr`) that serves as the spec of
   reading. Everything after it is a relation over `Raw` with `Pos`.
   *Why:* statement 3 is about "source code". Positions can be observed
   by a program (§3.9 below). A core-level start would leave out head
   dispatch and macros, which the paragraph of DESIGN.md on the
   language's aims makes central ("the constant-knownness of a head (§6) is what reconciles
   the two"). *Depends on it:* the statement of theorem 3, and whether
   `Pos` is in the judgment.
2. **What form does theorem 3 take?** [A] A Sleight proof with no fuel
   and no hypothesis seems to need compile-time evaluation proved
   terminating inside Sleight. That looks like the diagonal obstacle
   the owner does not expect to overcome for `no_false` (statement 1);
   this is unverified here. 03 F6 argues a version of it, not checked:
   if Sleight's functions terminate, and under F6's further premises,
   no non-erased `compile` function taking no further evidence agrees
   with the spec on every source. *Options:* (a) relative to H.
   Statement 4 words H as "every accepted compile-time form's spec run
   halts"; this file uses the broader "every compile-time run in the
   spec halts", and
   which one is meant is for the owner. (b) A fuel parameter, with a
   third outcome `OutOfFuel`, or with exhausted fuel a rejection, as
   02's C4 proposes for a depth bound. (c) A coinductive "diverges" outcome.
   *Recommended:* (a), obtained from (b): a fuelled deriving function
   is total with no hypothesis, and (a) would follow from it under H
   together with two lemmas: that more fuel never changes an answer
   other than `OutOfFuel`, and that a spec run which halts is reached
   by the fuelled function at some finite fuel, so that H, applied to
   the finitely many runs one program makes (finitely many given the
   expansion limit), yields one fuel that suffices (reading; not
   checked). *Not analysed
   here:* whether statement 2's idea, a fuel-free self-interpreter run
   as steps of the driver's `Program` loop (§27, §42), would carry over
   to the deriving function for elaboration (this file's extension of
   it) and change this;
   such a loop computes without fuel but by itself proves no
   termination. *Depends on it:* whether the deriving function for
   elaboration takes fuel, and where.
3. **Is the expansion limit a parameter?** DESIGN.md already fixes it:
   "At most 10000 expansions run in one run" (§62), so the spec keeps
   it as written. One question is whether the spec generalizes it
   to a parameter `N`, which would be a change to DESIGN.md's wording.
   *Recommended:* keep §62's 10000 as written; `N` is an option if the
   owner wants it. Without some
   limit, theorem 3 fails even under H (§3.5). Also open: §62 does not
   say what a call past the limit does. Both implementations refuse it
   ("more than 10000 macro expansions", §3.5), and theorem 3 needs the
   spec to give it an outcome, which needs wording (03 decision 5).
   *Depends on it:* theorem 3, and determinism, because the count is
   global.
4. **What does a rejection carry?** *Options:* (a) only "rejected";
   (b) the first error's position and macro-call trace; (c) also a
   structured reason, including the text DESIGN.md requires (the string
   of `compile-error`, and the expected constructor and actual value of
   a failed `comptime-match`); (d) the full message text. *Recommended:* (b) in
   the main agreement theorem, with (c) available in the relation, and
   never (d). *Why:* DESIGN.md speaks of "whichever one the elaborator
   meets first" (§15), though only for which of two conflicting uses of
   a unique binder is reported, not for errors in general. In the two
   programs tested, the reference and slc agree on the first message
   but not on later ones (§3.7). On a compile-time crash they differ
   even in the first message's position: for `fuel.sl` under
   `--eval-fuel 5` the reference names the file alone and slc names
   `lib/prelude.sl:354:75` (§3.4). *Depends on it:* how
   much of the elaboration order the spec must pin down (decision 5).
5. **Is the order of elaboration part of the language?** It is visible
   through gensym numbers, the expansion count, and which error comes
   first (§3.6). DESIGN.md fixes only part of it. *Recommended:* yes.
   The order would be the one both implementations follow, as tested
   (§3.6): in an application, a head that is a form first; then every
   macro call among the arguments, left to right, each call's output
   expanded before the arguments after it; then a head that is a name,
   whose errors therefore come after the arguments' expansions; then
   the arguments left to right, each nested application in the same
   way; and each statement before the code after it. It needs DESIGN.md wording, which is the
   owner's to give.
6. **How is `slot-eq` handled at compile time?** Under DESIGN.md, one
   program can be accepted by one conforming implementation and
   rejected by another, or by the same one on another run (§3.8). *Options:*
   (a) `Run` is nondeterministic, and the theorem says the compiler's
   outcome is one of the spec's outcomes; theorem 3 then gives
   existence only, with no exclusivity. (b) An oracle parameter (a
   stream of answers), so the spec is functional for each oracle.
   (c) Fix the compile-time answer to word equality, which is a change
   to the language, and would have to say whose words: the evaluator
   and `native-compute`'s compiled run answer differently (§3.8).
   (d) Forbid `slot-eq` from reaching run position or a macro, also a
   change to the language. *Recommended:* (b). It
   changes nothing in DESIGN.md and uses the same mechanism as the
   `read-file` oracle.
7. **Is a crash at compile time a rejection, a third outcome, or
   outside the spec?** This covers §31 crashes, `--eval-fuel`, and a
   `native-compute` compile or crash. *Recommended:* the spec's machine
   never crashes (§31's "unlimited stack and heap"). The agreement
   theorem allows a third compiler outcome, `Crashed`, which proves
   nothing about the spec. DESIGN.md says a crash is an error only for
   `native-compute` (§72); see section 5 below, item 3. Two tensions for the owner: both
   implementations refuse a run-position form whose run fails with a
   runtime error (MANUAL.md, `--eval-fuel`), and on a host stack
   overflow both die, naming no form (BUGS.md 27), so `Crashed` would
   be a rejection, or a death, the theorem says nothing about; and for `native-compute`, §72 makes a
   crash "an error at its argument", so treating it as `Crashed` departs
   from DESIGN.md unless the spec takes the compiled run's outcome as an
   oracle input. A third: 02 (C4) recommends the opposite for compile
   time, a spec run with an explicit depth bound whose exhaustion
   rejects, which departs from §31's "unlimited stack and heap". The two
   files' recommendations are alternatives, not one plan.
8. **Which flags are spec parameters?** *Recommended:* in the spec are
   prelude on or off (§42), extern on or off (§33 item 9 and §35 depend
   on it), `--fn-same` (§70), the `--goal` mode (§71), the
   `--comptime-unconfine` names (§65), the FFI table's names and
   arities (§42, §43), and the expansion limit if decision 3 makes it a
   parameter. Not in the spec are
   `--eval-fuel`, `--no-native`, `--hints`, and `--warn-unused`.
   `--no-native` changes acceptance without a crash, through `slot-eq`
   (§3.8); [A] under decision 6 (b) that is another oracle, so it can
   stay out.
   *Open:* `--warnings-as-errors`. DESIGN.md mentions it (§4), but its
   effect depends also on warnings that WARNINGS.md defines, beyond the
   few DESIGN.md defines (§4's, and the prelude's warnings in §69). In
   the reference it also changes when a `Program` final runs, and so
   acceptance of a unit with no warning at all (§3.7, section 5 item 14).
   *Recommended:* acceptance ignores warnings, and the flag is a policy
   of the driver that the theorem does not cover.
9. **What is the prelude to the spec?** *Options:* (a) a fixed elaborated
   snapshot Σ0; (b) the shipped text, as an input; (c) any prelude text,
   with the spec finding the names it needs (`Nat`, `String`, `Macro`,
   `Raw`, and so on) in the prelude (where exactly is open, §4.5).
   *Recommended:* (c),
   with the shipped prelude as one instance. The compiler theorem would
   quantify over it, and `--no-prelude` would be the empty prelude,
   except that §42 then allows `extern` anywhere ("only in the source
   prelude, or anywhere in a program run with `--no-prelude`"), so an
   empty prelude text and `--no-prelude` are not the same input. *Why:*
   [A] (a) needs a concrete elaboration of the prelude (2881 lines)
   proved inside Sleight. The only practical route this agent sees is
   reflection, which relies on the evaluator (§29), so the result would
   rest on the evaluator that the compiler proof is meant to cover.
10. **Judgment shape.** *Recommended:* the layers and the Σ/Γ split of
    §4.2. Where possible, the run relation is a *parameter* of
    elaboration, so that the metatheory of elaboration (determinism, and
    the theorem-3 skeleton) is proved once for every lawful run
    relation. 05 F7 compiles the mechanism: an ADT indexed by a
    relation-valued `TyCtor`, with a field whose type applies it, and a
    function generic over it, are accepted by both implementations
    (`proto/theorems/model.sl` after `bove.sl`). That the metatheory can
    be proved once this way is unverified.
11. **Staging order.** *Recommended:* §4.6. This affects how much of
    mini/ is rewritten.

## 3. Findings

### 3.1 Elaboration reads run results [D]

- Dispatch: "If its result is a `Settled`, non-erased entry whose minted
  type canonicalizes to `(Special)` … the list is the special form named
  by that entry's stored value" (§6 item 1). Macros work the same way
  (§19). `Settled` arises "once the form has run" (§29 site 1).
- "`(comptime-match m x (C f1 ... fn))` asserts … that `x` is a
  `Settled`, non-erased value headed by `C`" (§28). §7 adds that a
  verified fact "holds afterwards".
- In run position, a form "is elaborated, its erased positions are
  stripped, the evaluator runs the code, and its results become
  `Settled`", and this happens "before the code after it is checked"
  (§27). Round trips nest (§29).
- `prove-literal-lt` "relies on the evaluator" (§45). `unary` "mints the
  `Eq` … after checking it with `nat-cmp`" (§49). In the prelude, both
  are macros [C] `lib/prelude.sl:2480`, `:2571`.
- `native-compute` (§72). And: "Code runs at compile time only where a
  run-position form runs … and where a call of a macro is expanded"
  (§7).

### 3.2 The fact engine does not, and the run reads the elaborator [D]

- "Canonicalization never reads a `Settled` entry's stored value" (§7).
  "The engine of §7 reads no stored value" (§29). "The checker never
  evaluates" (§29). So canonicalization and unification can be a layer
  free of evaluation, as in mini/ (`canon.sl`, `unify.sl`).
- Some macro primitives read elaboration state while they run.
  `resolve` "looks a name up in the scope at the macro call". `settled-eq`
  canonicalizes "against the facts of the innermost run position
  enclosing the call". `settled-ty-apply` and `settled-val-apply` are
  "checked again" where they run. `intern-*` and `mint-settled` add
  entries (§65). [A] Each of these seems to need only the fact engine, a
  scope lookup, or Σ, never the full elaborator. If so, the layers do
  not form a cycle: fact engine, then Run, then Elab. Two points to
  check: where `settled-ty-apply` runs, "the application is checked
  again, against the facts `settled-eq` reads" (§65; where it is
  written, "`(t t1 ... tn)` must check as a term (§9)"), which is term
  checking, assumed here to be fact-engine work; and §45 leaves to the implementation "whether a literal's
  entries are produced by elaborating statements or created directly to
  the same effect", so, for the layers to stay acyclic, the spec of
  `intern-*` would take the second.

### 3.3 The macro world is the threaded store [D]

"The macro world is the elaborator's program store: the run-position
entries with their values and facts, the literal table, the gensym
counter and the expansion count. It is threaded sequentially through
all of elaboration, carried out of every scope where uses are carried,
and passed along rather than joined" (§65). [A] This is Σ. The owner
suspects the spec's run should be a mutating heap machine (statement
6). A top-level binder "may be `unique`" (§32), an extern may mutate a
unique value in place (§43), and a `cell-write` at `unique` is "a
physical store into memory" (§37). [A] This suggests a heap whose
blocks change, rather than a map from entries to trees. Whether a
value semantics would differ observably, given that a `unique` binder
is the only reference to a mutable value (§13), has not been checked;
`slot-eq`, `cell-same`, and `fn-same` are where this agent would look.

### 3.4 Parameters DESIGN.md makes acceptance depend on

- [D] `read-file` reads the file system, relative to "a source file or
  to a name `--comptime-unconfine` adds". `here` must be "spelled as the
  command line names it", and the path must stay inside that directory
  "through any symlinks" (§65). [A] So the spec needs an oracle
  `(name, path) → Result String`, and the file names as given.
- [D] `extern` on a name "the table lacks, or … already claimed, is an
  error" (§42). There is also a shape check against the
  implementation's arities (§43). `coercible-tag` "is refused … under
  `--no-extern`, and without the prelude" (§33 item 9). [A] So the FFI
  table's keys and arities, and the extern flag, are parameters.
- [D] `--no-prelude` (§42), `--fn-same` (§70), `--goal` (§71), and
  `--warnings-as-errors` (§4) are flags DESIGN.md names. [C]
  `--eval-fuel 5` rejects every program that loads the prelude, failing
  inside the prelude (`proto/spec-shape/fuel.sl`: the reference prints
  "lib/prelude.sl: runtime error: out of fuel", slc "lib/prelude.sl:354:75:
  error: compile-time evaluation failed: out of fuel"); a one-constructor
  program under `--no-prelude --eval-fuel 5` is accepted by both. The
  reference has no fuel bound by default, and slc's is 1000000000
  (MANUAL.md, `--eval-fuel`).

### 3.5 Termination [D/A]

- [D] "At most 10000 expansions run in one run, every file on the
  command line included" (§62). SOUNDNESS.md part 6 argues that checking
  terminates, using (T) for the run-position runs only, and the end of
  its part 5 adds "Macro expansion
  is bounded (§62)". [A] The
  bound carries real weight. Each macro function is total by levels,
  but a macro whose output calls itself expands without end
  (`proto/spec-shape/expansion_limit.sl` [C], refused with "more than
  10000 macro expansions").
- [C] The reference never resets its counter (`lib/elab.ml:553`,
  `:683-684`), so in principle prelude expansions count. The prelude
  defines two macros, `unary` and `prove-literal-lt`, bound at
  `lib/prelude.sl:2480` by the only `MkMacro` applications in it, at
  `:2571`, and calls neither after `:2571` (grep), so it seems to expand
  none. `proto/review6/01_count_10000.sl` agrees: a macro that recurses
  until its gensym number reaches 10000, so that the program expands
  exactly 10000 times, is accepted by both implementations, and the same
  with 10001 (`01_count_10001.sl`) is refused with "more than 10000
  macro expansions". `gensym_order.sl` [C] starts its gensym numbering
  at 1, which shows only that the prelude calls no `gensym`.
- [O] The owner was in general agreement, not agreement to exact
  statements, with framing compile-time termination as a hypothesis H
  (statement 4). [A] Theorem 3 without H needs (T), "every function activation
  returns" (SOUNDNESS.md part 1), proved inside Sleight about Sleight.

### 3.6 Elaboration order is visible [C]

`proto/spec-shape/gensym_order.sl` prints `(MkPair _ _ 1 $ MkPair _ _ 2
3)` on both implementations. That test cannot tell a depth-first order
from the one actually used. `proto/review3/gensym_depth.sl`, with the
nested pair first, prints `(MkPair _ _ (MkPair _ _ 2 3) 1)`, and
`review3/gensym_splice.sl` confirms the pattern one level deeper, on
both implementations: every macro call among an application's
arguments is expanded, left to right, before any argument is
elaborated, and only then are the arguments elaborated left to right,
each nested application in the same way. A macro call's output is
expanded before the arguments after it: in
`proto/review6/01_splice_output.sl`, `(MkPair _ _ (two) (gs))`, where
`two` expands to `(gs)`, prints `(MkPair _ _ 1 2)` on both. In the reference this is
`splicing` (`lib/elab.ml:710-722`), called on a call's arguments before
its head is checked (`:1380-1383`); a sequence of statements is
expanded one item at a time instead (`expand_seq`, `:723`). A head
that is a form is elaborated before the arguments are spliced
(`settle_head`, `:1368`, and `computed_head`): `review3/gensym_head.sl`,
whose head is a macro call that takes a number, gives the head 1 and
the arguments 2 and 3 (inferred: the head's number is not printed, and
`b` gets 4). A head that is a name is only looked up for dispatch
first (`:1376`); its elaboration, with its errors, comes after the
splicing (`:1383`): in `proto/review4/01_head_name_err.sl`,
`(nosuch (loop))` with `nosuch` unbound and `loop` a macro that
expands to itself is refused, on both implementations, with "more
than 10000 macro expansions", not with the unbound name. A macro can
branch on its number, so the order can decide acceptance: in
`proto/review7/01_order_accept.sl`, `(MkPair _ _ (MkPair _ _ (gs) (gs))
(first-only))`, `first-only` expands to `(Zero)` when its number is 1
and to an unbound name otherwise. Both implementations give it 1 and
accept; a depth-first order would give it 3, and placed where it gets
3 (`01_order_refuse.sl`) it is refused by both. [D] DESIGN.md fixes "The head is elaborated
first" (§6), that statements come before the code after them (§27), that
"the forms inside a form run before it does" (§27), and hoisting (§15),
which places hoisted bindings "just before the statement or final form
that contains the call" but does not order them among themselves.
§65 says the macro world "is threaded sequentially through all of
elaboration", so some sequential order exists, without saying which.
In run position §6 item 1 adds that "A head that is a form is `Settled`
in run position, since it runs as soon as it is elaborated (§29)", and
§28 that each form there "runs as soon as it is elaborated", so a
form's compile-time effects follow its elaboration order.
§50's expectation for an argument is "its parameter, given the
arguments before it", and §36 instantiates an `at` target "with the
earlier arguments"; [A] these constrain what an argument's checking
may depend on, not the order in which compile-time effects happen.
[A] I could not find a sentence that fixes the left-to-right order of
the items.

### 3.7 Errors [D/C]

- [D] There is a positive error *content* requirement in places: a
  failed `comptime-match` "prints the expected constructor and the actual
  value" (§28), `compile-error` reports "the text of `m`" (§4), and §62
  says which macro calls a message names. DESIGN.md says nothing
  explicit about reporting more than one error. "whichever one the
  elaborator meets first" appears in §15, and §4's "Warnings go to
  standard error and do not stop elaboration" may be read as implying
  that an error does stop it. §54 says `dump-context` "stops
  elaboration with a report of the context"; the reference stops
  there, and slc goes on (`tests/dump_context.sl`, 10 §1).
- [C] `two_errors.sl`: the reference reports only `one`, and slc reports
  `one` and `two`; self/README.md:298-301 says slc records errors and
  goes on, and slc's `--first-error` (MANUAL.md) stops its report, not
  its elaboration, after the first.
  `error_then_effects.sl`: after the first error, slc still prints a
  later `compile-warn`, but then refuses a later macro call as not
  constant-known. slc gates its run-position runs on there being no
  earlier error (`self/elab-main.sl:539`, `:545`, `:739`, `:2152`, each
  testing `(env-run-pos …)` together with `(not $ env-failed …)`, and
  `:2152` also a `many` mode), so after an error it
  seems not to run run-position code through its evaluator. Macro
  expansion is not gated, so a macro bound before the error still runs
  at compile time (10 §2). A
  run-position `let` whose right-hand side hoists a temporary leaves its
  binders `Hypothetical`: a call with argument `(Zero)`
  (`proto/review2/after_error_call.sl`, `after_error_call2.sl`) and
  `(Succ (Zero))` (`proto/review4/01_after_error_succ.sl`) give no
  `Settled` result. A macro bound after the error is not dispatched
  (`after_error_macro.sl`). Otherwise, in the cases 10 traced (a call
  with a variable argument among them), the binders are
  `Settled` but hold the erased token, not a computed value
  (`env-set-tokens`,
  `self/elab-main.sl:2209-2216`), and slc's discriminant read takes a
  token as the word 0 (`self/eval.sl:51`). So a nullary `(Zero)` bound
  after an error reads as `0` ("expected `Succ`, got 0",
  `proto/review2/after_error_run.sl`) only by coincidence: `(BFalse)`
  reads as `(BTrue)`, and `3` as `0`, giving false later messages (10
  §1 to §3; BUGS.md 25). A string literal, or a `Settled` string
  variable, gets the token too: `comptime-match` reads it as `(SNil)`,
  and a `compile-warn` of it says it "is `Hypothetical`", slc's wording
  for any stored value that is not a string (`self/elab.sl:2585-2587`;
  `proto/review7/10_string_token.sl`). Acceptance seems unaffected, since the first
  error already makes slc exit 1 (10 §4).
- [C] Both implementations read a whole file before elaborating it.
  `reader_phase.sl` (a missing `)` on line 3) and `pragma_phase.sl` (an
  unknown pragma) print no earlier `compile-warn`. Reading is per file,
  though: with two files on the command line, where the second has a
  syntax error, the first file's `compile-warn` is still printed
  (`proto/review2/rf_a.sl` then `rf_b.sl`, on both implementations);
  the reference even prints the first file's final value, `0`, on
  standard output before the second file's syntax error, and exits 1.
  When the first file's final value is a `Program`, the two differ in
  acceptance: with `proto/review5/01_prog_first.sl`, whose `Program`
  writes `effect` and exits 0, followed by `review2/rf_b.sl` (a syntax
  error) or `review5/01_late_error.sl` (a `compile-error`), the
  reference prints `effect` and exits 0, reporting no error, and slc
  reports the second file's error and exits 1 without running the
  `Program`. The reference reads each file on the command line only
  when it reaches it (`bin/main.ml:11-16`), and its driver ends the
  process when the `Program` ends (`lib/program.ml:116`), so it never
  reads the later file. Each implementation treats files made by a
  `;! file` pragma (§4) as it treats files on the command line (`proto/review6/01_pragma_file_prog.sl`,
  `01_pragma_file_late.sl`: the reference prints `effect` and exits 0,
  slc reports the later file's error and exits 1). Under
  `--warnings-as-errors` the reference holds every final value back
  until all files are elaborated (`bin/main.ml:97-102`, `:109-110`), and
  `01_prog_first.sl` then `01_late_error.sl` is refused, with no
  `effect`, though no warning is given. It is refused under `--extract`
  too, which runs no final (`bin/main.ml:93`). [A]
  Where reading or elaboration fails only in a
  later file, acceptance then depends on when the driver runs, which
  section 5 item 14 raises; otherwise reading can be a separate total
  function per file, or for all files at once.
- [C] mini/ makes each judgment total with "an [Ok] with what was
  derived or an [Err] with the first reason found" (`mini/elab.sl:3-4`).
  `Fails` is a one-constructor relation over a derivation of
  `ElabProgram`'s `Err` outcome, `PErr` (`mini/elab.sl:1224-1241`).
  But "A malformed shape is not a reason: the relations have no
  derivation for one" (`mini/elab.sl:40-42`; `mini/README.md:140`), and
  `elab-program` can answer `ProgramStuck` (`mini/elabfn.sl:2374-2380`).
  [A] At source level that gap breaks theorem 3, so malformed syntax
  must become a positive `Err`.

### 3.8 Nondeterminism that reaches acceptance

- [D] `slot-eq`: "an implementation may always answer [ENone], and which
  one a call answers may differ between runs" (§67). [C]
  `slot_eq_comptime.sl` (`comptime-match` on `ESome`) is accepted, and
  `slot_eq_comptime_none.sl` is refused, on both implementations, and
  also under the reference's `--no-extern` (slc has no such flag). [A] So an implementation that answers `ENone`
  would conform to DESIGN.md and have the opposite outcomes. [C] Both
  answers already occur at compile time: in
  `proto/review7/01_slot_eq_native.sl`, a `comptime-match` expects
  `(BTrue)` from a `native-compute` of a function that asks `slot-eq`
  about the slots of `(add 1 2)` and `3`. The compiled run answers
  `ESome`, and both implementations accept; under `--no-native` the
  evaluator answers `ENone`, and both refuse, as does the reference
  under `--no-extern`. Acceptance is not a function of the source under
  DESIGN.md as written.
- [D] `native-compute` "may crash where the evaluator would not" (§72).
  §31 crashes are a host matter. [A] These are compiler outcomes, not
  spec outcomes (decision 7).
- [A] Gensym numbering and the expansion count are deterministic once
  the order is fixed (decision 5). `read-file` is deterministic given a
  fixed oracle, but a file changing during compilation is outside any
  static oracle. I could not determine whether §50's meta solving can
  depend on order within one boundary.

### 3.9 What a source-level spec must cover in the reader [D/C]

§1: atoms, `;` comments, string tokens, digit atoms, `#\c`, `#"..."` raw
names, and the ban on `__` names (refused by both implementations,
[C], `proto/review2/dunder.sl`). §2: `$`, and "the missing
`)` is an error" (`dollar_top.sl` [C]). §4: `;! warn`, which "must be
written between top-level forms"; `;! suppress` and `;! restore`, which
"may appear at any nesting depth"; `;! file "name"`
(new file name and line numbering), and "Any other word after `;!` is an
error". §45: numeral, character, and string syntax and escapes. §63:
literals are interned "just before" each top-level form is elaborated.
[A] So the reader outputs literal *tokens*, and interning is an
elaboration step that changes Σ. Positions can be observed: [C]
`pos_observable.sl` gives a macro its `here`, which prints as
`(MkPos "…/pos_observable.sl" 7 13)` and `… 7 21` across a tab, the
file named as on the command line. Columns
are 1-based byte counts, and a tab counts 1; that the unit is bytes, not
characters, is shown by `proto/review2/pos_bytes.sl`, where a
two-byte `é` before the call gives column 41, the byte count, not 40.
DESIGN.md does not define the unit.

### 3.10 mini/ as a starting point [C/A]

- It keeps: the canonicalization and unification layer, structural and
  free of fuel (`mini/README.md:49-60`); the Ok/Err total judgments; ids
  that are never reused, with the context's `next` surviving `Leave`
  (`mini/README.md:120-125`, which names one exception, the entries a
  telescope is elaborated with), which is Σ/Γ in embryo; and the
  relation-plus-deriving-function pairing.
- Not compatible with the full language: keywords are reserved `RKey`s
  (`mini/elab.sl:8-38`; README:138), but §19 says special forms "may be
  shadowed"; `Sexp` has no `Pos`; `ElabTerm` is pure (README:125), but
  a type can contain a macro call (§9); `Eval` is environment-based, not
  a heap machine, and its deriving function `eval` is fuelled
  (`mini/eval.sl:53`); and malformed shapes
  get stuck.
- What was cut is exactly the hard part. MINIMAL.md "What is removed"
  item 4 removes `Settled`, "the compile-time round trip", macros, and
  `Special` as a value, so that "Elaboration is a pure function from raw
  syntax to core terms; evaluation is a separate phase after it". The
  decisions it records ("Evaluation and typing are relations", "A
  positive `Fails` relation … beside the relation that types it") are
  MINIMAL.md's record, and may need to be revisited once the two
  relations are intertwined.

## 4. Options

### 4.1 Where the spec starts

| Start | Design | Pros | Cons | Cost (rough, [A]) |
|---|---|---|---|---|
| Bytes | `read` function, then a relation over `Raw` | Theorem 3 literally; positions and pragmas covered | Reader rules (pragmas, escapes, `$`) must be specified | Reader: a few hundred lines |
| `Raw` | Relation over §63's `Raw` plus pragma events | Reuses the language's own `Raw`; reader trusted | Theorem 3 is about `Raw`, not source; pragmas need a side channel | Smallest step over mini/ |
| Core | Typing over expanded, dispatched code, with Σ given | Closest to mini/; cheap | No dispatch, macros, or `read-file`; theorem 3 is not about source | Low, but leaves the hard part outside |

### 4.2 Judgment forms [A]

- `read : List (Name, Bytes) → Items | ReadErr Pos Reason`. `Items`
  holds `Raw` forms with `Pos`, literal tokens, and pragma events.
- Fact engine: `Canon F t t'`, `Unify mode F eqs (Ok F' | Contra)`.
- `Run Γr Σ code (ws, Σ')`, where Γr is the read-only scope and the
  facts of the innermost run position (for `resolve` and `settled-eq`).
- `Elab Γ ρ Σ raw (Ok Γ' code ids | Err e) Σ'`, where ρ is the mode:
  run position, or a body with its level and subterm arguments, or an
  erased position.
  - Γ, restored when a scope ends: the scope list of §5; the facts,
    split into the facts of the innermost enclosing run position and
    those added below it, in bodies and branches, because §6 and §65
    read only the former ("the table as it stood at the innermost
    enclosing run position", §7); the
    opened `Matchable`s and `AtFn`s; and the ambient level and subterm
    arguments.
  - Σ, threaded: the heap; the id counter (introduction order); the
    literal table; the out-of-scope minted entries; gensym; the
    expansion count; the claimed extern names; the goal and qed state;
    the slot-eq oracle stream; and the emitted warnings. Uses of unique
    binders are threaded per path and joined at a match (§15).
  - [A] §65 counts "the run-position entries with their values and
    facts" as part of the macro world, which §3.3 identifies with Σ.
    This split keeps those facts in Γ and only the words in Σ, so the
    identification of §3.3 holds only in part; which side the
    run-position facts belong on is open.
  - Run-position rule: `Elab … (Ok code)`, `Strip code c`, and
    `Run Γr Σ c (ws, Σ')`. The entries become `Settled` with words in
    `Σ'.heap`, a minted type, and a minted `is` (§29).
- `Program flags fs ffi prelude files (Accept Σ finals | Reject e)`,
  with one final value per file that ends in an expression (§27: "A
  file that ends in a statement produces nothing. Otherwise the type of
  the final value decides what the driver does with it"), including the
  treatment of each final value in §27 (a final `Fn` "in neither form …
  is an error").

### 4.3 Rejection

(i) `Reject` is "not accepted": weak, and gives no constructive
exhaustiveness. (ii) A positive `Fails` as the Err outcome (recommended):
exhaustiveness is totality, which needs H, and exclusivity is
functionality, which needs decisions 5 and 6. (iii) A separate `Fails`
relation, with exclusivity and exhaustiveness proved: more duplication,
against rule 5.

### 4.4 Determinism

Per decision 6 for `slot-eq`. Everything else seems deterministic once
the order is fixed. The agreement theorem would read: compiler accepts
⇒ spec Accept with the same Σ-observables; compiler rejects with first
error at p ⇒ spec Reject at p; compiler crashes ⇒ nothing.

### 4.5 The prelude

See decision 9. Under (c), the spec must say how it finds the prelude's
`Nat`, `Char`, and `String`. §45 says literals refer to them "whatever
names the program has shadowed since". [A] So they are captured from
the prelude, not looked up in the program's scope. [C] Capturing them
when the prelude ends would not cover the prelude's own literals: the
shipped prelude (2881 lines) uses its first string literal at
`lib/prelude.sl:2526` and its first numeral at `:2542`, in the `let`
that defines `unary` and `prove-literal-lt`. Where in the prelude the
capture happens is open.

### 4.6 Staging [A]

The principle: a feature that changes the judgment's *signature* goes
before one that only adds rules.

1. S0, the reader and Items, with a positive ReadErr. It is total and
   needs no fuel. It is independent of everything else.
2. S1, mini/ recast into the final shape: Σ threaded; `Pos` and a
   positive Err for malformed syntax; `Raw` from §63 (without
   `RawSettled`); special forms resolved through scope entries bound to
   `Special` values (§42), not `RKey`. [A] These entries must be
   `Settled` from the start for §6 to dispatch on them; §42 does not
   say so (see section 5 below, item 12).
3. S2, `Settled`, run position, the round trip, `comptime-match`, and
   forwarding `let`, with `Run` as a parameter (mini/'s `Eval`, or the
   heap machine of the run track). Stripping is the identity at this
   stage.
4. S3, multiplicities, erasure, and uses (§13 to §16), `Matchable` and
   its open (§8), and the real strip. S3 could equally come before S2.
   The argument for S2 first is that S2 changes every rule's signature
   (Σ, ρ, the Run premise), while S3 mostly adds per-entry data and
   checks. Both orders seem workable.
5. S4, extern models with the FFI-table parameter, then `Macro`, `Raw`,
   the macro world, the expansion limit, gensym, the `read-file` oracle,
   literals, and finally the real prelude as input. `Raw` and `String`
   are `extern` (§63, §45), so macros need extern models first.
6. S5, slots, `at`, cells, placement, at-functions, `coerce`, `tail`,
   and `delegate`.
7. S6, the sugar of §46 to §53, warning pragmas, goals (§71), and
   `native-compute` (§72).

## 5. Rough edges, contradictions, and gaps in DESIGN.md

1. The order in which an application's arguments are elaborated and
   their macro calls expanded is not stated, but gensym ("counting from 1 over the whole
   run", §65), the expansion count (§62), and which error an
   implementation reports first make it observable. (§15's "whichever
   one the elaborator meets first" covers only two conflicting uses of
   one unique binder.)
2. `slot-eq`'s freedom (§67) reaches acceptance through `comptime-match`
   in run position (tested, §3.8).
3. A crash in run position: only §72 says "a run that crashes is an
   error". MANUAL.md (`--eval-fuel`) says a crashing run-position form
   "is refused". For the general case, §31 says "A crash produces no
   value, never a different one. How a crash is reported is not
   specified; it need not be a runtime error", which does not say
   whether the program is then refused.
4. Numerals: §1 says "Atoms made only of digits … are numeral …
   literals", and §45 says a numeral has "no leading zero". It does not
   say what `042` is. [C] Both implementations: "syntax error: 042 has
   a leading zero" (`leading_zero.sl`).
5. String escapes: "Any other byte, including a newline, stands for
   itself" (§45) could be read as allowing `\q`. [C] Both
   implementations refuse it: "unknown escape \q" (`esc.sl`).
6. `Pos` columns: the unit is not stated (§42 says only "a line and a
   column (`Nat`)"; §4 counts lines "from 1" after `;! file`). [C] In
   both implementations columns are bytes, 1-based, with a tab counting
   1. It is observable by macros.
7. The expansion limit's scope says "every file on the command line
   included" (§62). It does not say whether the prelude counts. [C] The
   reference does not reset its counter, and the shipped prelude expands
   no macro: a program of exactly 10000 expansions is accepted by both
   implementations (§3.5, `proto/review6/01_count_10000.sl`). So the
   question bears only on a prelude that does expand one. Nor does §62
   say what a call past the limit does (decision 3).
8. `--warnings-as-errors` is in DESIGN.md (§4), but which warnings exist
   beyond §4's is in WARNINGS.md. So under that flag, acceptance depends
   on text outside the spec. [C] `fuel.sl` draws an implementation
   warning ("same-level call … mark it `notail`").
9. "The prototype's FFI is a fixed table keyed by the declared name"
   (§42) puts one implementation's table into the definition of
   acceptance.
10. `dump-context` is defined by reference to MANUAL.md (§27, §54) and
    "stops elaboration" (§54); slc goes on after its report (§3.7). [A]
    For the spec it is an `Err` with unspecified content.
11. Multiple errors: DESIGN.md says nothing explicit (§4's "Warnings
    ... do not stop elaboration" may imply that errors do). The two
    implementations differ after the first error (tested).
12. Where `Settled` entries come from: §29 says "`Settled` arises at three
    sites" and "Nothing else creates a `Settled`", and concludes "So
    any `Special` or `Macro` that is ever invoked (§6) comes from run
    position". [A] Possibly in tension with this: the built-in
    `Special` entries of §42, which §6 needs to be `Settled` to
    dispatch, are in scope "Before any file is read" (§42), not made in
    run position; and
    `mint-settled` and `mint-settled-erased` mint "a fresh anonymous
    `Settled` entry", and `settled-ty-apply` and `settled-val-apply` give
    a handle to one (§65), inside a macro's run, which is not obviously
    one of the three sites. A literal's entries are "as if minted by
    run-position forms" (§45), which ties them to site 1. A question for the owner,
    not a resolved contradiction.
13. A head that is a name: §6 says "The head is elaborated first", but
    both implementations expand the macro calls among the arguments
    before they elaborate a name head, so an error in an argument's
    expansion is reported, and the head's error is not
    (`proto/review4/01_head_name_err.sl`, §3.6). DESIGN.md does not say
    which error is reported, so this may be no conflict; but read
    literally, §6 would report the head's error. A question for the
    owner.
14. When the driver runs a file's final value: §27 has "Several files
    on one command line share one scope, in order" and gives each file
    that ends in an expression a final value for the driver, but does
    not say whether a `Program` final runs when its file ends or after
    every file is elaborated, nor whether its `Exit` ends the unit.
    §71's "nothing is printed, applied or written after elaboration",
    said of the modes that turn the driver off, may be read as putting
    the driver after elaboration, but not as saying whether a file's
    or the unit's. The
    reference runs it when its file ends and then exits, never reading
    a later file, except under `--warnings-as-errors`, where it
    elaborates every file first, and under `--extract`, where it runs
    no final; slc always elaborates every file first
    (§3.7, `proto/review5/01_prog_first.sl`). So the two disagree on
    acceptance for such a unit, and the reference's acceptance depends
    on `--warnings-as-errors` even when nothing warns, and on
    `--extract`. §4 makes a
    `;! file` file mean "what it would as a separate file of the unit",
    and both implementations treat it so here. A question for the
    owner.

## 6. Unverified claims

- That the metatheory of elaboration can be proved once over a run
  relation taken as a parameter (decision 10); 05 F7 shows only that
  such indexing is accepted.
- That a proof of theorem 3 without hypotheses would hit the diagonal
  obstacle of statement 1 (decision 2). Here this is an analogy, not an
  argument; 03 F6 argues it, not checked and under its premises, for a
  non-erased `compile` function.
- That §50's meta solving is independent of order within a boundary.
- That the Run layer needs only the fact engine, scope lookup, and Σ,
  and never the full elaborator (§3.2). This comes from reading §65,
  not from code.
- The cost estimates in §4.1 and §4.6.
- That a value semantics for the run would be observably different from
  a mutating heap (§3.3).
- That every program run under `--eval-fuel 5` with the prelude is
  rejected: checked on one program, plus the prelude failing first.

## Review notes

Added by an adversarial review of this file. The test files under
`proto/spec-shape/` were rerun on the reference and on the slc in the
scratchpad; all outputs quoted above reproduce, with the exceptions in
items 4 and 5.

1. Decision 1 cited "§4.4 below" for positions being observable; §4.4 is
   Determinism. Changed to §3.9.
2. Owner statements overstated. §3.3 said statement 6 "asks for" a
   mutating heap; the brief says the owner "suspects" it. §3.5 said
   statement 4 "already frames" termination as H; the brief records only
   "general agreement (not agreement to exact statements)". Decision 2
   said the owner "ruled out" the `no_false` route; statement 1 says no
   such theorem "is expected". The summary's quotation of statement 3
   was not the brief's wording. All reworded.
3. Decision 2 used a broader H ("every compile-time run in the spec
   halts") than statement 4(ii) ("every accepted compile-time form's spec
   run halts") without saying so, and did not mention owner statement 2
   (the `Program`-loop idea), which bears directly on fuel. Both now
   noted; the statement-2 analysis is not done here.
4. §3.4: "`--eval-fuel 5` rejects every program" is false: under
   `--no-prelude` a trivial program is accepted by both implementations
   (rerun). Restricted to programs with the prelude; added slc's
   different message for the same file.
5. §3.8: "on both implementations and under `--no-extern`": slc rejects
   `--no-extern` as an unknown flag. Restricted to the reference.
6. Summary: "`slot-eq` at compile time can flip it (tested)" overstated
   the test: only the `ESome` answer was observed; the flip is inferred
   from §67. Likewise "order ... affects acceptance" is inferred. Also,
   a crash does not stop the spec being functional (its machine does not
   crash, §31); it concerns the agreement theorem. Reworded.
7. Decision 4 used §15's "whichever one the elaborator meets first" as
   if DESIGN.md spoke of a first error in general; §15 is about two
   conflicting uses of one unique binder. Qualified. "agree on the first
   message" was from two programs; qualified.
8. Decision 6 said `slot-eq` "can make one program both accepted and
   rejected", which reads as both outcomes at once. Reworded: different
   conforming implementations, or runs, can disagree.
9. Decision 7's `Crashed` recommendation did not note that both
   implementations refuse a crashing run-position form (MANUAL.md), nor
   that §72 makes a `native-compute` crash "an error at its argument",
   which the recommendation departs from. Added as tensions; not
   resolved.
10. Decision 9: "can only be done by reflection" and "circular" were
    unhedged; marked [A] and softened. "about 2900 lines" replaced by the
    count, 2881.
11. §3.2: the no-cycle conclusion was stated as fact; hedged, and two
    places to check were added (`settled-ty-apply`'s term check; §45's
    option of producing literal entries by elaborating statements).
12. §3.3: "So Σ needs a heap whose blocks change" was an unhedged
    inference; hedged, `cell-write`'s "physical store" (§37) added as the
    stronger citation, and observability left as an open check.
13. §3.5: the "Macro expansion is bounded (§62)" quote is at the end of
    SOUNDNESS.md part 5, not part 6. Fixed.
14. §3.6: added the DESIGN.md text nearest to fixing order (§65's
    "threaded sequentially", §50's "given the arguments before it", §36's
    "earlier arguments"); none fixes the order of effects, so the
    finding stands.
15. §3.9 said `;! warn`, `;! suppress` and `;! restore` are allowed "at
    any nesting depth"; §4 says `;! warn` "must be written between
    top-level forms", and only the suppress/restore pair may nest.
    Fixed. The `__` ban was marked [C] with no test file; rerun ad hoc on
    both implementations and noted.
16. §4.6 S1 cited §42 for special-form entries being `Settled`; §42 does
    not say that. Marked [A] and added §5 item 12, a possible tension
    with §29's "Nothing else creates a `Settled`" (also covering
    `mint-settled` and `settled-ty-apply`). Unsure whether the owner
    reads the built-ins or a macro's run as one of §29's sites.
17. §4.6 S3 referred to "the order the coordinator suggested", which
    the owner cannot look up. Removed.
18. §5 item 6 said the unit of `Pos` lines is not stated; §4 counts
    lines "from 1" (after `;! file`). Narrowed to columns.
19. Summary: the spec's parameter list omitted the `slot-eq` oracle that
    decision 6 recommends. Added.

Not changed, but unsure: whether decision 1's reading of DESIGN.md's
opening paragraph as making head dispatch "central" is fair (it is a
reading, not a quote); and decision 8's exclusion of `--warn-unused`
and `--no-native`, which can change acceptance under
`--warnings-as-errors` and for `native-compute` crashes respectively.

## Second review notes

Added by a second, independent review. Every test under
`proto/spec-shape/` was rerun on the reference and on `_build/release/slc
--interpret`; the outputs quoted above reproduce. New tests are under
`proto/review2/`.

1. §3.7 said "[A] It seems slc stops running compile-time code after an
   error". False as stated: `after_error_run.sl` binds `(Zero)` after an
   error, and slc's `comptime-match` on it reports "expected `Succ`, got
   0", so the value was computed. What does stop is narrower: a call of
   a function gives no `Settled` result after an error, whether the
   function was defined before (`after_error_call2.sl`) or after
   (`after_error_call.sl`) it, and a macro bound after it is not
   dispatched (`after_error_macro.sl`). The claim that this "fits
   statement 4(i)" went with it. Rewritten, with self/README.md:298-301
   ("Errors are values") and slc's `--first-error` cited.
2. Decision 7 (spec machine never crashes, `Crashed` outcome) and 02's
   C4 (compile-time depth bound whose exhaustion rejects) are opposite
   recommendations; neither file said so. Cross-referenced in decision
   2, decision 7, and the summary, which said theorem 3 needs "fuel and
   a third outcome", omitting fuel-as-rejection.
3. §4.2 put run-position facts in Γ, while §3.3 calls the threaded
   store Σ the macro world, which §65 defines as including "the
   run-position entries with their values and facts". Added as an open
   point; not resolved.
4. Decision 9: "`--no-prelude` is the empty prelude" ignored §42, under
   which `--no-prelude` allows `extern` anywhere, while with a prelude
   it is allowed only in the prelude. Qualified.
5. §3.9: "Columns are 1-based byte counts" was tested only with a tab,
   which cannot tell bytes from characters. `pos_bytes.sl` puts a
   two-byte `é` before the call; both implementations give column 41,
   the byte count (40 characters). Added.
6. Decision 1 cited "DESIGN.md's opening paragraph"; the quote is from
   the second paragraph, on the language's aims. Fixed.
7. Summary: "The fact engine of §7 is the one part that is free of
   evaluation" overclaimed (the reader, for one, is also free of it).
   Replaced by §29's own words.
8. §3.2: "interning by `intern-*` must be specified the other way" read
   as a requirement of DESIGN.md; it is this file's condition for
   acyclic layers. Reworded, quoting §45 in full.
9. §3.5: "the prelude ... seems to call none" was [A]; checked by grep:
   the only `MkMacro` applications are at `lib/prelude.sl:2571`, and
   neither macro is called after it. Upgraded to [C]; removed from §6.
10. §3.6 omitted the most direct run-position text, §6 item 1's "A head
    that is a form is `Settled` in run position, since it runs as soon
    as it is elaborated" and §28's "runs as soon as it is elaborated".
    Added.
11. §3.7: the two-file reading test had no file; it is now `rf_a.sl`
    and `rf_b.sl`. Rerunning it showed the reference prints the first
    file's final value, `0`, on standard output before the second
    file's syntax error (exit 1). Noted.
12. §5 item 12 omitted `settled-val-apply`, which also yields a handle
    to a fresh `Settled` entry, and §45's "as if minted by run-position
    forms" for literal entries. Added.
13. "see §5" (decision 7, §4.6 S1) read as DESIGN.md §5 (the scope
    environment). Now "section 5 below".

Unsure, not changed:
- The summary is still about 40 lines, against the brief's 15.
- Why slc, after an error, still runs a constructor application but not
  a call was not traced in its source.
- Whether an empty prelude text should behave as `--no-prelude` is a
  question for the owner (item 4).

## Third review notes

Added by a third, independent review. Every test under
`proto/spec-shape/` and the `proto/review2/` tests this file cites were
rerun on the reference and on `_build/release/slc --interpret`; the
outputs quoted above reproduce. New tests are under `proto/review3/`.

1. §3.6 and decision 5 said the numbers go "left to right, depth first",
   and decision 5 recommended that order as "the reference's order, as
   tested". `gensym_order.sl` cannot tell depth first from other orders.
   `review3/gensym_depth.sl` (`(MkPair _ _ (MkPair _ _ (gs) (gs)) (gs))`)
   prints `(MkPair _ _ (MkPair _ _ 2 3) 1)` on both implementations, and
   `review3/gensym_splice.sl` confirms it one level deeper: every macro
   call among an application's arguments expands before any argument is
   elaborated (`lib/elab.ml:710-722`, `:1380-1383`).
   `review3/gensym_head.sl` shows a head form still goes first. §3.6,
   decision 5, and section 5 item 1 rewritten to the observed order.
2. Decision 2 recommended (a) "stated so that (b) is a corollary". The
   implication runs the other way: the fuelled version needs no
   hypothesis, and (a) would follow from it under H plus a fuel
   monotonicity lemma. Reworded.
3. Decision 4: §28 requires "the expected constructor and the actual
   value", not "the expected and actual values". Fixed. Also added that
   on `fuel.sl` under `--eval-fuel 5` the two implementations differ in
   the first message's position (the reference names the file alone),
   which bears on recommendation (b).
4. §3.5 still cited `lib/prelude.sl:2480` as an `MkMacro` application,
   contradicting second review note 9; line 2480 is the `let` that binds
   both macros, and the applications are at `:2571`. Fixed.
5. §3.5 said SOUNDNESS.md part 6 argues termination "from (T)"; part 6
   uses (T) only for run-position runs. Narrowed.
6. §3.10 said mini/'s ids are never reused; the cited README lines name
   one exception (telescope entries). Added.
7. Section 5 item 1 cited §15 for "the first error" in general, the
   overreach that the first review fixed in decision 4. Reworded.
8. §3.7 attributed reading a whole file first to the reference alone;
   `reader_phase.sl` and `pragma_phase.sl` show it for slc too.
9. Oxford comma in §3.3.

Unsure, not changed:
- Only constructor applications and a macro head were tested for the
  splicing order. Special forms splice their operands through their own
  paths (`lib/elab.ml:922`, `:1079`, `:1740`), not checked one by one.
- The summary is still far beyond the brief's 15 lines.

## Fourth review notes

Added by a fourth, independent review. Every test under
`proto/spec-shape/` and the `proto/review2/` and `proto/review3/` tests
this file cites were rerun on the reference and on `_build/release/slc
--interpret` (and `fuel.sl` and the `--no-prelude` program under
`--eval-fuel 5`, the `slot_eq` pair under the reference's
`--no-extern`); the outputs quoted reproduce. New tests are
`proto/review4/01_*.sl`.

1. §3.7 (from the second review) said "After an error slc still runs
   some run-position code". slc gates each run-position run on no
   earlier error (`self/elab-main.sl:539`, `:545`, `:739`, `:2152`), and
   `review4/01_after_error_succ.sl` shows `(Succ (Zero))` after an
   error gets no `Settled` value; only the nullary `(Zero)` of
   `after_error_run.sl` does, by an untraced path. The inference from
   that one test was wrong. Rewritten, and section 6 adjusted.
2. Decision 5 and §3.6 said the order is "the head first". That holds
   for a head that is a form. A name head is only looked up for
   dispatch first (`lib/elab.ml:1376`) and elaborated after the
   arguments are spliced (`:1380-1383`, which §3.6 already cited):
   `review4/01_head_name_err.sl`, `(nosuch (loop))`, is refused for the
   expansion limit, not for the unbound head, on both implementations.
   Fixed; added as section 5 item 13.
3. Decision 3 asked whether the spec "keeps" the expansion limit, as if
   that were open; §62 already fixes it ("At most 10000 expansions run
   in one run"). Reframed: only making it a parameter `N` is open, and
   that would change DESIGN.md. Decision 8 adjusted to match.
4. Decision 2 derived (a) from (b) "under H together with a lemma that
   more fuel never changes an answer". Monotonicity alone does not give
   it: a lemma that a halting spec run is reached at some finite fuel
   is also needed, with H applied to the finitely many runs of one
   program. Added.
5. §3.2 cited `settled-ty-apply`'s elaboration-time condition ("must
   check as a term") as what the Run layer needs; the run-time one is
   "the application is checked again, against the facts `settled-eq`
   reads" (§65). Both now quoted.
6. Section 5 item 12 omitted §29's most direct sentence, "So any
   `Special` or `Macro` that is ever invoked (§6) comes from run
   position", against which the built-in `Special` entries (bound
   before any file is read) stand. Added.
7. §3.7 said `Fails` "is the `Err` outcome of `ElabProgram`"; it is a
   separate one-constructor relation over a derivation of that outcome
   (`mini/elab.sl:1237-1241`). Fixed.
8. §3.9 quoted `pos_observable.sl`'s output with a shortened file name;
   it prints the path as given on the command line. Fixed.

Unsure, not changed:
- Whether §5 item 13 is a deviation from §6 or only a matter of which
  error is reported, which DESIGN.md does not fix.
- `review3/gensym_head.sl`'s "the head gets 1" is inferred from the
  other numbers, not printed; the earlier notes did not say so (now in
  §3.6).
- The summary is still far beyond the brief's 15 lines.

## Fifth review notes

Added by a fifth, independent review. Every test under
`proto/spec-shape/` and the `proto/review2/`, `proto/review3/` and
`proto/review4/01_*` tests this file cites were rerun on the reference
and on `_build/release/slc --interpret` (and `fuel.sl` and a
`--no-prelude` program under `--eval-fuel 5`, the `slot_eq` pair under
the reference's `--no-extern`); the outputs quoted reproduce. The code
citations were reopened. New tests are `proto/review5/01_*.sl`.

1. §3.7 said, of two files where the second has a syntax error,
   "Acceptance is unaffected, since either way the run is rejected".
   Not so when the first file's final value is a `Program`:
   `review5/01_prog_first.sl` followed by `review2/rf_b.sl` or
   `review5/01_late_error.sl` is accepted by the reference (it prints
   `effect`, exits 0, and reports nothing about the second file) and
   rejected by slc (exit 1, the `Program` not run). Rewritten, and
   added as section 5 item 14: §27 does not say when the driver runs a
   file's final value relative to later files.
2. §4.5 and decision 9 (c) had the spec capture `Nat`, `Char`, and
   `String` "when the prelude ends". The shipped prelude uses literals
   before it ends (`lib/prelude.sl:2526`, `:2542`, in the `let` that
   defines the two macros), so that capture point cannot serve them.
   Reworded; where the capture happens is left open.
3. §4.2's `Program` judgment had one `final`; §27 gives a final value
   to each file that ends in an expression, and both implementations
   print one per file (two files ending `(Zero)` and `(Succ (Zero))`
   print `0` then `1`). Now `finals`.
4. §3.7 and section 5 item 11 said DESIGN.md is silent on more than
   one error; §4's "Warnings go to standard error and do not stop
   elaboration" is nearby text that may imply errors do stop it. Added.
5. §3.10 called `Eval` "fuelled"; the relation `Eval` takes no fuel,
   its deriving function `eval` does (`mini/eval.sl:53`). Fixed.
6. §3.7 said each of slc's four gates is `(and (env-run-pos …) $ not $
   env-failed …)`; `:2152` also tests a `many` mode. Fixed.
7. Decision 8 said `--warnings-as-errors` depends on warnings "defined
   in WARNINGS.md, not in DESIGN.md"; DESIGN.md defines some (§4, and
   the prelude's warnings of §69). Reworded.
8. Section 5 item 12 quoted §42 as "before any file is read"; it is
   "Before any file is read", and the entries are in scope then, not
   made then. Fixed.
9. The [C] tag's description named only `proto/spec-shape/`, while many
   [C] claims rest on `proto/review*/` tests. Fixed.

Unsure, not changed:
- Whether the reference reads a later file at all once a `Program`
  final has exited, or only does not report it; the test shows only the
  latter.
- Whether elaboration order is also observable without macros, through
  introduction order (§5, §18), was looked at briefly: `prove-predates`
  needs a level made by `def-lvl`, a statement, which cannot stand in an
  argument, so no such program was found.
- The summary is still far beyond the brief's 15 lines.

## Coordinator notes

1. §3.7 said a nullary `(Zero)` bound after an error is `Settled` with
   a value read by `comptime-match`, "by a path in slc's source that
   was not traced", and section 6 listed that path as unverified. 10
   traces it: the binder is `Settled` but holds the erased token, which
   slc reads as the word 0, so no value is computed, and the `0` is a
   coincidence. The second review notes' item 1 ("so the value was
   computed") and unsure point (slc "still runs a constructor
   application"), and the fourth review notes' item 1 ("only the
   nullary `(Zero)` ... does" get a `Settled` value), are superseded in
   the same way. §3.7 now gives 10's account, including that macro
   expansion is not gated and that a call with a variable argument gets
   the token too, and points to BUGS.md 25; the section 6 item is
   removed. From 10 §1, §2, and §4.

## Round 6 review notes

Added by a sixth, independent review. Every test under
`proto/spec-shape/` and the `proto/review2/` to `proto/review5/` tests
this file cites were rerun on the reference and on `_build/release/slc
--interpret` (`fuel.sl` and a `--no-prelude` program under
`--eval-fuel 5`, the `slot_eq` pair under the reference's
`--no-extern`); the outputs quoted reproduce. The code citations in
`lib/`, `self/`, `mini/`, `bin/`, SOUNDNESS.md, and MINIMAL.md were
reopened and hold. New tests are `proto/review6/01_*.sl`.

1. §3.7 said slc's `--first-error` "stops at the first". MANUAL.md says
   it "stops its report after the first error"; elaboration goes on (10
   §1, `self/main.sl:45`). Fixed.
2. Decision 2 described owner statement 2 as "a fuel-free deriving
   function run as steps of the driver's `Program` loop". The brief's
   statement 2 is about a fuel-free self-interpreter; applying it to
   elaboration is this file's extension. Reworded.
3. The coordinator note says §3.7 gives 10's account "that a call with
   a variable argument gets the token too"; the body did not say so.
   Added.
4. §3.5 put "`gensym_order.sl` starts its numbering at 1" next to the
   expansion count, which a gensym number does not measure. New tests
   `01_count_10000.sl` (exactly 10000 expansions, accepted by both) and
   `01_count_10001.sl` (refused, "more than 10000 macro expansions")
   show the shipped prelude adds nothing to the count. §3.5 and section
   5 item 7 updated; the gensym sentence now says what it shows.
5. Section 5 item 14 and §3.7 said the reference "reports no error in
   the later file". It never reads it: it reads each command-line file
   when the fold reaches it (`bin/main.ml:11-16`), and a `Program` final
   ends the process (`lib/program.ml:116`), which answers the fifth
   review's open point. Missed: under `--warnings-as-errors` the
   reference holds finals back until every file is elaborated
   (`bin/main.ml:97-102`, `:109-110`), so `01_prog_first.sl` then
   `01_late_error.sl` is refused though nothing warns. Also tested:
   `;! file` files behave as command-line files in both
   (`01_pragma_file_prog.sl`, `01_pragma_file_late.sl`), as §4 says.
   §3.7, section 5 item 14, and decision 8 updated.
6. Section 5 item 13 said the head's error "is reported after" the
   argument's expansion error; the reference stops at the first error,
   so it is not reported at all. Fixed.
7. The summary listed three acceptance-affecting gaps but not the
   driver-timing one (section 5 item 14), the only one already shown to
   split the two implementations. Added.
8. Section 5 items 4 and 5 credited only the reference; slc gives the
   same messages. Fixed.

Also added: `01_splice_output.sl` shows that a macro call's output is
expanded before the arguments after it, on both implementations, which
decision 5 stated from code alone (§3.6).

Unsure, not changed:
- Whether "A fourth" in the summary should instead renumber the list;
  left as an addition.
- slc's out-of-fuel is an error value and evaluation goes on (02 C4);
  whether that changes which first message slc gives for `fuel.sl`
  under `--eval-fuel 5` was not traced.
- The summary is still far beyond the brief's 15 lines.

## Round 7 review notes

Added by a seventh, independent review. Every test under
`proto/spec-shape/` and the `proto/review2/` to `proto/review6/` tests
this file cites were rerun on the reference and on `_build/release/slc
--interpret` (`fuel.sl` and a `--no-prelude` program under
`--eval-fuel 5`, the `slot_eq` pair under the reference's
`--no-extern`); the outputs quoted reproduce. The code citations in
`lib/`, `bin/`, `self/`, and `mini/` were reopened and hold. New tests
are `proto/review7/01_*.sl`; `01_order_accept.sl`, left by an
interrupted reviewer, is used as written.

1. §3.7 said a string literal or a `Settled` string variable after an
   error "leaves the binder `Hypothetical`". It gets the token:
   `proto/review7/10_string_token.sl` gives "expected `SCons`, got
   `(SNil)`" for both, and the "is `Hypothetical`" of a `compile-warn`
   is how `message-of` words any stored value that is not a string
   (`self/elab.sl:2585-2587`), as 10 now says. Fixed.
2. Section 5 item 3 said DESIGN.md "is silent for the general case" of
   a crash; §31 says "A crash produces no value, never a different one.
   How a crash is reported is not specified". Now quoted.
3. Section 5 item 2 said `slot-eq`'s freedom reaches acceptance
   "(tested)" when only `ESome` had been seen, the overclaim first
   review note 6 removed from the summary. `01_slot_eq_native.sl` now
   tests both answers: a `comptime-match` on a `native-compute` that
   asks `slot-eq` passes on both implementations by default and fails
   on both under `--no-native` (and on the reference under
   `--no-extern`). §3.8, the summary, item 2, and decision 6 (c) updated;
   decision 8 notes that `--no-native` changes acceptance without a
   crash.
4. Decision 3 said §62 fixes the limit, so "The question is only"
   whether to make it a parameter `N`. §62 does not say what a call past
   the limit does (as 03 decision 5 notes); both implementations refuse
   it, and theorem 3 needs an outcome there. Added to decision 3 and
   section 5 item 7.
5. §4.2 split Γ's facts into those "of the innermost run position" and
   those "forced in branches". Facts added in a body outside any branch
   (its declarations, opens, a `let-match`'s exports) are neither, and
   §7 has dispatch read "the table as it stood at the innermost
   enclosing run position", which excludes them too. Reworded to "those
   added below it, in bodies and branches".
6. Decision 10 and section 6 called it unverified that an ADT can be
   indexed by a relation-valued `TyCtor`. 05 F7 compiled that:
   `proto/theorems/bove.sl` then `model.sl` is accepted by both (rerun).
   Narrowed to what is still unverified, proving the metatheory once
   that way.

Also added: `01_order_accept.sl` and `01_order_refuse.sl` show a
program whose acceptance turns on the gensym number a macro call gets
(§3.6, summary); §54's `dump-context` "stops elaboration", and slc goes
on after it (`tests/dump_context.sl`), in §3.7 and section 5 item 10;
§71's "nothing is printed, applied or written after elaboration" and
the reference refusing the `01_prog_first.sl` pair under `--extract`
(`bin/main.ml:93`) in §3.7 and section 5 item 14; 03 F6 as the argument
behind decision 2's diagonal analogy. Checked and not added: both
implementations count expansions across the files on the command line
(`01_files_6000.sl` then `01_files_10000.sl`, 10000 in all, accepted;
then `01_files_10001.sl` instead, refused), and in
`01_order_forms.sl` the entries of a `values`, a `let`'s statements,
and a call's arguments take gensym numbers in decision 5's order on
both.

Unsure, not changed:
- §4.6 says S2 "changes every rule's signature (Σ, ρ, the Run
  premise)", but S1 already threads Σ, and the summary puts the run
  mode in the shape fixed first. Possibly S2 only grows Σ (a heap);
  which was meant is the author's to say.
- Whether decision 8 should list `--extract`, which changes the
  reference's acceptance in item 14's case, and `--build`, which takes
  the same path (`bin/main.ml:93`) but was not run.
- The summary is still far beyond the brief's 15 lines.

## Round 7 coordinator notes

1. Decision 7 said both implementations refuse a run-position form
   whose run crashes. On a host stack overflow both die instead,
   naming no form (02 r7.3, r7.4; BUGS.md 27). Narrowed. Raised by
   the round-7 check of 00-summary.

