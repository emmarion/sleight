# 08. The spikes

A Claude session's record, written overnight at the owner's request.
Nothing here is approved. Every spike is a toy or a small model built
to test one question. None of them is DESIGN.md's language, and the
two that use `mini/` use its fragment as it stands.

"Passes" below means that the files check with `--goal proved` under
both the reference implementation and slc. This session re-ran every
command in this file from this directory; `spikes/check.sh` runs them
all again in under a minute and ends with "all goals and lemma files
passed". It expects the built binaries at `_build/default/bin/main.exe`
and `_build/release/slc`, or their paths in `REF` and `SLC`.

Each directory that a sub-agent wrote has that agent's report under
`evidence/`. The reports give paths in a scratch directory; the code
they describe is the directory named here.

## 8.1 Index

| Directory | Bears on | The question | Result |
|---|---|---|---|
| `verdict/` | D1, D2 | Can "accepted or rejected, never both" be a goal? | Passes |
| `verdict-machine/` | D1 | Can "certified on exit" be a goal over a step machine? | Passes; runs as a `Program` |
| `three-iterations/` | D1, D8 | Can one certified step be iterated by the driver, by a counter, and by a halting derivation? | Passes |
| `step-machine/` | D8, D2 | For `mini/`'s evaluator: a machine with no fuel that returns `mini/`'s own derivation | Checks and runs; the converse direction proved in two forms |
| `derivation-and-doubling/` | D8 | For `mini/`'s evaluator: recursion on an erased derivation; fuel that doubles | Both pass |
| `heap-machine/` | D3, D5, D6 | A mutating heap machine as relations, big-step and small-step | Checks; four properties proved |
| `suspendable-elaborator/` | D8 | Three ways for an elaborator to wait for a run the driver iterates | All three run with no fuel |
| `reader/` | D7 | Reading text as a relation, with a total reader | Passes, for a subset |
| `order/` | D4 | Can an accepted program observe the order of siblings? | Yes |
| `gaps/` | D6, 06 | Does acceptance depend on more than the source? | Yes |

## 8.2 The statement idiom: `verdict/`, `verdict-machine/`, `three-iterations/`

Written by this session. The language is lists of `Open` and `Close`
tokens, accepted when balanced. 01, section 1.3, shows the goals.

- `verdict/`: two relations, `Accepts` and `Fails`, written
  separately; a goal that packages a function from a source to one of
  the two with its erased derivation, and an erased function from both
  derivations to `(False)`. 57 lines.
- `verdict-machine/`: the goal `CertifiedOnExit` packages a state
  type, a `start`, and a `step` whose result is a next state or a
  verdict. `drive.sl` loops `step` as a `Program`; `run-balanced.sl`
  and `run-unbalanced.sl` end with exit codes 0 and 1. 87 lines.
- `three-iterations/`: one `step`, which also returns an erased
  derivation of a relation `StepsTo` describing what it did, and three
  functions that iterate it: `run-counted` takes up to `n` steps and
  returns a verdict or the state it reached; `run-by` recurses on an
  erased derivation of `Halts`; and `decide-by` builds that derivation
  for every source, which is possible because this toy always halts.
  `drive.sl` uses `run-counted` with a quantum of 3 under the driver.
  177 lines.

What they do not show: anything about a language whose runs may not
halt, or about size at scale.

## 8.3 `step-machine/`

Written by a sub-agent (`evidence/S1-step-machine.md`). It uses
`mini/`'s own files unchanged and adds a machine for `mini/`'s `Core`.

- `machine.sl`: the stack, the state, and `step`, a total function
  with no fuel argument. A state that returns to an empty stack holds
  the values and an erased derivation of `mini/`'s `Eval`.
  `machine_tail.sl` is the same machine with the frames that carry
  only erased data moved into an erased context.
- `drive.sl`: the `Program` drivers, one step at a time or a quantum
  of steps at a time. `test_a_program.sl` gives the value that
  `tests/mini_eval.sl` gives, in 40 steps; `test_stuck.sl` shows five
  programs that end in "stuck" after a few steps and one that does
  not.
- `graph.sl`, `reach.sl`, `traced.sl`: the machine's step as a
  relation, `StepTo`; the proof that a derivation of `Eval` gives a
  path of such steps from "evaluate this code" to "return these
  values", for every stack; and a copy of `step` that returns the
  relation's evidence for each step it takes.
- `guided.sl`, `evalby.sl`, `runguided.sl`: lookups guided by an
  erased proof; `eval-by`, the direct evaluator with the fuel replaced
  by the erased derivation; and `run-from-spec`, which runs the
  machine along the path of `reach.sl` as one total function.
- `heap/`: a second, smaller language with a store. The relation
  threads the store; the machine keeps it in a `unique` array that it
  updates in place.
- `mutants/`: fourteen wrong variants, each refused by the checker
  with a type error (re-run by this session).

What it does not show: that the plain loop of `step` under the driver
reaches a result whenever a derivation exists (04, 4.2); allocation
or addresses in the store prototype; and the report's timings were
taken with binaries that are not in the repository (its `RUN.md`
commands rebuild them).

## 8.4 `derivation-and-doubling/`

Written by a sub-agent (`evidence/S1b-derivation-and-doubling.md`).
Both parts are about `mini/`'s own `Eval` relation.

- `evalby.sl`: `eval-by` takes an environment, a term, and an erased
  derivation of `Eval`, and returns the values, with no fuel and no
  failure outcome. 73 lines and no lemma. `evalby_goal.sl` states it
  as the goal `EvalTotal`.
- `doubling*.sl`, `program_*.sl`: `mini/`'s fuelled evaluator under a
  driver step that retries with twice the fuel. The report measures
  what the retries cost (04, 4.6).
- `eval2.sl` to `fuelqed.sl`: a copy of the evaluator that returns
  evidence when it fails as well as when it succeeds, and a proof
  that its answer does not depend on the fuel (the goal
  `FuelUnobservable`), in about 600 lines.

## 8.5 `heap-machine/`

Written by a sub-agent (`evidence/S2-heap-machine.md`). The language
is a small one of its own, with allocation, an in-place write, a
copying write, a same-word test, a match, and calls; the report's
section 10 lists what it leaves out of DESIGN.md's language.

- `heap.sl`, `code.sl`, `big.sl`, `small.sl`: the relations, 160
  lines. One relation, `Prim`, says what an instruction does to a
  heap. Each step carries a label: nothing, the address an allocation
  took, or the answer of a same-word test. The big-step and small-step
  relations both use `Prim`.
- `heap-fn.sl`, `prim-fn.sl`, `run-fn.sl`, `step-fn.sl`: functions
  that derive the relations, 248 lines. They allocate with a counter;
  the relations ask only that the address be fresh.
- `det.sl`: a run is determined by its labels. `keep.sl`: a block
  keeps its address, tag, and size, and no address is taken twice.
  `agree.sl`: every big-step run is a small-step run. `ren*.sl`: a run
  under one choice of addresses gives a run under any other one-to-one
  choice. `stated.sl` states the converse of `agree.sl` without
  proving it.
- `neg/`: seven files that the checker refuses, as intended; for
  example a same-word test that answers yes for two different words.

What it does not show: closures, cells, slots, `at`, or erasure; and
its renaming proof covers two heaps of one shape only.

## 8.6 `suspendable-elaborator/`

Written by a sub-agent (`evidence/S3-suspendable-elaborator.md`). The
toy, in `common.sl`: a tree is elaborated to a number; a `TRun` leaf
needs the result of a run that may not halt (a Collatz-style step
relation); a `TIf` elaborates one of two sub-trees according to the
value of a third. The `Elab` relation has the run as a premise.

- `r0.sl`, `r-elab.sl` with `r.sl`: W-replay of 04. The elaborator is
  an ordinary function of the tree and a log of answers.
- `rc.sl`: replay with a checkpoint per unit, kept by the driver.
- `rq.sl`: replay with an inline quantum of machine steps.
- `ro.sl`: the log hidden behind a function that answers requests,
  and `total-under-h`: with an answerer that cannot fail, the same
  elaborator has no "need an answer" outcome.
- `m.sl`, `mu.sl`: W-continuation. `bind` is a constructor that the
  driver interprets, and continuations live at one level fixed at the
  top.
- `d.sl`: W-machine.
- `obstacles/`: 22 small files, each showing one refusal or one
  accepted loop that the report discusses; `m-unchecked-loop.sl` is a
  continuation-style walk that the checker accepts and that never
  ends.
- `checks/`: what the replay design does with a forged or mismatched
  log entry.

All eight designs print the same value for the same tree
(`check.sh` shows one line from each, under both implementations).

What it does not show: rejection, a verdict type, or a goal; and its
figures for slc are estimates from counts.

## 8.7 `reader/`

Written by a sub-agent (`evidence/S4-reader-spec.md`). The subset:
`(`, `)`, the bare `$`, atoms, and `;` comments over the prelude's
`String`. No literals, raw names, `_`, pragmas, or positions.

- `syntax.sl`: the relations, 112 lines. `Lex` takes text to tokens;
  `Items` takes tokens to forms and records whether it stopped at the
  end or before a `)`, which is how "a `$` form ends where its
  enclosing form ends" is said; `Unreadable` is the positive failure
  relation.
- `read.sl`: `read`, a total function from a text to "these forms,
  with a derivation" or "unreadable, with a derivation". 95 lines.
- `spec.sl`, `proof.sl`, `qed.sl`: the goal `Reader` packages `read`
  with three lemmas: never both, one reading, and one mistake.
- `adequacy-*.sl`: a second goal. Reading is restated as printing,
  and the two are proved equivalent at the token level.
- `diff/`: comparisons with the readers of the two implementations.
  `run.sh` checks 22 texts, all agreeing. `probe.sh` shows what each
  reader makes of a text. `corpus.py` compares the three on the
  repository's files that have no literal or pragma; its last run, in
  `corpus.log`, has 1132 of 1137 agreeing, and the other 5 are names
  that begin with `__`, a rule the subset leaves out.
- `mutations/run.sh`: three weakened rules, each of which breaks a
  lemma; a reader changed to let a `$` form take the closing `)`,
  which the checker refuses; and one change that nothing notices:
  adding characters to the whitespace table. The lemmas hold for any
  table, so they do not show that the table is the right one.

## 8.8 `order/` and `gaps/`: probes of the implementations

These report what the two implementations do. They say nothing of
what the language is.

- `order/` (from a sub-agent's probes, `evidence/A2-reference-run.md`;
  02, section 2.7): seven accepted programs.
  `values-measure-first.sl` and `values-build-first.sl` differ only in
  the order of the two entries of one `values`, and print "measured
  BEFORE the build" and "measured AFTER the build".
  `values-say-then-crash.sl` and `values-crash-then-say.sl` differ in
  the same way; run with `--eval-fuel 50000`, the first prints `A`
  before it fails and the second prints nothing.
  `values-nested-argument.sl`, with the same flag, prints nothing
  before it fails. On these five the two implementations agree.
  `cell-write-operand.sl` prints "measured BEFORE the build" under the
  reference and "measured AFTER the build" under slc, and
  `cell-write-operand-crash.sl`, with the flag, prints `A` before it
  fails under the reference and nothing under slc.
- `gaps/` (written by this session; 06, G1, G6, and G9): two files
  that differ only in which answer of a compile-time `slot-eq` they
  assert, one accepted and one rejected by both implementations;
  three files that assert at which tag slot a `Special` constructor
  sits; and one that shows the order of macro expansion through
  `gensym`.

## 8.9 What the checker taught

Points that cost time in more than one spike. Each is this session's
or a sub-agent's experience with the two implementations, with the
DESIGN.md section it traces to where one was found.

- A type cannot mention a function call (§9, lines 419 to 420: "The
  elaborated form of a type never contains a function call, and
  elaborating a type calls none"). A statement about what a function
  returns therefore needs a relation, and the function returns a
  derivation of it. This shapes every theorem in 01.
- A numeral is opaque (§45, lines 2200 to 2202: "`3` is not
  `(Succ (Succ (Succ (Zero))))`"), so `0` and `(Zero)` do not unify.
  The spikes' relations over `Nat` are written with constructors.
- Two outcomes that carry different erased proofs of one fact are
  different terms. A relation meant to be functional keeps proofs out
  of what it relates (`three-iterations/` compares states only).
- A `subterm` mark is part of a function's type (§17, lines 696 to
  697: "the marks are part of its signature"). A goal that names an
  unmarked `Fn` cannot be given a recursive lemma directly; a
  three-line wrapper that is not recursive serves
  (`reader/obstacles/subterm-in-goal.sl`).
- Recursion on an erased derivation is accepted in a function that
  returns non-erased values (§21, lines 864 to 865: "Subterm recursion
  (§17) may go through an erased field"). `eval-by` and `run-by` rest
  on it.
- A branch whose constructor is refuted by the indices needs no code,
  and a match all of whose branches are refuted is written
  `(match erased q _)`.
- A function stored in data at a fresh level can call the function
  that builds it, so a function-valued certificate can be built for a
  relation that loops (`stlc/README.md`, lines 59 to 62). Certificates
  are first-order here.
- In continuation style, `bind` cannot be a function at one level;
  it works as a constructor that the driver interprets
  (`suspendable-elaborator/obstacles/`).
