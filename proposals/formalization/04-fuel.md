# 04. Fuel

A Claude session's analysis and proposals, written overnight at the
owner's request. Nothing here is approved, and DESIGN.md is unchanged.
What slc does today is reported from `evidence/A1-slc-anatomy.md`. The
spikes are described in 08.

## 4.1 Why something has to give

01, section 1.2, argues that no Sleight function can take only a
source and return its verdict, when the verdict includes the values of
compile-time runs. So the evaluator that the compiler uses at compile
time needs one of three things from outside itself: a counter, a
derivation that the run halts, or a loop that is not a Sleight
function. DESIGN.md has such a loop: the driver's, over a `Program`
(§42, lines 1993 to 1994: "It never recurses, so an unbounded
interaction is the driver's loop over total functions"). The handoff's
item 2 reports the owner's observation that this makes a fuel-free
interpreter possible.

"Fuel" below means a counter whose running out changes what the user
sees. A counter whose running out changes nothing the user can see is
called a quantum.

## 4.2 The proposal: certify one step, and iterate it three ways

**F1. The evaluator is a machine whose single step is a total
function, certified once against the run relation.** `spikes/step-machine/`
does this for `mini/`'s evaluator (08): the machine's stack holds, in
each frame, the erased partial derivation collected so far, so when
the stack empties the machine holds the values and an erased
derivation of `mini/`'s own `Eval`. There is no counter in it.

**F2. How the step is iterated is a separate and small choice, and
the three ways can coexist.** `spikes/three-iterations/` shows all
three over one step function, on the toy language of 01, in one goal
that checks under both implementations:

1. **Under the driver.** Each driver step takes machine steps and
   returns a `Continue`. Nothing bounds the loop. This is statement
   (a) of 01.
2. **Under a counter that hands the state back.** A function takes up
   to `n` steps by recursion on `n` and returns either the result or
   the state it reached. Running out loses nothing: the caller goes
   on from the returned state. Used inside a driver step, this is a
   quantum, and it only sets how often the machine returns to the
   driver. Used with no driver behind it, it is fuel, and could be a
   budget written into the language (statement (b) of 01).
3. **Under an erased halting derivation.** A function recurses on an
   erased derivation that the machine halts from this state. It has
   no counter and is total. This is statement (c) of 01, and it is
   the handoff's result (ii) as the type of a function. Where the
   derivation can be built, as it can for the toy, the function runs.
   For the compiler it cannot be built in general, by 01, so there it
   is a theorem about the step function and nothing more.

The three share the step function and its certificate, so choosing
among them, or keeping all three, costs a few lines each.

## 4.3 The harder part: the elaborator has to wait

In the full language, elaboration needs the result of a run in the
middle of a form: a run-position form "runs as soon as it has been
elaborated, before the code after it is checked" (§27, lines 1179 to
1180); a head that is a form runs and its value decides how the list
is elaborated (§6, lines 236 to 242); a macro's function runs where
its call is expanded (§62). If the evaluator is iterated by the
driver, the elaborator has to stop in the middle of a form, let the
driver run the machine, and go on with the answer. Sleight has no
continuations to capture and no exceptions. Three designs:

- **W-replay.** The elaborator is an ordinary total function of the
  form and a log of the answers already obtained. Where it needs an
  answer the log lacks, it returns the request. The driver runs the
  machine, appends the answer, and calls the elaborator again from the
  start of the form. Each log entry carries an erased derivation that
  its answer is the run's. Its cost is re-elaboration: a form with `k`
  requests is elaborated `k + 1` times.
- **W-continuation.** The elaborator returns either its result or a
  request together with a function that takes the answer and goes on.
  The driver loop runs the machine and calls that function. Nothing
  is elaborated twice. Every elaborator function on a path to a
  request is written in this style.
- **W-machine.** The elaborator itself becomes an explicit-stack
  machine. Not explored: it would turn the largest part of the
  compiler inside out.

`spikes/suspendable-elaborator/` builds W-replay and W-continuation on
a toy (08). The inline quantum of F2 matters for W-replay: if the
elaborator first tries up to some number of machine steps on the spot,
only long runs ever cause a replay.

A design that avoids the wait keeps today's shape: the evaluator
takes a counter, and elaboration calls it directly.

- **W-none, fuel made invisible.** When the counter runs out, the
  driver retries the form with a larger one. Each attempt is one total
  function call that returns a certified verdict or "out of fuel". No
  out-of-fuel answer reaches the user, so this is a quantum in the
  sense above, at the cost of repeated work. `spikes/derivation-and-doubling/`
  does this for `mini/`'s evaluator (08).

## 4.4 What each gives

| | Is `compile` a function? | A counter anywhere? | What can loop forever | Change to slc |
|---|---|---|---|---|
| Today | Yes | Fuel: running out is an error the user sees | Nothing | None |
| W-none, doubling | Each attempt is | A quantum | The retry loop, if no counter ever suffices | Small |
| F1 with W-replay | No: a driver loop | Optional quantum | The machine loop; the replay loop | The evaluator, and the top of the elaborator |
| F1 with W-continuation | No: a driver loop | None needed | The one driver loop | The evaluator, and every elaborator function on a path to a run |
| A budget in the language | Yes | Fuel, as a rule of the language | Nothing | None to the code; a rule in DESIGN.md |

In every row but the first and the last, a verdict that is reached is
certified, and what is missing is a proof that one is reached. That
proof is T7 of 01. For the machine alone it is an induction on the run
relation's derivation, which `spikes/step-machine/` attempts. For the
whole compiler under the driver it needs more, and iteration 3 above
is the cheaper statement: under a halting derivation for the form's
runs, the same step functions give a total function.

## 4.5 The counters slc has today

From `evidence/A1-slc-anatomy.md`, section 2, which gives the line of
each declaration and the searches behind "all". DESIGN.md does not
contain the word "fuel"; its one such limit is §62's.

A whole compile is one driver step: `self/main.sl` ends in
`(Continue _ start)`, and `start` returns `Exit`. A1 confirmed it by
counting continuations in a scratch copy of slc's emitted OCaml: 1 for
slc compiling itself.

| Counter | Starts at | When it runs out | Kind |
|---|---|---|---|
| The interpreter's `fuel`: one unit per application and one more per call of an interpreted body, so it bounds depth | 1000000000, or `--eval-fuel n` | The program is refused: "compile-time evaluation failed: out of fuel" | Fuel |
| The expansion budget and the global expansion count | 10000 | "more than 10000 macro expansions" | §62's limit, where the charge follows an expansion. slc also charges it for rewrites that are not macro expansions, which §62 does not cover (below). |
| `callbacks`, `hop-0` to `hop-9`, `Steps` | | Cannot: erased, or the zero case is refuted in the type | No effect at run time |
| `sugar` | The size of the form | "internal: the sugar budget is spent" | An error for a case believed unreachable |
| `list-refs`, `rope-walk` | The number of allocations so far | An error block; at one site a macro's output is taken as the empty list, silently | An error, or a silent default, for a case believed unreachable |
| `heap-strs-fuel` | 1000000 | A list is cut, silently; only under `--interpret` | Fuel |
| The compile-time printer's depth | 100000 | Prints `_` for the rest | Fuel |
| The generated printer's fuel | 100000 | Prints `?` | Fuel |
| `merge-opens` | One more than the number of opened objects | Answers "merged" without finishing | A silent default for a case believed unreachable |
| `frame-chain`, `str-split-fuel`, `parse-pieces` | A size of the input | Returns what it has | A silent default; the first affects messages only |

Measured by A1 on slc as it stands:

- **The host stack runs out before the fuel.** slc dies with an
  uncaught stack overflow at between 50000 and 75000 nested
  interpreted calls on the default 8 MB stack. A tail loop of
  500000100 iterations is refused with "out of fuel" after 118 s. The
  reference has no fuel unless `--eval-fuel` is given.
- **How often elaboration enters the interpreter.** In one self-compile
  the interpreter was entered 2270 times for run-position forms and
  470 times for macro expansions, and called back into the elaborator
  8 times. Inside a single top-level form there were up to 689 runs (a
  table-building `let` in `core.sl`) and up to 125 expansions (the
  main block of `elab-main.sl`, 3077 lines). So under W-replay with no
  quantum that block would be elaborated at least 126 times.
- **The elaborator's state is one persistent value.** A checkpoint
  before a top-level form costs nothing. The only effects on the
  outside world in the middle of a form are a macro's `read-file` and
  `native-compute`; a replay would repeat them unless their answers
  were logged.

Three behaviours A1 found that differ from the reference or from
DESIGN.md, each with its reproduction in the report:

- A file of 10001 top-level forms with computed heads and no macro
  call is refused by slc with "more than 10000 macro expansions" and
  accepted by the reference.
- `slc --interpret` prints a 60000-element list cut short at the
  printer's depth, with exit code 0; the reference prints all of it.
- After an out-of-fuel error inside a function body slc's interpreter
  goes on evaluating with error values, where the reference stops.

## 4.6 What the spikes measured

`evidence/S1-step-machine.md`, `evidence/S1b-derivation-and-doubling.md`,
and `evidence/S3-suspendable-elaborator.md`; 08 has the commands.

- **A function that recurses on an erased derivation of `mini/`'s
  `Eval`** has exactly the type "given a derivation that the run has
  these values, return them": no fuel, no failure outcome, 73 lines,
  no lemma, accepted by both implementations and stated as a goal. It
  ran faster than the fuelled evaluator on the program measured,
  mostly because it can call a body in tail position.
- **Doubling** needed one failure constructor carrying "stuck" or "out
  of fuel", and a 16-line driver step. Because `mini/`'s fuel bounds
  depth, a failed attempt can repeat nearly all the work: retries cost
  between 1.0 and 1.5 times a single run on a program whose work grows
  with its depth, and 8 to 9 times on one that does a large shallow
  computation before a deep one. A fuel that counted steps would bound
  the total at under four times a single run; that was not built.
- **"The answer never depends on the fuel"** is provable, and was
  proved for a copy of the evaluator that returns evidence when it
  fails as well as when it succeeds: about 600 lines against the 73
  above. It cannot be stated about `mini/`'s evaluator as it is,
  because a type cannot mention a call (§9).
