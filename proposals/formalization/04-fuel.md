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

To be filled from `evidence/A1-slc-anatomy.md`.
