# 00. Decisions for the owner

A Claude session wrote this overnight, at the owner's request, from
the other files in this directory. It is the one file to read first.
Nothing here is approved, and DESIGN.md, DECISIONS.md, OPEN.md, and
ASSUMPTIONS.md are unchanged. Each decision gives the question, what
bears on it, the options, and the session's recommendation, which is
only that; D11 and D12 are questions only. The numbered files give the
detail and the evidence:

- 01, what can be proved and how it would be stated;
- 02, the specification's run;
- 03, the static specification;
- 04, fuel;
- 05, the compiler route and where the output proof stops;
- 06, where DESIGN.md is silent or gives a choice;
- 07, prior art;
- 08, the spikes and how to run them;
- 09, a staged plan;
- `evidence/`, the sub-agents' reports as they wrote them.

## The decisions at a glance

| | The question | The session's recommendation |
|---|---|---|
| D1 | What "either accepted or rejected" is a theorem of, given that no total `compile` that is always right can exist | The compiler's only exits are the two verdicts, each with its derivation; beside it, the theorem under a hypothesis |
| D2 | Whether "never both" and "the compiler stops when the specification's runs do" are in scope | Both |
| D3 | Whether the specification's run is a mutating heap machine on code with its erased positions removed, and how it is written | Confirm; a small-step machine as the definition, with a big-step relation proved to agree |
| D4 | The order of evaluation among siblings, and whether DESIGN.md states it | Strict left to right, stated in DESIGN.md |
| D5 | How addresses are modelled | Any fresh address; equality only |
| D6 | What reaches a run from outside the source, and how the theorems treat it | One record of the outside's answers, as a parameter of the relations |
| D7 | Where the specification starts, and what "rejected" covers | At source text; no third outcome; the prelude inside |
| D8 | Fuel | A certified step machine with no counter; the elaborator waits for it by replay |
| D9 | Retrofit slc, put a kernel behind it, or write a new compiler | A new compiler grown from the specification, taking slc's proved parts |
| D10 | Where the proof stops on the output side | At code with its erased positions removed, for now |
| D11 | Process | Four questions |
| D12 | What "parameterized" means | A question |

## What the handoff reports as already decided or stated

Second-hand, from the previous session's handoff, in its words where
quoted.

- Item 1: no `no_false` theorem is expected.
- Item 2: "A fuel-free self-interpreter is possible because the top
  level is not a function; it is the continuation that the driver
  loops over"; "Whether that approach makes sense for the interpreter
  was left to analysis" (D8 takes it up).
- Item 3: "It should be a theorem that every program's source code is
  either accepted or rejected as an error" (D1 asks how it can be
  stated).
- Item 4: the owner asked whether anything would catch a naive
  infinite loop in the compiler's core, and answered the previous
  session's two results with "I think I'm in general agreement", which
  the handoff says "is not agreement to exact statements".
- Item 5: the owner would "strongly discourage you from relying too
  much on the lean proof".
- Item 6: the owner "suspects the spec's run should be a mutating heap
  machine from the start"; the previous session's reading of that is
  not confirmed (D3 asks).
- Item 7: the owner "voiced concern about three session proposals: not
  modelling a heap machine, a pure and order-free run, and running in
  stripped mode", and asked whether DESIGN.md spells out evaluation
  order (D3, D4).
- Item 8: a missing branch is an error by §21.

The handoff notes that none of this is in DECISIONS.md. Recording it
there is part of D11.

## Where these proposals depart from the handoff's

The owner said of the handoff that its approach "may not be the best
approach". Its proposals were taken as a starting point and tested.
Where tonight's work ended somewhere else:

- **Its results (i) and (ii)** on termination are kept in substance
  and restated per source, as T7 of 01. New is the argument that no
  total `compile` without fuel or hypothesis can return the right
  verdict on every source of the whole language (finding 1 below),
  which gives the three ways of D1.
- **Its proposal A, strict left-to-right order**, is still the
  recommendation (D4). The handoff notes that §15's wording "might
  need to follow". Tonight's probes add that neither implementation
  runs a function body that way today, that accepted programs can
  observe the order, and that the two implementations disagree in one
  case.
- **Its proposal B, abstract addresses**, held up in a spike (D5).
- **Its explicit-stack machine looped by the driver** is one of the
  designs for the evaluator (D8). The handoff does not mention the
  harder half: the elaborator has to stop in the middle of a form and
  wait for that machine. D8 has three designs for it, each built on a
  toy.
- **Its proposal to end the output proof at a modelled subset of
  OCaml** is not the recommendation (D10): 05 reports a sub-agent's
  judgment that it differs from a small lower language "more in name
  than in assurance", and that it adds an obligation about the OCaml
  compiler. What is recommended instead is the handoff's own stated
  alternative, to end the proof earlier.
- **Two things the handoff does not raise**: on DESIGN.md's text,
  whether a source is accepted is not a function of the source (D6);
  and "no third answer" has content, since `mini/` and slc both have
  third answers today (D7). On "never both", which the handoff lists
  as an open question, 01 says what it buys: without it the relation
  that says "rejected" is trusted (D2).

## Four findings that the decisions rest on

1. **No Sleight function that takes only a source, with no fuel and
   no hypothesis, can return the right verdict on every source**, if
   the language it compiles includes its own source (01, 1.2; a
   diagonal argument that a reviewer agent checked and no machine
   did). So for the whole language "accepted or rejected" cannot be
   the type of a plain function. 01 gives three statements that remain
   possible (D1). For a part of the language, such as MINIMAL.md's
   fragment, a plain total function is not ruled out (01, 1.2; 09,
   stage 1).
2. **Whether a source is accepted is not a function of the source, on
   DESIGN.md's text.** A compile-time `slot-eq` can decide it, and §67
   lets its answer "differ between runs" (06, G1, with two probe files
   that both implementations treat one way and a conforming
   implementation could treat the other way).
3. **An accepted program can observe the order in which sibling
   sub-expressions run**, through what is written before a failure and
   through the answer to a `Measure` request. Both implementations run
   one form in one order inside a function body and in another at the
   top level, and for one accepted program the reference and slc print
   different output (02, 2.7; the programs are in `spikes/order/`).
4. **One certified step function can be iterated by the driver, by a
   counter, or by an erased halting derivation.** All three check
   today for a toy language (`spikes/three-iterations/`) and for
   `mini/`'s evaluator (`spikes/step-machine/`; 04, 4.2). So for the
   evaluator alone, how the step is iterated is a small choice that
   can be made late. For the compiler it is not: iterating under the
   driver makes the elaborator wait in the middle of a form (D8).

## D1. What "every program's source code is either accepted or rejected" is a theorem of

**What bears on it.** Finding 1 above. 01, 1.2 and 1.3. Prior art
(07): MetaCoq states its checker under a normalization hypothesis and
supplies the hypothesis by an axiom where the checker runs inside its
erasure plugin; CakeML classifies every input string and keeps two
outcomes its theorem says nothing about.

**Options.** Finding 1 says a "don't know" cannot be avoided for the
whole language; the options differ in where it goes. The first three
can be held together.

- (a) *Certified on exit.* The compiler is a loop under the driver.
  Each step is a total function, and the only exits are "accepted" and
  "rejected", each with its erased derivation. Nothing is claimed
  about a loop that never exits.
- (b) *A budget in the language.* DESIGN.md gains a limit on a
  compile-time run, as §62 has for expansions. Running out is then a
  rejection like any other, and `compile` is a total function with no
  hypothesis, provided every other loop in the compiler terminates
  without a counter of its own, which is not established. The rule
  would have to say what a step is.
- (c) *Under a hypothesis.* Given, erased, a derivation of a verdict
  for the source, `compile` is a total function with no fuel. No
  Sleight function can supply that derivation for every source (01,
  1.2, given "never both"), so this is a theorem about the algorithm
  and not a way to run it. As a type it says only that some total
  function returns verdicts from derivations; it is tied to the
  compiler's own loop by sharing its step function, or by T7 (D2).
- (d) *A third answer stays*: "undetermined", with no derivation, as
  slc's "out of fuel" is today. The handoff's item 3 reads as
  excluding it.

**Recommendation.** (a) for the compiler that ships, with (c) stated
beside it as the theorem about the same step function. Under (a) with
(c), the handoff's item 3 is not proved as worded for the whole
language. What would be proved is that the compiler gives no third
answer (T3) and, with T7 (D2), that it answers whenever the
specification derives a verdict. Only (b) gives the sentence as
worded, and it does so by changing which programs the language
accepts; it is the choice if an unconditional total function matters
more to the owner than having no limit on compile-time runs. G7 of 06
asks the matching question for a compile-time run that crashes.

**Blocks.** The type of the compiler's entry point, and so D8.

## D2. Which further theorems are in scope

**What bears on it.** 01, 1.4.

- *Never both* (T4). Without it the `Fails` relation is trusted: a
  `Fails` rule that is too generous would let a compiler reject good
  programs and still be "certified". With it, a `Rejected` exit is
  never given to a source that the acceptance relation covers. It does
  not say that every source has one of the two derivations. Proving it
  is expected to need determinism lemmas for the relations. For the
  full language it can only be stated relative to a fixed record of
  what the outside answered (finding 2 above). The heap-machine spike
  proved determinism of its run relations once the choices are fixed,
  in 177 lines for 160 lines of relations
  (`spikes/heap-machine/det.sl`). For elaboration the size of that
  proof is not known, and nobody has attempted it for `mini/` (09, 9.4
  and 9.7); the 177 lines are for the run relations of a small
  language.
- *The compiler stops when the specification's runs do* (T7): if the
  relation derives a verdict for a source, relative to the record of
  what the outside answered, the compiler reaches that verdict. It
  implies T4. For the step machine alone it is an induction on the run
  relation's derivation: `spikes/step-machine/` proves it for
  `mini/`'s evaluator as a path in the machine's step relation and as
  a function that runs the machine along that path, and does not prove
  it of the plain loop under the driver (04, 4.2). For the whole
  compiler, option (c) of D1 is the cheaper form.

**Recommendation.** State T4 from the first stage, relative to the
record of answers of D6, and prove it stage by stage, so that a
`Rejected` answer never rests on trust in `Fails`. Prove T7 for the
machine. Take D1's (c) as the whole-compiler form.

**Blocks.** How the relations are written: two outcomes that carry
different erased proofs of one fact are different terms, so a relation
meant to be deterministic has to keep proofs out of its outcome
(`spikes/three-iterations/` met this, and compares states only).

## D3. The specification's run

**What bears on it.** 02, 2.1 and 2.2. DESIGN.md §31: "The semantics
is that of a machine with unlimited stack and heap." §27 and §29 say
the evaluator runs code with the erased positions removed. `mini/`'s
run and the Lean model's first run are both over trees with no heap;
the Lean documents record a session's reading that supporting
`cell-same` there would mean tracking slots as locations, "not a case
beside the existing ones", and its machine-agreement proofs came to
39% of its lines. The heap-machine spike wrote a mutating heap machine
both ways, big-step and small-step, in 160 lines of relations that
share every rule touching the heap, and proved that every big-step run
is a small-step run.

**Options.**

- *Confirm the reading*: the run is a mutating heap machine on code
  with its erased positions removed. That much is the handoff's
  unconfirmed reading of its item 6. R1 of 02 adds that the map to
  that code is part of the specification; 06, G13, asks whether it is
  the same object as §19's post-erasure code.
- *Which relation is the definition*: big-step with a threaded heap
  (closer to prose; a run that has not finished has no derivation), or
  a small-step machine with an explicit stack (the step machine of D8
  is then the specification's own step; an unfinished run can be
  described), or both, proved to agree.
- *An impossible path* (a refuted constructor, an absurd branch): the
  run relation derives no result for it, and a positive relation says
  that a run reached one, so that a compile-time run that does is a
  rejection with a derivation (R7); or a named outcome of the run.

**Recommendation.** Confirm the reading. Write both relations over
shared heap rules and prove them to agree; call the small-step one the
definition. That is the recommendation of the spike's author
(`evidence/S2-heap-machine.md`, section 9.1): the step machine's
certificate is then a step of the definition, and a run that has not
finished can be described. Against it: its states are harder to read,
the agreement is proved in one direction only, and MINIMAL.md records,
for the minimal language's relations, that "readability and simplicity
outrank everything else". No result for an impossible path, and a
rejection where a compile-time run reaches one (06, G8, asks).

**Blocks.** Everything in 02; replaces `mini/core.sl` and
`mini/eval.sl` (258 lines) instead of extending them.

## D4. The order of evaluation

**What bears on it.** Finding 3 above. 02, 2.3, 2.7, and 2.8. On this
session's reading, DESIGN.md fixes that a form's sub-forms run before
it (§27 says it of run position), and §15 places an argument's binding
"just before the statement or final form that contains the call". It does not fix the order among sibling
temporaries, among the entries of a `values`, or among the operands of
a cell form, and §15's sentence has two readings. ASSUMPTIONS.md item
168 says the language "specifies no observable evaluation order"; the
handoff warns that the previous session wrongly relied on that item,
and these proposals do not (02, 2.3).

**Options.**

- *O-α, complete §15 on its first reading.* All the temporaries of a
  statement or final form first, in the order written, inner ones
  first; then the rest in place. This is what both implementations do
  in function bodies, apart from the operands of cell forms, where
  they differ. Two choices come with it: which implementation is right
  about cell forms, and whether run position changes to run as a body
  does or keeps today's different order.
- *O-β, strict left to right.* Each sub-expression runs completely
  before the next, the head first. This is the handoff's proposal A,
  and what both implementations do in run position. §15's sentence
  would be reworded as a rule about scope, and both implementations
  would change how a function body runs.
- *O-γ, any order.* The specification would then allow programs'
  outputs to differ, the run relation would not be a function of its
  inputs, the agreement theorem would become a refinement, and showing
  that the order cannot be observed would need the sole-reference
  property (02, 2.3). The handoff's item 7 records that the owner
  voiced concern about "a pure and order-free run".

And, whichever is chosen: is it written in DESIGN.md, or only in the
formal relations?

**Recommendation.** O-β, in DESIGN.md. It is the one rule under which
a form runs alike at the top level and in a function body without
changing how run position elaborates, and it settles the two
implementations' disagreement. Since programs can observe the order,
leaving it out of DESIGN.md would leave their output unspecified.

**Blocks.** The map to post-erasure code; R4 of 02.

## D5. Addresses

**What bears on it.** 02, 2.4. The handoff's proposal B (abstract
names, any fresh address, equality only), which has no reply yet.
DESIGN.md's one sentence with the word is "address equality does not
change when contents do" (§36). The heap-machine spike wrote the
relation with a freshness rule and proved, for its small language,
that a block keeps its address and no address is reused, that runs
are deterministic once the choices are fixed, and that a run with one
choice of addresses gives a run with any other one-to-one choice. The
last cost 413 lines against 160 of relations, and was proved for two
heaps of one shape only.

**Options.** *A-fresh*: the rule takes any address not in the heap.
*A-count*: the heap carries a counter. A third wording under D6: the
address each allocation takes is one more recorded answer, constrained
to be fresh. The handoff records that the owner questioned "whether
the session was assuming a concrete model such as newest or largest
address", which bears against A-count.

**Recommendation.** A-fresh, as in proposal B, with the allocator's
counter kept in the implementation. An implementation then owes only
"my address is fresh", and the renaming theorem is proved once, of the
relations alone. Under A-fresh as stated, today's native build gives
an answer the specification would not allow: `ocamlopt` merges equal
constants, and `slot-eq` then answers `ESome` for two blocks built
separately (05, 5.2). 06, G5, asks whether such sharing is to be
allowed.

**Blocks.** The heap relations of 02.

## D6. What the outside supplies

**What bears on it.** Finding 2 above. 02, R6 and 2.5; 06, G1, G10,
and G14. Several things reach a run from outside the source. DESIGN.md
leaves the answer of `slot-eq` free (§67). It does not fix what
`read-file` finds (§65) or how a `Program`'s requests are answered
(§42). For extern implementations and `native-compute` it fixes the
values (§42: "the same values" as the models; §72: the form "means
`(values (f1) … (fn))`") and leaves free only whether they crash; 02,
R6, proposes to treat their results as answers from the outside as
well, because the proof would not reach them (05, 5.3). Acceptance
also depends on flags, the other files, the prelude's text, file names
and positions, and the order of `Special`'s constructors (06, G10).

**Options.**

- *One record of answers.* The relations take, as a parameter, what
  the outside answered, each answer constrained as DESIGN.md
  constrains it. With that record fixed the relations have no choice
  left. This is one reading of the owner's word "parameterized" (D12).
  Or the relations keep their choices and the theorem is a refinement,
  as in CompCert (07).
- *Compile-time `slot-eq`*: pinned, so that it stops being an input
  to acceptance, or left as §67 has it and recorded.
- *Extern types and functions*: the specification runs the models
  only (and the implementations are an assumption beside the
  theorem), or constructing, matching, and calling at an extern type
  are answers in the record (and §42's requirement relates the two
  instances).

**Recommendation.** One record of answers, with extern operations and
`native-compute` results in it, so that the theorem is about the
relation the shipping compiler actually follows. Ask the owner
separately whether a compile-time `slot-eq` should be pinned; that is
a language question, G1.

**Blocks.** The signature of every run rule and of the top-level
judgment; the statement of T4.

## D7. Where the specification starts, and what "rejected" covers

**What bears on it.** 03; 06, G10 to G12 and G17. The handoff's item 3
says "source code". `mini/` has no reader, and its top-level function
has a third, evidence-free outcome, "stuck", on 28 groups of shapes
its relations have no rule for, the empty program among them; one of
them, a program that ends in a statement, DESIGN.md §27 gives a
meaning (03, 3.1). `spikes/reader/` specifies reading for a subset,
with a total two-outcome reader and "never both" proved, in 112 lines
of relations, 95 of function, and 180 of lemmas (03, S1; 08). It also found that the two implementations disagree on
which characters are whitespace, which DESIGN.md does not say (06,
G12). The prelude uses two declaration forms DESIGN.md does not
mention, `def-prim` and `def-opaque`.

**Options.**

- Start at text, with reading as a relation and a positive failure
  relation; or start at a syntax tree and trust the reader.
- Such a shape is a rejection with a derivation, or an acceptance
  where DESIGN.md gives it a meaning; or a third outcome stays.
- The prelude's text is inside the specification; or the
  specification covers `--no-prelude` plus a stated interface.
- Messages and warnings: outside at first; or inside.

**Recommendation.** Start at text. No third outcome. The prelude
inside, which needs rules for `def-prim` and `def-opaque` in DESIGN.md
first (G11). Messages and warnings outside at first; a `Fails`
derivation names the first error in elaboration order. With warnings
outside, acceptance under `--warnings-as-errors` (§4) is outside as
well.

**Blocks.** T3 of 01.

## D8. Fuel

**What bears on it.** 04. slc's interpreter takes fuel (default
1000000000, bounding depth), and running out is an error the user
sees; in practice the host stack overflows first, at 50000 to 75000
nested calls. A whole compile is one driver step. Elaboration enters
the interpreter thousands of times per compile, up to 689 times inside
one top-level form. The spikes: a step machine for `mini/`'s evaluator
that returns `mini/`'s own derivation and has no counter, ran a
recursion a million deep under a 64 KB host stack, and about matches
the fuelled evaluator's speed; the three iterations of one step; three
ways for the elaborator to wait for the driver, all working; and
doubling, which makes fuel invisible with a small change.

**Options.**

- *The evaluator*: keep fuel, in which case running out stays a third
  answer or becomes the rule of D1 (b); or make it a certified step
  machine (F1) and choose how to iterate it (F2).
- *How the elaborator waits*, if the driver iterates the machine:
  replay from a checkpoint with a log of answers; or continuations; or
  the elaborator as a machine too. Replay keeps every pass a checked
  total function and changes about 7 call sites of slc, and needs a
  quantum and checkpoints to be fast. The other two need no counter at
  all, rewrite the elaborator's main block (95 functions), and take
  its recursion out of the termination check.
- *Is a quantum fuel?* A counter whose running out hands the state
  back and changes nothing the user can see.
- *A first step that needs none of this*: retry with doubled fuel
  under the driver.

**Recommendation.** F1 with all three iterations kept. For waiting,
replay with a quantum and checkpoints. It is the least change by the
spike's estimate (about 7 call sites against the 95 functions of the
main block, counted and not built), and it is the only one of the
three in which the checker still accepts every pass of the elaborator
as terminating, so that a naive infinite loop inside a pass is ruled
out. That the loop of passes ends is a separate argument, which 04,
4.3, reports as not proved. This bears on the handoff's item 4.
Whether a quantum is acceptable under "minimize fuel" is the owner's
call; the continuation design is the alternative if it is not. The
handoff's open point, whether slc's front end keeps fuel for macro
expansion, is answered in passing by 03 and 04: §62's limit of 10000
expansions serves as the measure there.

**Blocks.** The shape of the compiler's top level.

## D9. The compiler route

**What bears on it.** 05, 5.1. slc proves termination and invariants
of representation today, and no relation of typing, running, or
canonical form appears in it; its elaborator records errors and goes
on with placeholders. `mini/` has the shape wanted, for its fragment:
functions that return derivations. Measured there, the deriving side
is 2.3 times the relations. Checking is fast: all of `mini/` in about
3 s, and slc compiles itself in about 5 s. Prior art (07, the survey's
inference): a kernel behind an untrusted front end certifies accepted
programs and, unless the front end is proved complete or rejections
carry checkable refutations, says nothing of rejected ones.

**Options.** C1, retrofit slc. C2, a certified kernel behind slc's
front end. C3, a new compiler grown from the specification. C4, C3
taking from slc what already carries proofs.

**Recommendation.** C4. The relations have to be written first under
every route, and written from DESIGN.md, not from slc. C2 does not
give item 3 of the handoff. slc stays the fast compiler until the new
one covers the language; 09 stages it. The risks 05 and 09 name for
this route: the simplest algorithms may be too slow, at worst too slow
for the compiler to compile itself (09, 9.7), and there are two
compilers until stage 7.

**Blocks.** Who does what next.

## D10. Where the proof stops on the output side

**What bears on it.** 05, 5.2. The emitter makes 48 decisions and its
OCaml means something only as words and blocks; an 834-line header
and 82 templates are trusted under every option; a native build and a
bytecode build of one emitted file already answer `slot-eq`
differently.

**Options.** P1, stop at post-erasure code and the store. P2, a
certified lowering to a small language of words and blocks, and a
printer that decides nothing. P3, a modelled subset of OCaml.

**Recommendation.** P1 now. P1 is the handoff's stated alternative,
"to end the proof earlier and trust all of emission": under it T6 is
proved only for a program run by the certified compiler's own
interpreting mode (today's counterpart is `slc --interpret`), nothing
is proved of emitted OCaml, and the certified compiler itself still
reaches a machine through the trusted emitter (05, 5.2). P2 later, as
its own project. Not P3: by a sub-agent's judgment it differs from P2
"more in name than in assurance". Both rest on OCaml giving the
printed text the model's meaning, and P3 presents that as a semantics
of OCaml that the project cannot check against the OCaml compiler.

**Blocks.** T6 of 01.

## D11. Process

**What bears on it.** 09; 03, S7. Formalizing forces a position on
every point where DESIGN.md is silent. 06 lists 19 such points from an
audit of DESIGN.md alone. ASSUMPTIONS.md has 133 items today; an
agent's classification (`evidence/A8-assumptions-backlog.md`) finds
that 56 of them record a choice that can change acceptance or runs,
that these come to about 30 distinct questions, and that 21 items
present their main choice as the owner's, which CLAUDE.md rule 14
says such an entry cannot do.

**Questions.**

- Where DESIGN.md is silent, may the relations follow the reference
  implementation, with the choice recorded under CLAUDE.md rule 14 and
  the question batched for the owner (S7 of 03)? CLAUDE.md rule 11
  bears on this as well: its default is to stop and ask, and to record
  a gap "as an explicit open question, not a candidate answer".
- Should the handoff's items be recorded in DECISIONS.md now?
- Is the first stage the one 09 proposes: the fragment of MINIMAL.md,
  end to end, from text to a certified verdict and a fuel-free run?
- The behaviours of 04, 4.5; 02, 2.7; and 06, G12, in which slc and
  the reference differ: are they to be entered in BUGS.md?

## D12. "Parameterized"

The handoff quotes the owner: "we parameterized the semantics of the
language, and this, or the syntax of the language, or both, and our
compiler is proven to be in agreement with those." Does this mean (a)
the semantics and the syntax are written down as the fixed objects the
theorems refer to, or (b) the theorems take parts of the semantics as
parameters? The proposals are meant to work under either; D6's record
of answers is a use of (b).
