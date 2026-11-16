# 09. A staged plan

A Claude session's proposal, written overnight at the owner's request.
Nothing here is approved. It assumes the recommendations of
`00-decisions.md`; where the owner decides otherwise, the stages
change with the decision, and 9.6 says how.

## 9.1 The shape of the work

Three kinds of text come out of this project, and they are trusted
differently.

- **The specification**: relations only. It is what the theorems
  refer to and what the owner has to read. The proposal is that it
  lives apart from everything else, under a directory of its own, with
  no functions and no lemmas in it.
- **The certified compiler**: functions that return derivations of
  those relations, and the lemmas they need. Nobody has to read it to
  trust its answers; the checker reads it.
- **The theorems**: a few goals, each a type, stated in the
  specification's files and discharged by the compiler's (01, 1.3).

Measured on `mini/` (03, 3.1), the second kind is 2.3 times the first.
So most of the text is of the kind that needs no review, and the
scarce resource is the owner's reading of the first kind and answering
of the questions it raises.

## 9.2 Before the stages: a skeleton

`evidence/A3-mini-and-precedents.md`, section 2.8, judges that most of
what MINIMAL.md removed does not only add rules to `mini/`'s relations
but changes their shape (03, 3.3): multiplicities give every entry a
multiplicity and every judgment a position; uniqueness threads a usage
state through every expression rule; run position gives elaboration a
store and run premises; `_` makes an expected telescope an input. A
change of shape is paid for 3.3 times over, in the relations and in
everything that derives them.

The proposal is to fix the signatures first: for the full language,
which judgments there are and what each one's inputs and outputs are,
with no rules. That is a short document, it is where decisions D3 to
D7 become concrete, and the owner can review it before rules are
written against it. Rules then arrive stage by stage inside signatures
that already have room for them. This is a judgment call: the
alternative is to grow `mini/` as it is and restructure at stages 2,
3, and 4.

## 9.3 Stages

Each stage is a vertical slice with the same five deliverables:

1. the relations for the slice, each rule traced to the sentences of
   DESIGN.md it writes down (9.5);
2. the compiler for the slice, returning derivations;
3. the goals, checked by both implementations: no third answer (T3),
   never both (T4), and, for the machine, that it stops when the
   relation's run does (T7);
4. differential tests: the certified compiler against the reference
   implementation and slc on the files of `tests/` that fall inside
   the slice, for verdict and for output;
5. the list of places where DESIGN.md was silent or the
   implementations disagreed, as questions for the owner.

| Stage | Adds | What it settles |
|---|---|---|
| 1 | MINIMAL.md's fragment, end to end: reading from text; no `ProgramStuck`; a heap machine in place of `mini/`'s tree evaluator; a step machine with no fuel; one top-level goal | The handoff's item 3 as a checked theorem for the fragment. Elaboration runs nothing here, so `compile` is a total function. |
| 2 | Run position: `Settled`, stored values, `comptime-match`, a head that is a form, a `let` that forwards a state | The first slice where acceptance depends on a run. Decisions D1 and D8 take effect here. `spikes/` has this stage in miniature. |
| 3 | Erasure: multiplicities, the map to post-erasure code, phantom constructors, `absurd`, `else`, `let-match`, `tail`, `delegate` | Post-erasure code as an object of the specification (06, G13); the impossible path (06, G8). |
| 4 | `unique`, `share`, cells, slots, `at`, `coerce`, and the representation of §33 | The machine's whole memory model; decisions D4 and D5 take effect here. |
| 5 | `Matchable`; `extern`, the prelude, and literals; requests and the driver | Decision D6; the prelude as part of the specification (06, G11). |
| 6 | Macros and the macro world; the sugar of §46 to §53; pragmas | Elaboration order as part of the language (06, G9); §62's limit as the measure for expansion. |
| 7 | The compiler applied to its own source | What slc becomes: the fast compiler beside the certified one, or retired. |

The order is this session's judgment of what depends on what. Two
dependencies are in DESIGN.md's text: the representation of stage 4 is
stated in terms of erasure (§33, lines 1464 to 1465: "A value is the
tuple of its constructor's non-erased fields"), so 4 follows 3; and "A
macro is a value of the prelude's `Macro`" (§62, line 2725) that runs
at compile time, so 6 follows 2 and 5. Stages 2 and 3 could be
swapped.

## 9.4 Stage 1 in detail

It can start as soon as D1, D3, D7, and D9 are answered, because the
fragment has no cells, no `slot-eq`, no requests, and no compile-time
runs.

- **Reader.** `spikes/reader/` grown to the full lexical syntax:
  literals, raw names, `_`, the `__` rule, pragmas, and positions. Its
  author's guess is three to five times the spike. It needs the
  answers to 06, G12, first: at least which characters are whitespace.
- **No third answer.** Every stuck origin in `mini/` becomes a
  rejection with a derivation, or an acceptance where DESIGN.md gives
  the input a meaning, as it does for a file that ends in a statement
  (03, 3.1).
- **The run.** `mini/core.sl` and `mini/eval.sl` (258 lines) are
  replaced by relations in the style of `spikes/heap-machine/`, over
  code whose operands are variables. MINIMAL.md's fragment has no
  `unique` and no cells, so its heap is only allocated and read; the
  shape can be settled here before mutation arrives at stage 4.
- **The machine.** A step function with no fuel that returns the
  relation's derivation, iterated by the driver, with T7 proved for
  it.
- **Never both.** T4 for the fragment. `mini/README.md` lists
  "determinism of elaboration" among what is "stated nowhere yet"; the
  proof is new work and its size is not known.
- **One program.** Text in; a verdict with its derivation out; for an
  accepted program, its run on the machine.

## 9.5 Process proposals

- **P1. Trace every rule.** Each rule of the specification is listed
  with the lines of DESIGN.md it writes down. A rule with no such line
  is a place where the specification says more than DESIGN.md, and
  goes to the owner as a question. CLAUDE.md rule 4 allows no comment
  without permission, so the table would be a file beside the
  relations unless the owner permits a one-line citation above each
  rule.
- **P2. Where DESIGN.md is silent, follow the reference
  implementation, record the choice under CLAUDE.md rule 14, and batch
  the question** (03, S7). The existing backlog of such choices comes
  to about 30 questions (03, S7).
- **P3. Reviewer agents check each rule against DESIGN.md's text
  before the owner sees it**, as WORKFLOW.md has for messages.
- **P4. Both implementations check every goal**, since the checker is
  trusted (01, 1.6).
- **P5. A second formulation where one is cheap.** The reader spike
  restated reading as printing and proved the two equivalent; the
  heap-machine spike wrote the run twice. Agreement of two
  formulations is evidence that a relation says what was meant, which
  a "never both" lemma is not (08, 8.7).
- **P6. Disagreements between the three are findings.** Where the
  certified compiler, the reference, and slc differ on a test, one of
  them is wrong or DESIGN.md is silent. Tonight's examples are in 02,
  2.7; 04, 4.5; and 06, G12.

## 9.6 How the decisions change the plan

- **D1 (b), a budget in the language**: stage 2 loses the waiting
  design of 04, 4.3, and gains a rule in DESIGN.md.
- **D3, big-step as the definition**: stage 1's machine needs an
  agreement proof in both directions; the spike proved one direction.
- **D4, O-α instead of O-β**: no change to the implementations'
  bodies; the map to post-erasure code hoists argument temporaries,
  and run position needs a rule of its own or a change.
- **D7, start at a syntax tree**: stage 1 loses the reader; the
  theorem is about trees.
- **D9, C1 (retrofit slc)**: the stages stay, and each one's second
  deliverable becomes a change to slc's functions in place.
- **D10, P2**: a further stage after 7, or beside it: the lowering
  pass and its proof.

## 9.7 Risks

- **The owner's time.** Each stage ends in questions (deliverable 5).
  06 has 19 already, and the backlog about 30 more.
- **Shape changes.** 9.2 is the mitigation, and it may not hold: a
  signature fixed before its rules are written can be wrong.
- **Speed at stage 7.** MINIMAL.md records "the simplest one that can
  be written down, however slow" for the relations' algorithm. A
  compiler that follows the simplest algorithm may be too slow to
  compile itself. The mitigation is route C4: slc's proved data
  structures brought over where their types can state the relation
  (05, 5.1). `evidence/A3-mini-and-precedents.md`, section 3, reports
  that checking time is not the constraint today: the four colour
  unit, 64,979 lines, checks in under two minutes with slc.
- **Never both at scale.** T4 needs determinism of elaboration, which
  nobody has attempted for `mini/`.
- **What no stage delivers.** No theorem says the specification is
  consistent, that every source has a verdict, or that `unique` means
  sole reference (01, 1.5).
