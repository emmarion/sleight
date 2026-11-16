# 03. The static specification: from source text to a verdict

A Claude session's analysis and proposals, written overnight at the
owner's request. Nothing here is approved, and DESIGN.md is unchanged.
Facts about `mini/` come from `evidence/A3-mini-and-precedents.md`,
which gives the command or the lines read for each; the ones this
session re-checked say so.

## 3.1 What exists

`mini/` writes the semantics of MINIMAL.md's fragment as relations,
each with a function that derives it. MINIMAL.md records, under
"Decided about the semantics", among others: "Evaluation and typing are
relations, not functions"; "The relations follow an algorithm, the
simplest one that can be written down, however slow"; "A positive
`Fails` relation records why a program is refused, beside the relation
that types it". MINIMAL.md's header says its cuts are the owner's
decisions and its wording a session's.

Measured on `mini/` as it stands (A3, sections 2.2 to 2.7):

- 6,849 lines. The relations reachable from `ElabProgram`, `Fails`,
  and `Eval` are 179 ADTs with 662 rules, 186 KB. Everything that
  derives them is 2.3 times that: 86 KB of evidence types, 203 KB of
  functions, and 131 KB of erased lemmas.
- In the eighteen judgments that can fail, 110 of the 168 rules are
  error rules. Each error rule restates the premises that succeeded
  before the failing one.
- The top-level function has three outcomes: an outcome with its
  derivation, or `ProgramStuck` with no evidence
  (`mini/elabfn.sl`, the `ProgramDec` type; re-checked by this
  session). A3 lists 28 groups of stuck origins. All are shape tests
  on the raw syntax, and one of them also reads the context. Its
  eleven stuck runs include the empty program
  and a program that ends in a statement, to which DESIGN.md §27
  gives a meaning (lines 1163 to 1164: "A file that ends in a
  statement produces nothing").
- There is no reader. The input is a syntax tree built by hand, with
  keywords already classified.
- Elaboration never runs anything: MINIMAL.md removes `Settled`, so
  "Elaboration is a pure function from raw syntax to core terms;
  evaluation is a separate phase after it."
- All of `mini/` checks in about 3.0 s with the reference
  implementation and 1.6 s with slc, net of the prelude.

## 3.2 Proposals

Each is a short rule. None is approved.

**S1. The specification starts at source text.** The handoff's item 3
speaks of "every program's source code". Reading is a relation from
text to forms, with a positive relation for text that does not read.
`spikes/reader/` is a prototype for parentheses, `$`, atoms, and
comments (08). The alternative is to start at a syntax tree and trust
the reader; then "source code" in the theorem means the tree.

**S2. No third answer: a malformed shape is a rejection with a
derivation.** This is what T3 (01) needs. Three ways, from A3's
reading, none built:

1. A complement relation and an error rule for each shape. `mini/`
   already has six hand-written "not this shape" families of 2 to 7
   constructors each.
2. One small pattern language over the syntax tree, one "matches"
   relation, and one complement proved once; each judgment's
   malformed rule cites it.
3. Parse to a typed tree first. This fits MINIMAL.md's fragment, where
   keywords are reserved. It does not fit the full language, where
   what a list is depends on the value of its head (DESIGN.md §6,
   lines 234 to 239; §19, lines 741 to 743: "Everything in it may be
   shadowed, including special forms and types"). There the malformed
   rules have to be rules of elaboration itself.

**S3. The relations follow the algorithm DESIGN.md describes.**
MINIMAL.md decided this for the fragment; the proposal is to confirm
it for the full language. DESIGN.md is written as an algorithm: a
scope environment, a fact table, forcing in a stated order. So the
formal specification is, in effect, a simple reference elaborator
written as relations, and "the compiler agrees with the specification"
means "the compiler's faster algorithm computes what the simple one
does".

**S4. A rule for a run-position form has the run as a premise.**
DESIGN.md §27 and §29 make elaboration of such a form a round trip
through the evaluator. So the elaboration relation's rule takes a
derivation of the run relation (02), and the elaboration state carries
the store. §65, lines 2882 to 2885, already describes that state: "The
macro world is the elaborator's program store: the run-position
entries with their values and facts, the literal table, the gensym
counter and the expansion count. It is threaded sequentially through
all of elaboration". The dependency goes one way: elaboration mentions
the run, the run does not mention elaboration, except that a macro's
primitives (§65) read and extend that state.

**S5. What acceptance depends on besides the text is a parameter of
the top-level judgment.** DESIGN.md makes acceptance depend on the
other files on the command line (§27, line 1163: "Several files on one
command line share one scope, in order"; §62's expansion count runs
over "every file on the command line"), on flags (§42 `--no-prelude`,
§70 `--fn-same`, §71 `--goal`), on files read by `read-file` (§65), on
`native-compute` runs (§72), and on `slot-eq` answers in compile-time
runs (06, G1). 02 proposes one mechanism for the last three.

**S6. Which error, and messages.** A `Fails` derivation names the
first error in elaboration order, as `mini/` has it ("the first reason
found"). The text of messages and the warnings of §4 are left out at
first. DESIGN.md itself leaves a choice in one place: §15, lines 625
to 626, "an error, reported at whichever one the elaborator meets
first".

**S7. Where DESIGN.md is silent, the relation follows the reference
implementation, and the choice is recorded.** CLAUDE.md rule 14 gives
ASSUMPTIONS.md this purpose. `evidence/A8-assumptions-backlog.md`
classifies the 133 items that file has today by what each records.
The classes are that agent's judgment from reading each item; it
probed the implementations three times.

- 56 items record a choice that can change whether a program is
  accepted, what it does when it runs, or both. The other 77 are about
  messages only (9), internal to an implementation (63), or stated by
  DESIGN.md today (5).
- 30 of the 56 fall under four shared questions: whether the prelude's
  text and the FFI's table are part of the specification (12 items;
  06, G11); whether the answers to requests are specified or left to
  the outside (8; decision D6); what exactly the post-erasure code is
  on which `tail`, `delegate`, and §39's check are judged (6; 06,
  G13); and the order of evaluation, with the order in which the
  driver takes several files' final values (4; decision D4 and 06,
  G19). The other 26 stand alone. So the backlog comes to about 30
  questions.
- 21 items present their main choice as the owner's, which rule 14
  calls "a contradiction in terms". In 7 of them (88, 136, 144, 145,
  156, 168, and 172) the agent found content that can change
  acceptance or runs and that DESIGN.md does not state.
- The agent lists 11 places where an item and DESIGN.md read
  differently (its section 5). One is item 168, whose "no at fact is
  inferred just because nullary values share an immediate
  representation" stands against §35 and §36; in the agent's probe
  both implementations infer such a fact.

Each of the 56 is a place where formalizing forces either an owner
decision or a recorded choice. This bears on planning: the owner's
review time, not agent time, is likely the scarce resource.

## 3.3 How far the full language is from the fragment

A3, section 2.8, goes through what MINIMAL.md removes and judges, by
reading and not by building, which additions only add rules and which
change the shape of the relations. Its judgments in brief:

| Feature | Effect on `mini/`'s relations |
|---|---|
| Multiplicities and erasure (§13, §14) | Restructures: every entry gains a multiplicity, every expression judgment a position, and a map from elaborated code to stripped code is needed. |
| Uniqueness and `share` (§15, §16, §22, §23, §32) | Restructures: a usage state is threaded through every expression rule and joined across branches. |
| Cells, slots, and `at` (§35 to §41, §66 to §70) | Replaces the run (02); on the checking side slots are atoms of the same fact table, so mostly adds rules. |
| `Matchable` (§8, §24) | Restructures part of unification and the match rule. |
| `Settled`, run position, and `comptime-match` (§5, §6, §27 to §29) | Restructures, and changes the theorem: elaboration gains run premises and the store, and the deriving function has to wait for an evaluator (04). |
| Head dispatch and `Special` as a value (§6, §19) | Restructures: which rule applies to a list is decided by a stored value, not by a keyword. |
| Macros (§62 to §65) | Adds rules to the relation; the function can no longer recurse on syntax alone. §62's limit of 10000 expansions gives a measure without extra fuel. |
| `_` and metas (§46 to §53) | An expected telescope becomes an input of the expression judgments; unification gains a kind of variable. |
| `extern` and the FFI (§42, §43) | Adds rules if the specification runs the models (02). |
| Literals (§45) | Adds rules, after `Settled` exists. |
| `coerce` (§33, §34) | Adds rules to checking; constrains what a word is in the run. |

DESIGN.md's sections that `mini/`'s comments cite span 640 of its
3,156 lines. The reference implementation is 6,639 lines of OCaml and
slc 18,652 lines of Sleight (A3's counts).

## 3.4 Two costs worth designing against

- **Error rules.** Two thirds of the rules in `mini/`'s failing
  judgments are error rules that restate a successful prefix. A shape
  that lets one rule pass a failing premise's outcome through would
  cut the specification's size. Not prototyped.
- **Certificates are first-order.** `stlc/README.md`, lines 59 to 62,
  explains why a function-valued accessibility predicate "would not do
  here": "A closure at a fresh level can call the function that builds
  it, so such a value can be built for a relation that loops."
  `fourcolor/WORKAROUNDS.md`, item 1, notes that a function stored in
  data cannot be called by code defined earlier. So a rejection is
  better carried by a positive relation than by a function into
  `(False)` stored in the verdict, and "never both" (T4) is then a
  lemma stated once at the top.
