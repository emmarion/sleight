# 02. The specification's run

A Claude session's analysis and proposals, written overnight at the
owner's request. Nothing here is approved, and DESIGN.md is unchanged.
Quotes are DESIGN.md's unless marked otherwise, with section and line
numbers. What the implementations do is reported from
`evidence/A1-slc-anatomy.md` and `evidence/A2-reference-run.md`, and is
never offered as what the language is.

## 2.1 What DESIGN.md already says

- §31, lines 1319 to 1321: "Evaluation is eager. The semantics is that
  of a machine with unlimited stack and heap. A real run may crash
  where the host cannot represent what is asked of it. A crash
  produces no value, never a different one."
- §33, lines 1461 to 1462: "Values have a uniform representation:
  every value is one word, either an immediate or a pointer to a
  block, whatever its type." §33 goes on to fix when a value carries a
  tag, that a newtype is its field, and which words fieldless
  constructors have. It introduces all of this as "a requirement on
  the implementation" (line 1460).
- The run is of code with the erased positions removed. §27, lines
  1180 to 1182: "it is elaborated, its erased positions are stripped,
  the evaluator runs the code". §29, lines 1279 to 1280: an erased
  value "was never computed, because the erased positions are stripped
  before the evaluator runs".
- DESIGN.md defines several checks on that code and names it. §19,
  lines 821 to 824: "Tail position is judged on the post-erasure code,
  where erased positions, types, coercions and placings are gone and
  every `let` that only renames has been resolved away". §39, lines
  1836 to 1841, says what the code of an at-function's body may
  hold: "no call that is not skipped, no constructor application, no
  allocation, no store and no copy. Renames, constants, loads from a
  block, a `values`, a match whose every branch erases to nothing
  (including its dispatch), a nested definition whose remainder
  erases, and absurd code all count as nothing."
- Writes happen in memory. §37, lines 1754 to 1755, of a `cell-write`
  at `unique`: "This is a physical store into memory that the cell's
  eventual invocation re-creates". Lines 1756 to 1758, at `many`:
  "the result is a fresh block holding the old words with the written
  slots replaced".
- Addresses can be compared and nothing else. §67, lines 3044 to 3046:
  "`ESome` proves that `a` and `b` hold one word (§38). `ENone` proves
  nothing, so an implementation may always answer it, and which one a
  call answers may differ between runs." §36, lines 1700 to 1702: "A
  slot may belong to consumed entries; address equality does not
  change when contents do." §38, lines 1809 to 1810: "Nothing relies
  on two slots being distinct."

The handoff's item 6 reports that the owner "suspects the spec's run
should be a mutating heap machine from the start", and gives the
previous session's reading, not yet confirmed by the owner: "the
spec's run is a mutating heap machine on code with its erased
positions removed". The quotes above are consistent with that reading.

`mini/`'s run is not of that kind: its `Eval` is a big-step relation
over environments and value trees, with no heap and no addresses
(`mini/core.sl`, `mini/eval.sl`). The Lean model's first semantics is
also pure, with a machine proved to agree afterwards. Its documents
record that slots are not locations anywhere in it, and that
supporting `cell-same` (§68) "would mean the proofs tracking slots as
locations [...], not a case beside the existing ones"
(`lean/HANDOFF.md`, lines 403 to 406). Its machine-agreement proofs
are 39% of its lines, against 20.5% for all of its soundness proofs
(`evidence/A4-lean-lessons.md`, section 5).

## 2.2 Proposals

Each is a short rule. None is approved. Decision numbers refer to
`00-decisions.md`.

**R1. The run is defined on post-erasure code, and the map from
elaborated code to post-erasure code is part of the specification.**
DESIGN.md's own checks (tail position, `delegate`, "erases to
nothing") already need that code as an object. (D3)

**R2. The run is a relation over a heap.** A word is an immediate or
an address. A heap maps addresses to blocks. The relation threads the
heap. A write through a `unique` cell changes the block at its
address, whatever else holds that address: the relation does not
assume uniqueness, so "a `unique` binder is the only reference" is a
property one could go on to prove of the relation, and no theorem of
01 depends on it. (D3)

**R3. The relation is written twice over the same heap rules,
big-step and small-step, and the two are proved to agree. Which one is
called the definition is the owner's choice.** A big-step relation has
one derivation for the finished run of one form. DESIGN.md calls
Sleight's functions "total functions" (§42, line 1994) and says
"Termination rests on levels" (§17, line 696). Taking termination as
DESIGN.md states it, a function body's run is finite, and the one
unbounded thing, the driver's loop over a `Program` (§42), is a
sequence of such runs with requests between them. A small-step
relation is a machine with an explicit stack that takes one step at a
time. With it as the definition, the step machine of 04 is the
specification's own step, a run that has not finished can be
described, and claims about frames can be stated: `lean/TAIL.md`,
lines 23 to 26, notes that a big-step run "has no stack, so [...]
'this call reuses its caller's frame' cannot be stated". DESIGN.md's
`tail` claim is judged on the code (§19), not on a run, so the
big-step relation loses nothing DESIGN.md states. `spikes/heap-machine/`
wrote both for a small language of its own (08): one relation says
what an instruction does to a heap, both run relations use it, and
"every big-step run is a small-step run" is proved there. The converse
is stated and not proved. The spike's author recommends the small-step
relation as the definition (`evidence/S2-heap-machine.md`, section
9.1). (D3)

**R4. In post-erasure code every operand is a variable or a constant,
and statements run in the order written.** §15 already says an
argument that is not a variable "behaves as if it were first bound to
an anonymous variable" by "a statement (§27) placed just before the
statement or final form that contains the call". With that, the order
of evaluation is the order of the statements that the stripping map
produces, and the only open question is where that map puts sibling
temporaries (2.3). (D4)

**R5. Addresses are names with equality only.** Two candidate rules
for allocation (2.4). (D5)

**R6. What the outside supplies comes through one parameter of the
run relation.** DESIGN.md leaves four things to the outside: the
answers to `slot-eq` (§67), the results of extern implementations when
they are on (§42), `read-file` (§65), and `native-compute` (§72); and
at run time the answers to a `Program`'s requests (§42). The proposal
is that the relation takes, as a parameter, a record of the answers
the outside gave, each constrained by what DESIGN.md says of it (for
`slot-eq`: `ESome` only for equal words). With the models running and
that record fixed, the relation is closed and has no choices left.
This is reading (b) of "parameterized" in 01. (D6)

**R7. The run relation derives no result for an impossible path.**
Post-erasure code has no code for a refuted constructor or an absurd
branch (01, 1.5). The proposal is that no rule of the run relation
gives such a path a result, and that a second, positive relation says
that a run reached a branch with no code. A compile-time run that
reaches one is then a rejection with a derivation, so the compiler
still has an exit there (T3 of 01). For the output's run, T6 of 01
speaks only of runs the relation derives. 06, G8, asks the owner. (D3)

**R8. Values as trees appear only at the boundary.** A request to the
outside is read off the heap as a tree, and an answer is allocated
into it. §42's requirement on extern implementations is also in terms
of values: they "must give a program the same values, though not the
same cost". (D6)

## 2.3 Evaluation order

What the text says:

- §31, line 1319: "Evaluation is eager."
- §27, lines 1185 to 1187, of run position: "This nests: the forms
  inside a form run before it does, and the statements of a `let`'s
  right-hand side complete before the enclosing `let` does."
- §27, lines 1179 to 1180: a run-position form "runs as soon as it has
  been elaborated, before the code after it is checked". §6, line 236:
  "The head is elaborated first." §50, lines 2321 to 2322: an
  argument's expectation is "its parameter, given the arguments before
  it".
- §32, lines 1355 to 1356: "run-position statements are sequential."
- §15, lines 655 to 661: "Every argument to a constructor, a function
  or a cell behaves as if it were first bound to an anonymous
  variable. An argument that is already a variable is not rebound.
  That binding is a statement (§27) placed just before the statement
  or final form that contains the call, so its entry stays in scope,
  anonymously, for the rest of the expression around it, as the
  entries of a `let`'s right-hand-side statements do."
- §29, lines 1241 to 1242, speaks of "the elaborator's own binders for
  its head, arguments and scrutinee (§15)". §15's own sentence names
  arguments only.
- §39, lines 1843 to 1844: "Calling an at-function skips its runtime;
  its arguments are still evaluated, as §15 binds them." §40, lines
  1895 to 1896: an at-match's "scrutinee is evaluated as for any
  match".
- §61, lines 2717 to 2718: "The write stores `h` before the call: left
  to the invocation, that store would follow the call and the `tail`
  claim would fail." This relies on statements running in the order
  written.

What follows, on this session's reading and the audit's
(`evidence/A5-design-audit.md`, sections A2.3 to A2.5):

1. A form's sub-forms run before the form does.
2. §15's "the statement or final form that contains the call" can be
   read two ways. On the first, the binding joins the statements of
   the enclosing expression, which fits §15's own "as the entries of a
   `let`'s right-hand-side statements do". Then in a final form
   `(values (f x) (g (h y)))`, `(h y)` is bound before the whole
   `values`, and so before `(f x)`. On the second, an entry of a
   `values` counts as an expression of its own (§27, lines 1106 to
   1107, calls each entry "a size-one expression"), and the binding
   sits with its entry. A rule of strict left-to-right nesting agrees
   with the second reading and not the first. The handoff's proposal A
   is that strict rule, and it notes that "§15's wording might need to
   follow".
3. §15 presents its rule as one about scope: the consequence it draws
   is that the "entry stays in scope". §39 relies on it for
   evaluation.
4. In run position the order among siblings is the order of
   elaboration, since each form runs when it has been elaborated and
   before the code after it is checked. The text gives that order as
   head first (§6) and arguments in telescope order (§50). This is an
   inference from three sentences. No sentence says "left to right".
   Under the first reading of §15, run position and §15 can disagree:
   an elaborator that takes the entries of a top-level
   `(values (h b) (f (g a)))` in the order written runs `(h b)` before
   `(g a)`, while §15 places the binding of `(g a)` before the whole
   `values`.

What the text does not fix:

a. inside a function body, the order of two argument temporaries of
   one statement or final form, as in `(f (g a) (h b))`;
b. inside a function body, the order of the entries of one `values`,
   and of the items of one `cell-write` or `cell-alloc`;
c. whether the statements of a body run in the order written (§61
   presupposes it), and whether a body runs in the order that run
   position has;
d. whether §15's binding covers a head and a scrutinee, as §29 says in
   passing;
e. which of the two readings of §15 holds.

ASSUMPTIONS.md, item 168 (lines 1589 to 1593), records a different
position, in a session's words that the item attributes to the owner:
"The source language is pure and specifies no observable evaluation
order. Destructive updates implement that pure semantics; their
execution order must not be observable in well-typed programs. The
interpreter's traversal order is an implementation choice." These
proposals do not rely on it. The handoff says the previous session
"wrongly relied on item 168", and that the owner voiced concern about
"a pure and order-free run"; CLAUDE.md rule 14 says an entry of
ASSUMPTIONS.md is not the owner's decision; and the word "pure" does
not occur in DESIGN.md. It is quoted here because 2.7 bears on it:
accepted programs do observe the order.

Options for decision D4:

- **O-α, complete §15.** The temporaries of a statement or final form
  (its arguments, and its head and scrutinee where they are forms) are
  bound before it, in the order written, inner ones first; then the
  entries of a `values` and the items of a cell form run in the order
  written. Function bodies and run position run alike. This adds to
  DESIGN.md only what a to d leave open.
- **O-β, strict left to right.** Each sub-expression of a form runs
  completely before the next, the head first. This is the handoff's
  proposal A. It contradicts §15's placement in the `values` example
  above, so §15 would change.
- **O-γ, any order.** The relation allows every order. Then the
  relation is not a function of its inputs, an agreement theorem
  becomes a refinement, and showing that the order cannot be observed
  would need the sole-reference property, which the project does not
  plan to prove. 07 reports that each of the four formal semantics
  whose order the survey checked (CompCert, CakeML, Malfunction, and
  Standard ML) fixes an order or comes with a proved refinement to a
  chosen one.

A second question under D4 is where a chosen order is written: in
DESIGN.md, or only in the formal relations. If only there, the
relations are stricter than DESIGN.md, and a compiler has to follow
them all the same.

Whether an accepted program can observe the order is a separate,
empirical matter: see 2.7.

## 2.4 Addresses

The handoff's proposal B, which the owner has not answered: "an
address is an abstract name for a block, with no order and no
arithmetic; a step that allocates may take any address never taken
before; a block keeps its address for the rest of the run whatever is
written into it; a word is an address or an immediate; the machine can
read or write the block at an address and can find that two words are
the same word, and nothing else."

Two ways to write allocation in the relation:

- **A-fresh.** The rule may take any address not in the heap. Any
  allocator then satisfies the relation as it is. Two runs of one
  program can differ in their addresses, so "the result is unique"
  holds only up to a renaming of addresses.
- **A-count.** The heap carries a counter and the rule takes the next
  address. Runs are then equal, not merely equal up to renaming, and
  determinism of the relation is a plain induction. The cost is that
  the relation names a particular allocator, which DESIGN.md does not;
  an implementation with another allocator is related to it by a
  renaming. The handoff records that the owner questioned "whether the
  session was assuming a concrete model such as newest or largest
  address".

Under R6 there is a third wording that sits between them: the address
each allocation takes is one more answer in the record of the outside,
constrained to be fresh. The relation is then a function of that
record, and any allocator satisfies it by supplying its own choices.

`spikes/heap-machine/` writes the relation with the A-fresh rule for a
small language of its own, and keeps a counter in the function that
derives it (08). The function needed one invariant for that, "every
address in use is below the counter", of about 30 lines. For that
language the spike proves that runs are deterministic once the
addresses chosen are fixed, that a block keeps its address and no
address is taken twice, and that a run with one choice of addresses
gives a run with any other one-to-one choice. The last took 413 lines
against 160 of relations, and is proved for two heaps of one shape
only (`evidence/S2-heap-machine.md`, sections 0 and 6).

## 2.5 Extern types and functions

§42, lines 1941 to 1946: an extern declaration "is then a *model*. For
a type, its constructors and `Matchable` say what its values are and
how they are taken apart, and the FFI supplies the representation
together with construction and matching over it. For a function, the
body says what it computes, and the FFI supplies an implementation".
Lines 1951 to 1955: "An `extern` implementation must agree with its
model: except through `slot-eq` (§67), running the models instead of
the implementations must give a program the same values, though not
the same cost, and either may crash where the other does not (§31)."
Line 1958: "`--no-extern` runs the models instead".

Options for the specification's run (part of D6):

- **X-models.** The run ignores the `extern` mark and runs the models.
  The relation is closed: nothing about the FFI appears in it. An
  evaluator that also runs the models is certified outright, and is
  slow, since a model `Nat` is unary. An evaluator that runs the
  implementations is certified up to the assumption that each
  implementation agrees with its model, which §42 already makes the
  FFI author's obligation.
- **X-ports.** With implementations on, constructing, matching, and
  calling at an extern type or function are answers from the outside
  under R6. The relation with the models and the relation with the
  implementations are then two instances of one definition, and §42's
  requirement is the statement that relates them.

In either case the FFI is trusted. The difference is whether the
theorem about the shipping compiler, which runs implementations, is
stated about the relation it actually follows (X-ports) or about the
models' relation under an agreement assumption (X-models).

## 2.6 Points of the memory model that DESIGN.md leaves open

Each is a question for the owner in 06.

- **What a function value's word is, and when a closure is
  allocated.** §29, lines 1247 to 1248: "a function's value is its
  compiled code". §32, line 1327: "A function defined by `def-fns` is
  a closure over its scope." §33, lines 1488 to 1489: "The pointer of
  a `delegate`-bodied function is its callee's pointer". `slot-eq`
  can compare two function values, so the relation has to say whether
  running a `def-fns` twice gives one word or two.
- **Whether separately built equal blocks may share an address.** §36,
  lines 1697 to 1698, says they "are `is`-equal and are two blocks".
  An implementation that shared equal immutable blocks would answer
  `ESome` where the relation says the words differ.
- **Which words are "unspecified".** §33, line 1475, leaves a value
  with no non-erased field "an unspecified word" outside two listed
  cases. `slot-eq` can observe it.
- **The words of `Nat`, `Char`, and `String`.** §45, lines 2236 to
  2237, leaves how they are held "to the implementation".

## 2.7 What the implementations do, and whether order can be observed

This section reports implementations. It says nothing of what the
language is. The programs are in `spikes/order/`; this session re-ran
each one named here. The full tables, 27 further attempts, and the
code read are in `evidence/A2-reference-run.md`, sections 3 and 4, and
`evidence/A1-slc-anatomy.md`, section 4.

**An accepted program can observe the order of siblings.** Two ways
were found, and neither goes through a value the program computes.

- What is written before a failure. In a function body,
  `(values (say w "A\n") (deep 100000))` prints `A` and then fails
  when the run is given a small `--eval-fuel`; with the two entries
  swapped it prints nothing (`values-say-then-crash.sl`,
  `values-crash-then-say.sl`; the reference and `slc --interpret`
  agree).
- The answer to a request. `Measure` answers with the words allocated
  so far. `(values (measure w) (build 200000 (Nil _)))` prints
  "measured BEFORE the build", and the swapped form "measured AFTER
  the build", with no failure anywhere (`values-measure-first.sl`,
  `values-build-first.sl`; the reference interpreted and compiled, and
  slc interpreted and compiled, all agree).

At compile time the number `gensym` returns shows the order in which
sibling macro calls are expanded (06, G9).

**Through the language's own effects no observation was found.** A2
wrote 27 programs that try to make one sibling see another's in-place
write, through cells, extern arrays, `slot-of`, `share`, `at`,
`coerce`, erased mentions, and `def-unique` closures. Both checkers
refused 22 of them, 13 with "conflicting non-erased uses" of a
`unique` binder. The 3 accepted probes that could have shown an order
printed the same for both orders. This is evidence, and no proof, that
without a failure, and with the answers to requests taken as given,
the order cannot change what a program computes. That property would
rest on `unique` meaning sole reference.

**The order both implementations use in a function body is §15's, on
its first reading.** Within one statement or final form, every head
that is a form and every argument that is not a variable (of a call, a
constructor application, a cell invocation, a `world-do`, or a
primitive) runs first, left to right, inner ones first, the head
before its arguments. Then what remains runs where it stands: the
entries of a `values` left to right, a match's scrutinee, the operand
of `share`, the input of `cell-match`. So in
`(values (say w "A\n") (id-nat (deep 100000)))` the `deep` runs before
the `say`: nothing is printed before the failure
(`values-nested-argument.sl`, both implementations). Neither
implementation follows the handoff's proposal A in a body.

**In run position the order is different.** Each sub-form runs when
the elaborator reaches it, left to right and inner first, and nothing
is moved out: an entry of a top-level `values` finishes before the
next begins (A1, section 4.3; A2, section 3.3). So one form runs in
one order inside a function body and in another at the top level, in
both implementations.

**The two implementations disagree on the operands of cell forms.** In
a body, slc moves the input of a `cell-write`, and the items of a
`cell-write` or `cell-alloc`, out before the enclosing statement; the
reference runs them in place. `cell-write-operand.sl`, whose `start`
holds
`(values (measure w) (cell-write unique (build-cell 200000) (MkS1 _)))`,
prints "measured BEFORE the build" under the reference, interpreted
and compiled, and "measured AFTER the build" under slc, interpreted
and compiled. No failure is involved. DESIGN.md does not say which is
right.

**slc's emitted OCaml does not lean on OCaml's own order** in the
cases tried: the elaborator has already bound every argument that is a
call with a `let`, so no emitted application has a call as an argument
(A1, section 4.2).

**Words.** In the reference a constructed value is an OCaml block with
a mutable array of fields; a `cell-write` or an invocation at `unique`
assigns in place, the `many` forms copy, and `slot-eq` is OCaml's
physical equality (A2, section 4.3). The answers of `slot-eq` on equal
numbers computed separately differ between the interpreters, which
answer `ENone`, and the compiled programs, which answer `ESome`
(`evidence/S2-heap-machine.md`, section 8), as §67 allows.

## 2.8 What this means for decision D4

The options of 2.3, restated against these facts:

- **O-α** is what both implementations do in function bodies today,
  apart from their disagreement on cell forms. Choosing it leaves two
  further choices: which of the two is right for cell forms, and
  whether run position is to follow the same rule, which it does not
  today.
- **O-β** is what both implementations do in run position today, and
  what neither does in a body. Choosing it gives one rule for both
  positions, and changes §15's sentence and both implementations'
  bodies.
- **O-γ** would make the specification allow outputs that differ, as
  the `Measure` programs show.
