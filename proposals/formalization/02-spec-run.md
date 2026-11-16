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

**R3. The relation is big-step: one derivation for the terminating run
of one form.** Every function terminates, on the owner's assertion, so
a run of a function body has a finite derivation. The one unbounded
thing, the driver's loop over a `Program` (§42), is a sequence of such
runs with requests between them. A machine that takes one step at a
time (04) is then an implementation, proved to agree with the relation
in both directions. The alternative is to make a small-step machine
with an explicit stack the specification itself. Then the agreement
of the step machine is immediate, and claims about frames can be
stated: `lean/TAIL.md`, lines 23 to 26, notes that a big-step run "has
no stack, so [...] 'this call reuses its caller's frame' cannot be
stated". DESIGN.md's `tail` claim is judged on the code (§19), not on
a run, so the big-step relation loses nothing DESIGN.md states. (D3)

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

**R7. An impossible path has no rule.** Post-erasure code has no code
for a refuted constructor or an absurd branch. The relation derives
nothing for a run that would take one (01, 1.5). (D3)

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

What follows, on this session's reading:

1. A form's sub-forms run before the form does.
2. An argument that is not a variable is bound before the statement
   or final form that contains its call. So in a final form
   `(values (f x) (g (h y)))`, `(h y)` is bound before the whole
   `values`, and so before `(f x)`. A rule of strict left-to-right
   nesting would run `(f x)` first. The handoff's proposal A is that
   strict rule, and it notes that "§15's wording might need to
   follow".
3. In run position the order among siblings is the order of
   elaboration, since each form runs when it has been elaborated and
   before the code after it is checked; the text gives that order as
   head first (§6) and arguments in telescope order (§50). This is an
   inference from three sentences. No sentence says "left to right".

What the text does not fix, as far as this session and
`evidence/A5-design-audit.md` found:

a. inside a function body, the order of two argument temporaries of
   one statement or final form, as in `(f (g a) (h b))`;
b. inside a function body, the order of the entries of one `values`,
   and of the items of one `cell-write` or `cell-alloc`;
c. whether a function body runs in the order that run position has;
d. whether §15's binding covers a head and a scrutinee, as §29 says in
   passing.

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

`spikes/heap-machine/` writes the relation both ways for a small
language (08).

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

To be filled from `evidence/A1-slc-anatomy.md` and
`evidence/A2-reference-run.md`.
