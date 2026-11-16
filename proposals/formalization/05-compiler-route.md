# 05. The compiler: which route, and where the proof stops

A Claude session's analysis and proposals, written overnight at the
owner's request. Nothing here is approved, and DESIGN.md is unchanged.
Facts about slc come from `evidence/A1-slc-anatomy.md` and
`evidence/A7-emission.md`.

## 5.1 The routes

The handoff's goal 2: "change the self-hosted compiler (slc, in
self/), or write a new one, so that it handles Sleight and proves its
correctness". Its section C lists three routes. A fourth combines two
of them.

**C1. Retrofit slc.** Each of slc's functions comes to return, with
its result, an erased derivation of the specification's relation.
Where slc's data structures differ from the relation's (a trie where
the relation has a list, a cache of opened objects, a store with its
own addresses), an erased invariant says which abstract value the
structure stands for. slc keeps its speed: it compiles its own 18,652
lines in about 5 s here; the reference took 97 s to check the same
files, in one run on a machine other agents were using (A1, section
7).

What A1 found slc to prove today (its section 5): termination of
canonicalization and unification; invariants of representation (the
fact table's trie agrees with its rule list, a store reference never
dangles, code is well scoped, and the interpreter returns as many
values as its code's index says); and, for the map and list library
only, results stated against separately defined relations (`MapsTo`
and `Absent`, `Nth`, `Length`, `Concat`). No typing relation, run
relation, or canonical-form relation appears in `self/`. The type of
`canon` does not say its result is the canonical form of its
argument; the type of `unify` does not say which facts were added.
The elaborator's functions record an error in the environment and go
on with placeholders, and the environment hides the fact table's
indices. So under C1 the result type of nearly every function of the
elaborator's main block (95 functions, 3077 lines) changes, and what
a derivation is after the first recorded error has to be decided.

**C2. A certified kernel behind slc's front end.** slc elaborates as
it does today and hands a fully explicit core program to a small
certified checker. This certifies that what runs is well typed. It
does not certify that the core is what the source means, since macro
expansion, sugar, and inference stay outside the proof, and it says
nothing when slc rejects. So it does not give the handoff's item 3,
"every program's source code is either accepted or rejected", as a
theorem about source text. 07 reports the same of the precedents: a
kernel that re-checks an untrusted front end certifies accepted
programs only.

**C3. A new compiler grown from the specification.** `mini/` already
has this shape for its fragment: every function returns its
derivation, so agreement holds by construction, and the algorithms are
the simplest that work. The new compiler grows stage by stage with the
specification (09). slc stays the fast, uncertified compiler until the
new one covers the language. The risks are speed, since the simplest
algorithms may be too slow on large programs, and the time during
which there are two compilers.

**C4. C3, taking from slc what already carries proofs.** slc's reader,
its canonicalization and unification with their termination proofs,
its evidence-returning maps, and its emitter can be reused where their
types can be made to state the relation. This is C3 with a head start
on speed, not a fifth design.

What separates C1 from C3 and C4 is which way the work runs. C1 starts
from code and fits relations to it. C3 starts from relations, which
have to be written first under every route, and writes code to them.
Under C1 the relations risk being written to match slc, which would
copy slc's reading of DESIGN.md into the specification, where the
purpose is to check that reading.

## 5.2 Where the proof stops on the output side

slc's output is OCaml source. The handoff's section C gives two
options; the first below is a third.

**P1. Stop at post-erasure code and the store.** The theorem covers
elaboration and every compile-time run, and it says what the program
is: its post-erasure code and the heap its compile-time runs left
(02). Everything in the emitter is trusted. One mode of the compiler
is then certified to the end: `slc --interpret` runs the program on
the compiler's own evaluator, which under 04 is the certified step
machine. The emitted OCaml is tested against that mode, test by test,
as `self/bootstrap.sh` already compares the two.

**P2. Stop at a lower language, printed by a printer that decides
nothing.** A certified pass makes the emitter's decisions
(representation, control, order, static data) and produces a small
language close to OCaml; the printer only prints. Trusted: the
printer, and that OCaml gives the printed text the lower language's
meaning.

**P3. Stop at a modelled subset of OCaml.** As P2, with the lower
language being OCaml's own syntax and a semantics for the subset
written in Sleight. 07 notes that OCaml has no formal specification
and that the one verified extraction to OCaml stops at Malfunction for
that reason.

P1 is the least work and leaves the most trusted. The closer the
specification's run is to the machine (02: words, blocks, tags, the
representation of §33), the less the emitter has left to decide, and
so the smaller the step from P1 to P2.

## 5.3 `native-compute`

DESIGN.md §72 has the compiler run compiled code at compile time and
store what it returns. §29, lines 1307 to 1309: "A stored value that
`native-compute` produced relies on its compiled run in the same
way". Under P1 the emitted code is outside the proof, so a value that
came from a native run cannot carry a derivation of the run relation.
The proposal of 02, R6, covers this: the result of a native run is an
answer from the outside. A verdict for a program that uses
`native-compute` is then certified relative to those answers.
`bb/` and `fourcolor/` depend on `native-compute` for their checks.
