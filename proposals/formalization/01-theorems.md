# 01. What can be proved, and how it would be stated

A Claude session's analysis and proposals, written overnight at the
owner's request. Nothing here is approved, and DESIGN.md is unchanged.
Claims about DESIGN.md quote it with section and line numbers. An
argument marked "session's argument" was checked by a reviewer agent,
not by a machine.

## 1.1 The starting point

The handoff from the previous session reports the following as the
owner's. The handoff is second-hand, and its own words are quoted.

- Its item 1: "No `no_false` theorem is expected: for consistency,
  proving properties about the language runs into a diagonalization
  argument." What is wanted instead, in words the handoff attributes to
  the owner: "we parameterized the semantics of the language, and this,
  or the syntax of the language, or both, and our compiler is proven to
  be in agreement with those."
- Its item 3: "It should be a theorem that every program's source code
  is either accepted or rejected as an error."
- Its item 4, two results the previous session offered: "(i) the
  compiler can only diverge if the spec's own run of some compile-time
  code diverges; (ii) under a hypothesis H that every accepted
  compile-time form's spec run halts, `compile` is a total function to
  accepted-or-rejected." The owner replied "I think I'm in general
  agreement", which the handoff says "is not agreement to exact
  statements".

On this session's reading, the theorems wanted are agreement theorems.
The specification is taken as given, and the theorems say that the
compiler's answers agree with it. No theorem says the specification is
sound. These proposals write the specification as relations in
Sleight: the handoff's goal 1 is "Formalize Sleight in Sleight", and
MINIMAL.md records "Evaluation and typing are relations, not
functions" as decided for the minimal language.

"Parameterized", in the sentence attributed to the owner, can be read
two ways, and this session cannot tell which is meant: (a) the
semantics and the syntax are written down as the fixed objects the
theorems refer to; (b) the theorems are generic in parts of the
semantics, taking them as parameters. The proposals are meant to work
under either. 02 describes a use for reading (b). Decision D12 asks.

## 1.2 A limit that shapes the rest: no total, fuel-free `compile`

Session's argument. It is a diagonal argument of the kind the
handoff's item 1 mentions for `no_false`; the handoff does not apply
it to `compile`.

Suppose there were a Sleight function `compile` from source text to a
verdict, `Accepted` or `Rejected`, that takes no fuel and no
hypothesis, returns on every source, and is right in both directions:
it accepts exactly the sources the specification accepts. DESIGN.md
makes the verdict depend on a compile-time value: a run-position form
"runs as soon as it has been elaborated, before the code after it is
checked" (§27, lines 1179 to 1180), and "`(comptime-match m x (C f1
... fn))` asserts, at elaboration time, that `x` is a `Settled`,
non-erased value headed by `C`. It is an error otherwise" (§28, lines
1208 to 1210). Let `d n` be `(BFalse)` when `compile` accepts "text
number `n`, followed by `(comptime-match many (diag n) (BTrue))`", and
`(BTrue)` when it rejects it. If the compiler handles the whole
language, its own source included, then some text, of number `k`,
defines `compile`, then `d`, and then `diag` as `d`. Take that text
followed by `(comptime-match many (diag k) (BTrue))`. If `compile`
accepts it, the specification's run of `(diag k)` gave `(BTrue)`; but
`d k` is `(BFalse)`. If `compile` rejects it, `d k` is `(BTrue)`, so
the `comptime-match` holds and the specification accepts it. So no
such `compile` exists.

The argument uses three things of `compile`: that the language it
compiles accepts text `k`, its own source with `d` and `diag`; that
its verdict on the one source built from that text is right in both
directions; and that it returns on that source. For
the last: DESIGN.md calls Sleight's functions "total functions" (§42,
line 1994) and says "Termination rests on levels" (§17, line 696), and
README.md, a session's file, records that "The author asserts that
each Sleight function terminates". Without that, the conclusion is
that such a `compile` cannot return on every source.

This rules out one reading of "every program's source code is either
accepted or rejected": a function that takes only the source and
always returns the right verdict. Three statements remain possible,
and they can be held together:

- **(a) Certified on exit.** The compiler is a loop that the driver
  runs (DESIGN.md §42, lines 1993 to 1994: "It never recurses, so an
  unbounded interaction is the driver's loop over total functions").
  Each step is a total function. When the loop exits, the exit is
  "accepted, with an erased derivation" or "rejected, with an erased
  derivation", and there is no third exit. Nothing is claimed about a
  loop that never exits.
- **(b) A budget that is part of the language.** If DESIGN.md bounded
  the steps of a compile-time run, as §62 bounds macro expansions
  (lines 2752 to 2753: "At most 10000 expansions run in one run"), and
  made exceeding the bound an error, then running out would be a
  rejection with a derivation like any other. `compile` would be a
  total function, and the theorem would have no hypothesis, provided
  every other loop in the compiler terminates without a counter of its
  own. That is not established: slc has other counters today (04,
  section 4.5). The cost of (b) is a rule that refuses a program
  because its compile-time run is long.
- **(c) Under a hypothesis.** A function that also takes, erased, a
  derivation of a verdict for the source can recurse on that
  derivation, so it needs no fuel and is total. No Sleight function
  can supply that derivation for every source: given T4 below, the
  function so completed would be the `compile` that the argument above
  rules out. So this is a theorem about the algorithm and not a way to
  run it. It is the handoff's result (ii), restated per source. As a
  type it says only that some total function returns verdicts from
  derivations; what ties it to the compiler's own loop is that the two
  share their step function, or T7 below.

A fourth course keeps a third answer with no derivation, as slc's "out
of fuel" is today. T3 below is the statement that excludes it.

The argument needs one particular source: text `k`, which holds the
compiler, followed by a form whose acceptance depends on a
compile-time run of that compiler. So it does not rule out a total
`compile`, with no fuel and no hypothesis, for a part of the language
that has no such source. One such part is MINIMAL.md's fragment, where
no verdict depends on a run (MINIMAL.md, item 4: "Elaboration is a
pure function from raw syntax to core terms; evaluation is a separate
phase after it"; 09, stage 1). Another might be a part whose
compile-time code cannot express its own compiler, compiled by a
function outside that part. A total `compile` for such a part would
amount to a proof, in Sleight, that all compile-time code of the part
halts, and this session does not know whether Sleight can prove that
for any part worth having. The survey of prior art raises the
possibility in terms of levels ("an evaluator, at some level, for
programs of strictly lower levels") and marks it unknown
(`evidence/A6-prior-art.md`, section 2.5). A level is created by a
`def-lvl` of the program it stands in (§18, lines 728 to 730), so that
wording would first need a measure that compares a source's code with
the compiler's.

Decision D1 is which of these the project states. The handoff's item 2
("A fuel-free self-interpreter is possible because the top level is
not a function") points at (a), and its item 4 at (c). 04 shows, on a
toy language, one step function iterated in all three ways
(`spikes/three-iterations/`).

## 1.3 The statement idiom: a goal

DESIGN.md §71 gives a unit one goal, a type, discharged by `qed`; line
3134 says "an existential, such as a function with its level, is
packaged by an ADT". `stlc/spec.sl` states strong normalization this
way. The same idiom can state the compiler's theorem: the
specification's files define the relations and set the goal, and the
compiler's own function is the `qed`.

Three toys under `spikes/` check under both implementations with
`--goal proved`. Their language is lists of `Open` and `Close` tokens,
accepted when balanced.

`spikes/verdict/` has the result type that (b) and (c) share: a total
decider. Its `decide` takes no derivation and recurses on the source.

```scheme
(def-adts $ (Verdict : ((Nat) depth) ((List (Tok)) src) -> Type)
  enum
  (many Accepted : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Accepts d ts) p) -> (Verdict d ts))
  (many Rejected : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Fails d ts) p) -> (Verdict d ts)))

(def-adts $ (EitherAcceptedOrRejected : -> Type)
  enum
  (many MkEither : (erased (Level) L)
     (many (Fn L (many (Nat) d) (subterm many (List (Tok)) ts) -> (many (Verdict d ts) v)) decide)
     -> (EitherAcceptedOrRejected)))

(def-adts $ (NeverBoth : -> Type)
  enum
  (many MkNeverBoth : (erased (Level) L)
     (erased (Fn L (erased (Nat) d) (erased (List (Tok)) ts) (subterm erased (Accepts d ts) p) (erased (Fails d ts) q) -> (erased (False) f)) exclusive)
     -> (NeverBoth)))
```

`Accepts` and `Fails` are two separately written relations. `decide`
returns one of them with its derivation. `exclusive` says no source
has both.

`spikes/verdict-machine/` is statement (a) in shape: a state machine
whose step is a total function and whose only exit is a verdict.

```scheme
(def-adts $ (Stepped : ((TyCtor ((List (Tok)) src) -> Type) State) ((List (Tok)) src) -> Type)
  enum
  (many More : (erased (TyCtor ((List (Tok)) src) -> Type) State) (erased (List (Tok)) src) (many (State src) next) -> (Stepped State src))
  (many Done : (erased (TyCtor ((List (Tok)) src) -> Type) State) (erased (List (Tok)) src) (many (Verdict (Zero) src) v) -> (Stepped State src)))

(def-adts $ (CertifiedOnExit : -> Type)
  enum
  (many MkCertifiedOnExit : (erased (TyCtor ((List (Tok)) src) -> Type) State) (erased (Level) L)
     (many (Fn L (many (List (Tok)) src) -> (many (State src) s)) start)
     (many (Fn L (erased (List (Tok)) src) (many (State src) s) -> (many (Stepped State src) r)) step)
     -> (CertifiedOnExit)))
```

The state's type is a field of the statement that the proof chooses,
so the goal does not fix how the machine is built. `drive.sl` loops
`step` under the driver as a `Program`; that loop is about ten lines
and is not covered by the goal. This statement does not say the
machine makes progress: a machine whose step returns its own state
forever satisfies it (`spikes/verdict-machine/idle-machine.sl` with
`idle-qed.sl`, written by the reviewer). T7 below is the statement
that excludes that.

`spikes/three-iterations/` adds statement (c) in shape: its `run-by`
recurses on an erased derivation that the machine halts.

## 1.4 The theorems on offer

Each has a name so that the decisions can refer to it.

**T1, accepted means derivable.** When the compiler accepts a source,
an erased derivation of the specification's elaboration relation for
that source exists. The `Accepted` constructor carries it.

**T2, rejected means derivable.** When the compiler rejects, an erased
derivation of a positive `Fails` relation exists. MINIMAL.md records a
positive `Fails` as decided for the minimal language: "A positive
`Fails` relation records why a program is refused, beside the relation
that types it."

**T3, no third answer.** T1 and T2 together as the compiler's type:
its exits are `Accepted` and `Rejected` and nothing else. This is the
part of the handoff's item 3 that needs no hypothesis. It has content.
`mini/`'s top-level function has a third answer, `ProgramStuck`, with
no evidence, reached on shapes its relations have no rule for
(`evidence/A3-mini-and-precedents.md`, section 2.2, lists 28 groups of
them, the empty program among them). slc has internal-error paths and
an out-of-fuel answer (04). Under T3 each of these becomes a `Fails`
rule, is refuted in the types, or goes away. T3 is about the
specification's machine, "with unlimited stack and heap" (§31, lines
1319 to 1320). A real run of the compiler may still crash (lines 1320
to 1321), as both implementations do today on a deep compile-time
recursion: a top-level `let` whose right-hand side recurses three
million deep ends both with a stack overflow (run by this session).
See 06, G7.

**T4, never both.** No source has both derivations. This is a property
of the specification alone; the compiler does not appear in it. It
matters because without it the `Fails` relation is trusted: a `Fails`
rule that is too generous would let a compiler reject a good program
and still satisfy T3. With T4 proved, `Fails` can hold only where
`Accepts` does not, so a `Rejected` exit is never given to a source
that `Accepts` covers; for that purpose only `Accepts` has to be read
with care. T3 and T4 do not say that `Fails` holds everywhere
`Accepts` does not: T3 gives one of the two derivations only for a
source on which the compiler exits. That is every source under (b).
Under (a) and (c) no theorem here says every source has a verdict
derivation. With T4 and the function of (c), a Sleight proof of that
would give the `compile` that 1.2 rules out. A `Fails` relation that
lacks a rule leaves sources with no verdict, and on those the compiler
has no exit.

Proving T4 is expected to need determinism lemmas for the elaboration
relation (A3's inference; mini/README.md lists "determinism of
elaboration" among the metatheory "stated nowhere yet"). The toy's
`exclusive` needed none. If the relation leaves open what DESIGN.md
leaves to the outside, T4 is false as stated: 06, G1, shows a
compile-time `slot-eq` deciding acceptance, and DESIGN.md §67 lets its
answer "differ between runs" (lines 3045 to 3046). 02, R6, proposes a
fixed record of such answers, and T4 would then be stated relative to
it.

**T5, compile-time values are the specification's.** Every value
stored for a run-position form is the result of the specification's
run of that form's code. If the elaboration relation's rule for a
run-position form has the run relation as a premise, T5 is part of T1
and needs no statement of its own. OPEN.md item 4 asks a neighbouring
question, whether a reference evaluator should arbitrate runs that
produce facts.

**T6, the output runs as the specification says.** The emitted
program's run agrees with the specification's run of the elaborated
program. How far this reaches depends on where the proof stops (05).
It can only speak of runs the specification defines: see 1.5.

**T7, the compiler stops when the specification's runs do.** The
handoff's (i) and (ii), in the form this session proposes: the
specification's relation and the compiler's behaviour coincide in both
directions. T1 and T2 are one direction: what the compiler answers,
the relation derives. T7 is the other: if the relation derives a
verdict for a source, relative to the answers the outside gave (02,
R6), the compiler given those answers reaches that verdict in finitely
many steps. T7 implies T4, since a compiler cannot reach two verdicts,
so for the full language it too holds only relative to that record.
The handoff's hypothesis H becomes "the relation derives some verdict
for this source", which includes that each compile-time run it
mentions halts, since a derivation is finite. T7 bears on the question
in the handoff's item 4, whether anything would catch a naive infinite
loop in the compiler's core: with T7 proved, such a loop on a source
that has a derivable verdict contradicts the derivation. A loop on a
source with no derivable verdict is not excluded, and no theorem here
says every source has one. For `mini/`'s evaluator, the machine's
share of T7 is proved in `spikes/step-machine/` in two forms, and not
yet for the plain loop under the driver (04, 4.2).

## 1.5 What is not on offer, and why

- **Consistency, `no_false`.** Not expected (handoff item 1). OPEN.md
  item 1 is the question.
- **Every accepted form's run halts** (the handoff's H). If Sleight
  proved this of its own specification, the derivation that the
  function of 1.2 (c) needs could be built form by form, each
  run-position form being accepted before it runs (§27, lines 1180 to
  1182), provided the rest of elaboration needs no counter (the
  handoff's result (i), which is not proved). `compile` would then be
  total, which is the handoff's result (ii), and, given T4, it would
  be the function that 1.2 rules out. Session's argument. Of a whole
  program the statement is false by design: a `Program` may never exit
  (§42, lines 1993 to 1994).
- **An accepted program's run never reaches an impossible path.** The
  stripped code of an accepted program can lack code for a branch:
  DESIGN.md §21 allows a constructor with no branch when it is refuted
  (lines 925 to 926: "A constructor with no branch must either be
  refuted or be covered by the `else`"), and an absurd-by-proof
  branch's body is an erased position (§14, lines 558 to 559). That a
  run never takes such a path rests on the erased values behind the
  facts that refuted it being real. Session's argument: from a closed
  erased term of type `(False)` one can write an accepted program
  whose run takes an absurd-by-proof branch, so a proof that no
  accepted run reaches such a branch would give `no_false`. (Both
  implementations accept that program with the closed term replaced by
  an erased parameter of an empty type: `spikes/gaps/absurd-branch.sl`.
  With no closed term of such a type at hand, no run that takes the
  branch can be shown.) The
  proposal (02, R7) is that the run relation derives no result for
  such a path; 06, G8, asks the owner. T6 then speaks only of runs the
  relation derives. A compile-time run can reach such a path too,
  since that program can stand in run position. There the compiler
  still needs an exit under T3: either `Fails` has a rule for it, with
  a positive relation saying that the run reached a branch with no
  code, or the compiler does not exit. 02, R7, proposes the first.
- **`unique` means sole reference.** The handoff records, as the
  previous session's claim, that the project would not itself prove
  this. A run relation that is a mutating heap machine does not assume
  it: it writes the block whatever else points to it.
- **Stripping changes nothing.** There is no unstripped run to compare
  with: DESIGN.md describes the run on code with the erased positions
  removed (§27, lines 1180 to 1182: "it is elaborated, its erased
  positions are stripped, the evaluator runs the code"; §29, lines
  1299 to 1300: "The elaborator checks the form and produces code with
  the erased positions removed. The evaluator runs that code."). The
  handoff's item 6 records that the owner's concern about such a run
  "goes away if the heap is mutable", and that the owner has not
  confirmed the previous session's reading. OPEN.md item 2 asks a
  neighbouring question and records it as unverified; these proposals
  do not take it up.

## 1.6 What stays trusted

- The checker that checks the proofs: the reference implementation,
  and slc when it checks itself. A bug in slc's own checker could
  accept a wrong proof about slc. Having both implementations check
  the same proofs is the mitigation available today.
- The logic's consistency.
- That the specification's relations say what DESIGN.md means. The
  owner reading them is the check. MINIMAL.md records as decided, for
  the minimal language's relations and in a session's wording, that
  "readability and simplicity outrank everything else". The same
  priority for the full specification would serve this.
- `Fails`, unless T4 is proved.
- That the machine the compiler runs on has the stack and heap the run
  needs: a real run may crash (§31).
- Whatever lies beyond the point where the proof stops (05): the
  printer to OCaml, the OCaml compiler, the FFI implementations of the
  extern types and functions, whose agreement with their models
  DESIGN.md §42 requires (lines 1951 to 1955), and the driver.
