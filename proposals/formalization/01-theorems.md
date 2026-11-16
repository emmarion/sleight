# 01. What can be proved, and how it would be stated

A Claude session's analysis and proposals, written overnight at the
owner's request. Nothing here is approved, and DESIGN.md is unchanged.
Claims about DESIGN.md quote it with section and line numbers. An
argument marked "session's argument" was checked by reviewer agents,
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

So the theorems wanted are agreement theorems. The specification is
given: relations, written in Sleight, that say what it means for a
source to elaborate and for code to run. The theorems say that the
compiler's answers are in those relations. No theorem says the
relations are sound.

"Parameterized", in the sentence attributed to the owner, can be read
two ways, and this session cannot tell which is meant: (a) the
semantics and the syntax are written down as the fixed objects the
theorems refer to; (b) the theorems are generic in parts of the
semantics, taking them as parameters. The proposals work under either.
02 describes a use for reading (b). Decision D12 asks.

## 1.2 A limit that shapes the rest: no total, fuel-free `compile`

Session's argument. It is the usual diagonal argument, which the
handoff's item 1 alludes to. Suppose there were a Sleight function
`compile` from source text to a verdict that takes no fuel and no
hypothesis, and is correct: for an accepted source it returns the
values of the source's run-position forms. Every Sleight function is
total, on the owner's assertion that the termination check is sound.
DESIGN.md §27 runs every run-position form at compile time (lines 1179
to 1180: "Such a form runs as soon as it has been elaborated, before
the code after it is checked"), so any closed call `(p n)` can be put
in run position and its value read out of the verdict. `compile` would
then give a total evaluator for every accepted program. Let `d n` be
one more than the value `compile` finds for "the program whose source
is text number `n`, applied to `n`", and 0 where that text is not an
accepted program of the right type. If the compiler handles the whole
language, its own source included, `d` is itself an accepted program,
with a source of some number `k`, and `d k` is one more than `d k`. So
no such `compile` exists.

This rules out one reading of "every program's source code is either
accepted or rejected": the type of a function that takes only the
source. Three statements remain possible, and they can be held
together:

- **(a) Certified on exit.** The compiler is a loop that the driver
  runs (DESIGN.md §42, lines 1993 to 1994: "It never recurses, so an
  unbounded interaction is the driver's loop over total functions").
  Each step is a total function. When the loop exits, the exit is
  "accepted, with an erased derivation" or "rejected, with an erased
  derivation", and there is no third exit. Nothing is claimed about a
  loop that never exits.
- **(b) A budget that is part of the language.** If DESIGN.md said that
  a compile-time run of more than some number of steps is an error, as
  §62 says of macro expansions (lines 2752 to 2753: "At most 10000
  expansions run in one run"), then running out would be a rejection
  with a derivation like any other, `compile` would be a total
  function, and the theorem would have no hypothesis. The cost is a
  rule that refuses a program because its compile-time run is long.
- **(c) Under a hypothesis.** A function that also takes, erased, a
  derivation that the specification's relation holds of the source can
  recurse on that derivation, so it needs no fuel and is total.
  Nothing can supply the derivation for an arbitrary source, so this
  is a theorem about the algorithm and not a way to run it. It is the
  handoff's result (ii).

Decision D1 is which of these the project states. The handoff's item 2
("A fuel-free self-interpreter is possible because the top level is
not a function") points at (a), and its item 4 at (c). 04 shows that
one step function can serve all three.

## 1.3 The statement idiom: a goal

DESIGN.md §71 gives a unit one goal, a type, discharged by `qed`; line
3134 says "an existential, such as a function with its level, is
packaged by an ADT". `stlc/spec.sl` states strong normalization this
way. The same idiom can state the compiler's theorem: the
specification's files define the relations and set the goal, and the
compiler's own function is the `qed`.

Two toys under `spikes/` check under both implementations with
`--goal proved`. Their language is lists of `Open` and `Close` tokens,
accepted when balanced.

`spikes/verdict/` is statement (b) or (c) in shape: a total decider.

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

The state's type is a parameter of the statement, so the goal does not
fix how the machine is built. `drive.sl` loops `step` under the driver
as a `Program`; that loop is about ten lines and is not covered by the
goal. This statement does not say the machine makes progress: a step
that returned its own state forever would satisfy it. T7 below is the
statement that excludes that.

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
no evidence, reached on malformed shapes
(`evidence/A3-mini-and-precedents.md`, section 2.2, lists 28 groups of
them, the empty program among them). slc has internal-error paths and
an out-of-fuel answer (04). Under T3 each of these becomes a `Fails`
rule, is refuted in the types, or goes away.

**T4, never both.** No source has both derivations. This is a property
of the specification alone; the compiler does not appear in it. It
matters because without it the `Fails` relation is trusted: a `Fails`
rule that is too generous would let a compiler reject a good program
and still satisfy T3. With T4 proved, `Fails` can hold only where
`Accepts` does not, and with T3 it holds exactly there, so only
`Accepts` has to be read with care. T4 needs the elaboration relation
to be deterministic, a proof of its own (mini/README.md lists
"determinism of elaboration" among the metatheory "stated nowhere
yet"). For the full language T4 is false as stated: 06, G1, shows a
compile-time `slot-eq` deciding acceptance, and DESIGN.md §67 lets its
answer "differ between runs". T4 can hold relative to a fixed record
of such answers (02).

**T5, compile-time values are the specification's.** Every value
stored for a run-position form is the result of the specification's
run of that form's code. If the elaboration relation's rule for a
run-position form has the run relation as a premise, T5 is part of T1
and needs no statement of its own.

**T6, the output runs as the specification says.** The emitted
program's run agrees with the specification's run of the elaborated
program. How far this reaches depends on where the proof stops (05).
It can only speak of runs the specification defines: see 1.5.

**T7, the compiler stops when the specification's runs do.** The
handoff's (i) and (ii), in the form this session proposes: the
specification's relation and the compiler's behaviour coincide in both
directions. T1 and T2 are one direction: what the compiler answers,
the relation derives. T7 is the other: if the relation derives a
verdict for a source, the compiler reaches that verdict in finitely
many steps. The handoff's hypothesis H becomes "the relation derives
some verdict for this source", which includes that each compile-time
run it mentions halts, since a derivation is finite. T7 also answers
the question in the handoff's item 4, whether anything would catch a
naive infinite loop in the compiler's core: with T7 proved, such a
loop contradicts a derivation.

## 1.5 What is not on offer, and why

- **Consistency, `no_false`.** Not expected (handoff item 1).
- **Every accepted program's run halts.** If Sleight proved this of
  its own specification, the function of 1.2 (c) would have its
  derivation supplied and would be the total evaluator that 1.2 rules
  out. Session's argument.
- **An accepted program's run never reaches an impossible path.** The
  stripped code of an accepted program can lack code for a branch:
  DESIGN.md §21 allows a constructor with no branch when it is refuted
  (lines 925 to 926: "A constructor with no branch must either be
  refuted or be covered by the `else`"), and an absurd-by-proof
  branch's body is an erased position (§14, lines 558 to 559). That a
  run never takes such a path rests on the erased proof that refuted
  it being real. Session's argument: from a closed erased term of type
  `(False)` one can write an accepted program whose run takes an
  absurd-by-proof branch, so a proof that no accepted run reaches such
  a branch would give `no_false`. The run relation therefore has no
  rule for such a path, and T6 speaks only of runs the relation
  derives.
- **`unique` means sole reference.** The handoff records, as the
  previous session's claim, that the project would not itself prove
  this. A run relation that is a mutating heap machine does not assume
  it: it writes the block whatever else points to it.
- **Stripping changes nothing.** There is no unstripped run to compare
  with: DESIGN.md describes the run on code with the erased positions
  removed (§27, lines 1180 to 1182: "it is elaborated, its erased
  positions are stripped, the evaluator runs the code"; §29, lines
  1299 to 1300: "The elaborator checks the form and produces code with
  the erased positions removed. The evaluator runs that code.").

## 1.6 What stays trusted

- The checker that checks the proofs: the reference implementation,
  and slc when it checks itself. A bug in slc's own checker could
  accept a wrong proof about slc. Having both implementations check
  the same proofs is the mitigation available today.
- The logic's consistency.
- That the specification's relations say what DESIGN.md means. The
  owner reading them is the check. MINIMAL.md's decision that in the
  relations "readability and simplicity outrank everything else"
  serves this.
- `Fails`, unless T4 is proved.
- Whatever lies beyond the point where the proof stops (05): the
  printer to OCaml, the OCaml compiler, the FFI implementations of the
  extern types and functions, whose agreement with their models
  DESIGN.md §42 requires (lines 1951 to 1955), and the driver.
