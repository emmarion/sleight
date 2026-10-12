# lean/: the minimal language in Lean 4, with a soundness proof

A Lean 4 prototype of a fragment of the minimal language of MINIMAL.md:
a reader and elaborator from the surface syntax of `mini/README.md` to a
core language, a checker, an evaluator, and machine-checked theorems
connecting the two. Everything here is the work of Claude sessions at
the owner's request; the shapes they chose are listed at the end for the
owner to confirm or change. A claim in this file that the Lean files do
not check is a claim of those sessions, and may be mistaken.

## Build and run

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
cd lean
lake build                      # the library and every proof
lake build minimal              # the command-line runner
.lake/build/bin/minimal examples/map.sl
.lake/build/bin/minimal --unchecked examples/paradox_knot_bad.sl
./test.sh                       # examples against examples/expected.txt, then the axioms
```

`minimal` checks a program and runs it, or prints why it is refused.
`--unchecked` skips the checker and runs the program anyway.
`--stripped` checks it and runs it with erased code skipped (`runS`),
printing what was skipped as `_`.

## Files

- `Minimal/Syntax.lean`: terms (`Tm`, the type grammar of DESIGN.md
  section 9 with values and closures added), core programs (`Core`).
- `Minimal/Eval.lean`: the evaluator.
- `Minimal/Strip.lean`: the stripped run, which skips erased code, as a
  relation, and `Real`, what it is for a stripped value to stand for a
  value of the full run.
- `Minimal/Unify.lean`: forced unification.
- `Minimal/Typing.lean`: the typing relations.
- `Minimal/Check.lean`: the checker. Each of its functions returns a
  typing derivation, so the checker needs no correctness proof of its
  own.
- `Minimal/Lemmas.lean`, `Minimal/UnifySound.lean`, `Minimal/Sound.lean`:
  the proofs.
- `Minimal/Reader.lean`: the reader and the elaborator to `Core`.
- `examples/`: programs, with their expected output in
  `examples/expected.txt`.

## What is proved

`lake build` checks every theorem; `Axioms.lean` prints the axioms
each one rests on, which are Lean's own three (`propext`,
`Classical.choice`, `Quot.sound`) and no `sorry`.

- **`eval` is total, with no fuel.** It is a Lean definition by
  well-founded recursion, not `partial`, so Lean's kernel has checked
  that it ends on every input, checked or not. Each call compares the
  callee's measure with the caller's: the level, a number taken from a
  counter that grows with every `def-lvl` run, then the sizes of the
  `subterm`-marked arguments, lexicographically over as many places as
  the program's largest number of `subterm` parameters (SOUNDNESS.md
  part 5). A call that does not go down is stuck; so is a match that
  reaches a branch the program does not list. Erased code runs, as in
  SOUNDNESS.md part 3's full semantics: a proof is a token, and a level
  is a number.
- **`checked_runs`.** If `Checked P R` (what `checkProg` returns), then
  `eval` on `P` returns values of the types `R`. So a checked program is
  never stuck: no call fails the decrease check, and no refuted branch
  is reached. And the stripped run of `P` ends too, in values that
  stand for those (`Real`), wherever `R` is not erased.
- **The stripped run (SOUNDNESS.md's (E)).** `RunS` runs a program with
  every erased call and erased match skipped, its results replaced by a
  token, erased `let`s of terms and levels held as tokens, and no
  decrease check. A stripped value stands for a full one (`Real`) when
  it is built by the same constructor, which is not phantom, with its non-erased fields
  standing for theirs, or is the same function closed over an
  environment whose non-erased entries stand for theirs; any value
  stands for a type, a level or a proof. `eval_sound` carries, beside
  the full run's typing, that outside erased code a stripped run from an
  environment whose non-erased entries stand for the full one's exists
  and ends in values standing for the full results. So the stripped run
  never reaches a match or a call on something it skipped, which is the
  sense in which erasure is safe here. `RunS.det` says a stripped run
  has one outcome, and `runS_sound` that the executable `runS`, which
  `--stripped` uses, finds only stripped runs.
- **`no_false`.** No checked program has as its result type a data type
  with no constructors.

The proof is a syntactic, environment-based one. `VTy` says what it is
for a value to have a type. It is defined by recursion on values, not on
types, so neither `Type : Type` nor a type whose constructor takes a
function out of the type itself gets in the way. This is a session's
reading of why the proof goes through, not something the Lean files
state. SOUNDNESS.md's invariants appear as:

- (I1): the environment satisfies every rule the checker has minted
  (`Sat`, part of `EnvOK`).
- (I2) and (I3): `VTy` reads a `Subterm` proof as strict subtree, and a
  `Predates` proof as an order on level numbers.
- The lexical-order lemma: `Chrono`.

## Untrusted

- The reader and the elaborator, from surface syntax to `Core`. The
  theorems are about `Core` programs.
- That `Core`, `TmTy`, `CoreTy` and `eval` match MINIMAL.md. That
  agreement rests on reading alone, and the differences below are the
  ones known.

## Differences from MINIMAL.md

1. A `def-adts` signature may mention a top-level entry only when the
   elaborator knows its type from the text: a level, a function a
   `def-fns` defines, or a `let` binder written with a type; or when the
   entry is a `let` of a term, which is put in its place. Any other
   entry is refused.
2. The type of the program's final expression may not mention the
   program's own entries, once canonicalized.

## Beyond MINIMAL.md

- Multiplicities (DESIGN.md sections 13 and 14), `erased` and `many`,
  written as in the full language on telescope entries, `let` binders,
  a `match`'s mode and a `def-fns` function. A binder written without
  one is `many`, so MINIMAL.md's programs mean what they meant. A
  non-erased position may not mention an erased entry: the callee and
  the arguments for non-erased parameters of a non-erased call, the
  scrutinee of a non-erased match, a non-erased result, a non-erased
  `let` binder; a field of a constructor is a non-erased position
  exactly when the field is. A call whose binders are all erased, an
  `erased` match and the body of an `erased` function are erased
  throughout. A constructor declared `erased` is phantom (DESIGN.md
  section 21): only an erased position may build or hold it, and its
  branch under a non-erased match is erased throughout. What this omits
  from the full language: `unique` and erasure by kind, so a type, a
  level or a proof may be held at `many`. A call nested in an argument
  is erased when the parameter or field it stands for is, which the
  elaborator knows for a function a `def-fns` in scope names and for a
  constructor named directly; elsewhere it is elaborated at `many`, so
  one whose parameter is erased must be bound by an erased `let` first.
  What the rules buy at run time is the stripped run's
  theorem, under "What is proved".
- `absurd` (DESIGN.md sections 21 and 25): a function marked `absurd`,
  and a branch `(absurd (C f ...) body ...)`, whose body is erased and
  ends in one value of a data type with no constructors; and
  `(absurd C)`, which lists a constructor that must be refuted.
  Refuting the facts in force in place of that value (section 51) is
  not supported. An absurd body never returns in a checked program,
  since nothing has a type with no constructors.
- `else` branches (DESIGN.md section 21): an `else` stands for every
  constructor neither listed nor refuted, binds nothing, is checked with
  no forced facts, and is an error when it stands for no constructor.
- `_` as a `def-fns` level (DESIGN.md section 46).
- A call in a body with no decrease annotation, or with `(predates _)`
  or `(subterm _)` written anywhere in it (section 48): the checker
  supplies a `predates` proof when the callee's level does not
  canonicalize to the current one, which needs the callee's level to
  canonicalize to an entry made before the current level, and otherwise
  a `subterm` proof for the first `subterm` argument that differs from
  its counterpart, which needs it to be a strict subtree of the
  counterpart after canonicalization. A same-level call whose `subterm`
  arguments are all unchanged is refused. Where a `_` is written does
  not matter here, where section 48 reads `(subterm _)` before its
  argument.
- `(level-of f)` (section 53), in a term and as an argument of
  `prove-predates`, for an `f` that a `def-fns` in scope names, directly
  or through `let` binders forwarding from one. The elaborator does not
  know types, so `level-of` of a parameter is refused.

## Shapes chosen here, for the owner to confirm or change

- An `is` entry of a telescope, `(e is x)`, opens to an entry with the
  rule that it is `e`, and is typed through that rule, so its type is
  `e`'s (DESIGN.md section 12). An argument or a result supplied for it
  must canonicalize to `e`. In the core such an entry has no type of its
  own: its recorded type is a marker (`Tm.nil`) that the checker reads
  as "the type of its rule" and that every value has.
- The top-level entries a `def-adts` block's signatures mention become
  leading `erased` parameters of each of its types and constructors,
  which the elaborator supplies at every use and binds, unnamed, in every
  pattern; the printer leaves them out. The core's types stay closed, so
  the proofs need nothing new. `def-adts` blocks are elaborated in the
  order they are written.
- An application `(x args)` of a variable is a constructor application,
  a term, exactly when `x`'s type is written as a `TyCtor` or `ValCtor`
  where `x` is bound, or `x` is a `let` binder of a constructor named
  directly; otherwise it is a call. A constructor value reached any
  other way, a call's result say, is applied after a `let` binder
  written with its type. A type or constructor whose `def-adts`
  mentions top-level entries is not first class. A `ValCtor`'s return
  must be an application of a type constructor that is not one of its
  own fields (ASSUMPTIONS.md 80). In the core every
  application is one former, `Tm.app`, whose head is a declared type
  constructor, a declared value constructor or a variable, and is typed
  through its head's type; a value of a `ValCtor` type is a declared
  constructor with exactly that signature, and one of a `TyCtor` type a
  declared type constructor.
- A constructor is marked phantom by writing `erased` before its name
  in `def-adts`, `(erased C (fields) ret)`, as a binder's multiplicity is
  written in this syntax; `many` there is the default.
- A `let` binder written `(T x)` or `(e is x)` is checked, after
  canonicalization, against the type or the term written, and adds no
  rule of its own.
- A `let` binder forwards from its right-hand side, as DESIGN.md
  section 19 has it: a binder of a variable is that variable's entry,
  and a binder of any other term of the type grammar is a new entry
  with the `is` rule that it is the term.
- A branch forces two equations: the scrutinee equals the constructor
  applied to the branch's field entries, and the scrutinee's type equals
  the constructor's return type.
- Unification decomposes every node of the same shape, binders included.
  A variable equated with a term that mentions a binder contradicts, as
  DESIGN.md section 7's third case has it; the proof rests on no value
  mentioning a binder it is not under. When it can neither assign nor
  refute, the program is refused.
- A call's `Fn` telescope and a match's return telescope must be written
  out entry by entry, not reached through a variable (`Tm.isTele`).
  Without this check the proof did not go through: a telescope held in a
  variable can have more entries at run time than the checker counted.
- A match's branches are keyed by constructor. A listed branch whose
  unification contradicts is an error (SPEC-REVIEW 7, as MINIMAL.md
  records). An unlisted constructor must be refuted or covered by an
  `else`.
- The runtime check compares sizes of values where SOUNDNESS.md uses the
  strict-subtree order. The proof uses only that a strict subtree is
  smaller.
