# lean/: the minimal language in Lean 4, with a soundness proof

A Lean 4 prototype of a fragment of the language of DESIGN.md, the
minimal language of MINIMAL.md and the additions listed below: a reader
and elaborator from the full language's surface syntax to a core
language, a checker, an evaluator, and machine-checked theorems
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
./regen.sh                      # rewrite examples/expected.txt from the current runner
```

`minimal` checks a program and runs it, or prints why it is refused.
A value prints as DESIGN.md section 45 has it: a `Nat` of the prelude
as a numeral, an erased field as `_`, and a last argument that is an
application after `$`. A final value that is a function must have no
parameters and one `many` return written with its type; it is applied,
and its result printed (section 27).
`--unchecked` skips the checker and runs the program anyway.
A checked program runs with erased code skipped (the stripped run,
`runS`), which `eval_sound` proves agrees with the full run on what is
not erased; `--full` runs the full evaluator `eval` instead, which also
computes the erased values. `test.sh` compares the two on every
example. Every program starts in the scope of
`prelude.sl`, unless `--no-prelude` is given.

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
- `Minimal/Infer.lean`: inference of `_` arguments, between elaboration
  and checking.
- `prelude.sl`: the prelude, which `prelude.py` makes from
  `lib/prelude.sl`: the forms the runner accepts, in order, with the
  `extern` markers of functions removed, kept only when the full evaluator still finishes on them. `python3 prelude.py ../lib/prelude.sl
  .lake/build/bin/minimal prelude.sl` regenerates it.
- `compare.sh`: runs the runner over the OCaml suite's `tests/` and
  prints, per test, the verdict the test expects and the runner's.
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
  the runner uses, finds only stripped runs.
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

## Syntax

Programs are written in the full language's syntax (DESIGN.md sections
1 to 3, 11, 21 and 26), with `$` and comments. Each multiplicity the
full language requires is required. These forms are refused as not
supported: `unique`; `extern` functions (an `extern` type is an
ordinary type that records the mark, and only the prelude, or a program
run with `--no-prelude`, may write it); `_` in place of a
type (section 50); `delegate`; and every form
not named in this file,
among them `coerce`, character and string literals, `numeral-of`,
`prove-literal-lt`, `unary`, macros, pragmas, cells and
`at`. A file's top level has size one, or ends in a statement and
produces nothing (section 27).

## Differences from MINIMAL.md

1. A `def-adts` signature may mention an entry only when the elaborator
   knows its type from the text: a level, a function a `def-fns`
   defines, a function's parameter, a result of a call to such a
   function, or a `let` binder written with a type; or when the entry is a `let` of a term or an `is` parameter,
   which is put in its place. Any other entry is refused.

## Beyond MINIMAL.md

- Multiplicities (DESIGN.md sections 13 and 14), `erased` and `many`,
  on telescope entries, `let` binders, a `match`'s mode, a `def-fns`
  function and a `def-adts` constructor. A non-erased position may not mention an erased entry: the callee and
  the arguments for non-erased parameters of a non-erased call, the
  scrutinee of a non-erased match, a non-erased result, a non-erased
  `let` binder; a field of a constructor is a non-erased position
  exactly when the field is. A call whose binders are all erased, an
  `erased` match and the body of an `erased` function are erased
  throughout. A constructor declared `erased` is phantom (DESIGN.md
  section 21): only an erased position may build or hold it, and its
  branch under a non-erased match is erased throughout. What this omits
  from the full language: `unique`. An `erased` match whose results
  are not all erased is elaborated to `seq R (case ...) rest`, a match
  with one real branch that the stripped run takes without looking at
  the scrutinee; one whose results are all erased is erased throughout. A type, a type constructor, a level and a proof are erased by
  their kind (section 14): `def-lvl`, the proof forms and every type
  former make erased entries, and a type is not a non-erased value. A call nested in an argument
  is erased when the parameter or field it stands for is, which the
  elaborator knows for a function a `def-fns` in scope names and for a
  constructor named directly; elsewhere it is elaborated at `many`, so
  one whose parameter is erased must be bound by an erased `let` first.
  What the rules buy at run time is the stripped run's
  theorem, under "What is proved".
- `absurd` (DESIGN.md sections 21 and 25): a function marked `absurd`,
  and a branch `(absurd (C f ...) body ...)`, whose body is erased and
  ends by refuting the facts in force (section 51): with a `match`
  annotated `_` whose branches all refute, or with any other expression,
  whose every constructor must be refuted, one match deep; a value of a
  type with no constructors is the case where there are none. And
  `(absurd C)`, which lists a constructor that must be refuted.
  In the core a refutation is a `case` with no branch that returns, or
  a failing open (`open-absurd`, below) (`Core.noRet`), so an absurd
  body never returns in a checked program.
- `let-match` (sections 27 and 52), with or without further branches,
  elaborated to the core's `case`: a match without an annotation or a
  continuation of its own, whose branches each end the enclosing code.
  The pattern's branch holds everything after the `let-match`. Under an
  erased scrutinee a `case` has at most one real branch, whose fields
  are erased, and the stripped run takes it without looking at the
  scrutinee. A second real branch is refused outside a function or
  branch body.
- `_` as an inferred argument (section 50). `Minimal/Infer.lean` fills
  each `_` before checking: the `_`s of a call, a result or a `let`'s
  term, nested constructor applications included, become fresh
  entries, solved by first-order unification of the arguments' types
  with the parameters' and of the term's type with what the position
  expects. An unsolved `_` is an error. The checker then checks the
  program as filled in, so the inference is not trusted.
- Numerals (section 45), up to 100000. Each numeral of a program is one entry, made
  at the top level before the first form that mentions it: a `Nat` of
  the prelude, the numeral's `Succ`s at run time, with no rule, so the
  checker sees it as opaque. Its `Numeral` proof is not made.
- A result of the program whose type mentions the program's own entries
  is checked as a result of any type (`ArgsTy.anyCons`), so
  `checked_runs` says nothing of its type.
- `Matchable` types and `(matchable-of T)` for a declared type
  (section 24). A `Matchable`'s type names a declared type, its tag,
  marks and constructors in order (`VTy.mtbl`); its value is a token.
- `(open-adt m e)` (section 8): an anonymous `let` of `e` at `m`, then
  the open of that binder, which lasts as the binder's scope does. A
  match whose scrutinee's type is headed by a type constructor that an
  opened `Matchable` names takes its constructors, their order and their
  phantom marks from that `Matchable`, and each constructor's signature
  from its `ValCtor` type (`Shape`); a pattern names a constructor of an
  opened `Matchable` or a declared one. A match that dispatches at run
  time needs the `Matchable` opened at `many` and its entry non-erased.
  An open requires the listed constructors to be pairwise distinct
  after canonicalization, and unifies the opened `Matchable` with every
  `Matchable` that names its type constructor or one of its
  constructors, a declared type's included; a contradiction is an error
  (section 8's invariant). `(open-absurd e ann)` takes `e` at `erased`
  and requires its open to fail, by a constructor listed twice or a
  contradiction; it is then of any size, and in the core an open
  followed by nothing, which the proof shows is never reached.
- `union` and `newtype` (section 21). A `newtype` must have newtype
  shape. A non-erased match on a union may have one real branch, outside
  erased code; at run time the core keeps the constructor anyway, so the
  rule is the elaborator's alone. A union value with more than one
  non-phantom constructor prints as `_`.
- `tail` and `notail` (section 19): the call must, or must not, be in
  tail position: the final expression of a function body, of a branch of
  a match in tail position, or of a `let`'s right-hand side when the
  rest of the body returns its binders in order, after `let`s whose
  binders are all erased. Neither is accepted in an erased position.
- `else` branches (DESIGN.md section 21): an `else` stands for every
  constructor neither listed nor refuted, binds nothing, is checked with
  no forced facts, and is an error when it stands for no constructor.
- `_` as a `def-fns` level (DESIGN.md section 46).
- `_` as a match annotation (section 47) in the final expression of a
  function body, of a branch, and of a `let` whose binders all carry a
  type or `is` clause. In an argument position it is refused.
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
  or through `let` binders forwarding from one, and for a parameter
  written with an `Fn` type whose level is an entry.

## Shapes chosen here, for the owner to confirm or change

- An `is` entry of a telescope, `(m e is x)`, opens to an entry with the
  rule that it is `e`, and is typed through that rule, so its type is
  `e`'s (DESIGN.md section 12). An argument or a result supplied for it
  must canonicalize to `e`. In the core such an entry has no type of its
  own: its recorded type is a marker (`Tm.nil`) that the checker reads
  as "the type of its rule" and that every value has.
- The entries a `def-adts` block's signatures mention become
  leading `erased` parameters of each of its types and constructors,
  which the elaborator supplies at every use and binds, unnamed, in every
  pattern; the printer leaves them out. The core's types stay closed, so
  the proofs need nothing new. `def-adts` blocks are elaborated in the
  order they are written. A block inside a body is declared in the
  program like any other, and its names are in scope to the end of the
  body.
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
- A `let` binder written `(m T x)` or `(m e is x)` is checked, after
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
  When it equates a variable with a variable, a declared type
  constructor or a declared value constructor (`Ctx.atoms`), it
  contradicts if one opened `Matchable` lists the two at different
  positions; otherwise it unifies their signatures when both have one,
  as DESIGN.md section 7 has it for two atoms, and every `Matchable`
  that names either of them, as section 8's invariant has it. The proof
  rests on a value having at most one such signature (`VTy.sig_det`)
  and on every `Matchable` naming a value being its declared type's
  (`Names.uniq`).
  A variable equated with a term that mentions a binder contradicts, as
  DESIGN.md section 7's third case has it; the proof rests on no value
  mentioning a binder it is not under. When it can neither assign nor
  refute, the program is refused.
- A call's `Fn` telescope and a match's return telescope must be written
  out entry by entry, not reached through a variable (`Tm.isTele`).
  Without this check the proof did not go through: a telescope held in a
  variable can have more entries at run time than the checker counted.
- A match's branches are keyed by constructor: in the core, by its
  position among its type's constructors, with the constructor as
  written, which must canonicalize to the one at that position, and its
  field count, which the stripped run needs when it takes the one real
  branch of an erased match without looking. A listed branch whose
  unification contradicts is an error (SPEC-REVIEW 7, as MINIMAL.md
  records). An unlisted constructor must be refuted or covered by an
  `else`.
- The runtime check compares sizes of values where SOUNDNESS.md uses the
  strict-subtree order. The proof uses only that a strict subtree is
  smaller.
