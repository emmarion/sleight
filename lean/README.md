# lean/: the minimal language in Lean 4, with a soundness proof

A Lean 4 prototype of a fragment of the minimal language of MINIMAL.md:
a reader and elaborator from the surface syntax of `mini/README.md` to a
core language, a checker, an evaluator, and machine-checked theorems
connecting the two. Everything here is one session's work, done at the
owner's request; the shapes it chose are listed at the end for the owner
to confirm or change. A claim in this file that the Lean files do not
check is a claim of that session, and may be mistaken.

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

## Files

- `Minimal/Syntax.lean`: terms (`Tm`, the type grammar of DESIGN.md
  section 9 with values and closures added), core programs (`Core`).
- `Minimal/Eval.lean`: the evaluator.
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
  is reached.
- **`no_false`.** No checked program has as its result type a data type
  with no constructors.

The proof is a syntactic, environment-based one. `VTy` says what it is
for a value to have a type. It is defined by recursion on values, not on
types, so neither `Type : Type` nor a type whose constructor takes a
function out of the type itself gets in the way. This is the session's
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
  ones this session knows of.

## Differences from MINIMAL.md

1. A `def-adts` signature may not mention any entry, a top-level level
   included: it may mention only types, its own binders and `Type`.
   `examples/paradox_same_level_bad.sl` therefore carries the level as
   an index, where `tests/paradox_same_level_bad.sl` names a top-level
   level.
2. There are no `is` entries, in telescopes or `let` binders. A `let`
   binder is a bare name.
3. Type constructors and value constructors are applied only by name,
   saturated. The `TyCtor` and `ValCtor` formers are not values.
4. The type of the program's final expression may not mention the
   program's own entries.

## Shapes chosen here, for the owner to confirm or change

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
  records). An unlisted constructor must be refuted.
- The runtime check compares sizes of values where SOUNDNESS.md uses the
  strict-subtree order. The proof uses only that a strict subtree is
  smaller.
