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
application after `$`. A checked program's results print by their
types, since the stripped run holds a newtype's value as its field;
`--unchecked` prints by value. A final value that is a function must have one
of the two forms of section 27: from no parameters to one `many` return
written with its type, when it is applied and its result printed, or,
with the prelude, from one `many` `(String)` to one `many` `(String)`,
when it is applied to all of standard input and its result written to
standard output.
`--unchecked` skips the checker and runs the program anyway.
`--shared` reads the files named as one program, in order, the final
value of the last being the program's and that of any other being
discarded.
A checked program runs with erased code skipped (the stripped run,
`runS`), which `eval_sound` proves agrees with the full run on what is
not erased; `--full` runs the full evaluator `eval` instead, which also
computes the erased values. `test.sh` compares the two on every
example. Every program starts in the scope of
`prelude.sl`, or of `prelude-full.sl` under `--full` and `--unchecked`,
unless `--no-prelude` is given.

## Files

- `Minimal/Syntax.lean`: terms (`Tm`, the type grammar of DESIGN.md
  section 9 with values and closures added), core programs (`Core`).
- `Minimal/Eval.lean`: the evaluator.
- `Minimal/Strip.lean`: the stripped run, which skips erased code, as a
  relation, and `Real`, what it is for a stripped value to stand for a
  value of the full run.
- `Minimal/Native.lean`: the executable stripped run, the native
  externs it uses and their proofs.
- `WARNINGS.md`: the warnings only this runner emits.
- `Minimal/Unify.lean`: forced unification.
- `Minimal/Typing.lean`: the typing relations.
- `Minimal/Check.lean`: the checker. Each of its functions returns a
  typing derivation, so the checker needs no correctness proof of its
  own.
- `Minimal/Lemmas.lean`, `Minimal/UnifySound.lean`, `Minimal/Sound.lean`,
  `Minimal/Deleg.lean`: the proofs about the full and stripped runs.
- `Minimal/Uses.lean`: the uses pass (section 15's discipline on
  `unique`), which the runner requires of a checked program.
- `Minimal/Machine.lean`, `Minimal/MachineSound.lean`,
  `Minimal/MachineRun.lean`, `Minimal/MachineDeleg.lean`,
  `Minimal/MachineAsm.lean`: the machine run, which writes cells in
  place, and its agreement with the stripped run.
- `Minimal/Run.lean`: the runner's driver and printer.
- `Minimal/Reader.lean`: the reader and the elaborator to `Core`.
- `Minimal/Infer.lean`: inference of `_` arguments, between elaboration
  and checking.
- `prelude.sl`: the prelude, which `prelude.py` makes from
  `lib/prelude.sl`: the forms the runner accepts, in order.
  `prelude-full.sl`: those of them on which the full evaluator still
  finishes, for the runs that use it; `u62-modulus` is `2^62` in unary,
  which only the stripped run leaves uncomputed, so it and everything
  over `U62` are not there. `python3 prelude.py ../lib/prelude.sl
  .lake/build/bin/minimal prelude.sl prelude-full.sl` regenerates both.
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
  decrease check. A stripped call passes its callee only the arguments
  that the caller's view of the callee's type leaves non-erased, in
  order, and the callee spreads them over its own non-erased
  parameters, a token at each erased one; its results come back the
  same way (`FnDef.spreadIn`, `FnDef.spreadOut`). A stripped `def-fns`
  binds a function with a `delegate` body to the stripped value of its
  target, as DESIGN.md section 33 has a delegate's pointer be its
  callee's (`closuresS`). A stripped value stands for a full one
  (`Real`) when it is built by the same constructor, which is not
  phantom, with its non-erased fields standing for theirs, or is the
  same function, one with no `delegate` body, closed over an
  environment whose non-erased entries stand for theirs, or, for the
  closure of a function with a `delegate` body, when it stands for the
  target that closure's environment holds (`Real.dele`); any value
  stands for a type, a level or a proof. `eval_sound` carries, beside
  the full run's typing, that outside erased code a stripped run from an
  environment whose non-erased entries stand for the full one's exists
  and ends in values standing for the full results. So the stripped run
  never reaches a match or a call on something it skipped, which is the
  sense in which erasure is safe here. The stripped run holds a value
  built by a `newtype`'s wrapping constructor as its one non-erased
  field, as DESIGN.md section 33 has it (`Prog.unwrap`), and a stripped
  value stands for such a value when it stands for that field
  (`Real.wrap`). The stripped run holds a value of the declared type
  named `Nat` and marked `extern`, the prelude's, as a number
  (`Tm.nat`, `Prog.natD`): applying its constructors makes one
  (`Prog.norm`), and a match reads one as `Zero` or `Succ` of a number
  (`Prog.view`). A number stands for whatever its `Zero` or `Succ` form
  stands for (`Real.nat`). An extern function runs natively only once
  a Lean proof shows its native code agrees with its model; none is
  trusted unproved. So far that is `add`, `nat-cmp`, `mul`, `sub`,
  `divmod` and `nat-mod` (`Minimal/Native.lean`). The executable
  stripped run (`runS`) computes a call of one of them on numbers
  natively when the callee's elaborated body is exactly the model the
  proof is about (`addBody`, `cmpModel` and the like, kept in Lean),
  over the prelude's declarations, and, for a model that calls another
  (`mul` calls `add`; `divmod` and `nat-mod` call `succ-div` and
  `succ-mod`, which call `nat-cmp`), when the closure it calls is that
  one's proved model too (`Prog.native`). For each, a lemma (`add_run`,
  `cmp_run`, `mul_run`, `sub_run`, `divmod_run`, `natmod_run`) proves
  that the stripped run of the model gives the same non-erased results,
  so `runS_sound` still holds. The stripped run keeps a constructor's
  erased fields as tokens (`maskArgs`), which is what lets a result
  such as `nat-cmp`'s `Cmp` value be computed without its proof. A
  model the elaborator does not find to be the proved one runs as a
  model, with a warning (WARNINGS.md 1). Every other extern function
  runs its model, and the full run (`eval`, `--full`) runs every model.
  A numeral is elaborated to a primitive (`Prim.num`) whose stripped
  value is the number and whose full-run value is its `Zero` and `Succ`
  form (`natTm'`), which the number stands for (`natTm_real`); the
  checker types it `(Nat)` once the prelude's `Nat` has the shape the
  primitive assumes (`Prog.natOK`). A call of a delegate's closure is matched in the
  stripped run by the call its body makes, which `Group.deleOK` checks
  passes the delegate's own non-erased arguments through to its target,
  in order, and the target's non-erased results back
  (`Minimal/Deleg.lean`). `RunS.det` says a stripped run
  has one outcome, and `runS_sound` that the executable `runS`, which
  the runner uses, finds only stripped runs.
- **`machine_main`.** When the checker and the uses pass accept a
  program, the machine run of it (`RunM`, `Minimal/Machine.lean`) from
  the empty heap ends where the stripped run does: a heap of blocks, a
  cell invocation or `cell-write` at `unique` written into its block in
  place, `cell-alloc` allocating, and a call building only its
  non-erased arguments. Its results stand for the stripped run's, and
  the blocks a `unique` result owns are reached by nothing else live
  (`MOut`; `Spine` and `WO` are the ownership relations). `coerce` and
  calls through delegates are covered; the runner does not yet use the
  machine run.
- **`no_false`.** No checked program has as its result type a data type
  with no constructors that is neither `Coercible` nor opaque.

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
1 to 3, 11, 21 and 26), with `$`, comments and raw names `#"..."`. Each
multiplicity the full language requires is required. These forms are
refused as not supported: every form not named in this file, among
them macros, arrays, `Placed` and `World`. Only the prelude, or a program
run with `--no-prelude`, may mark a type or a function `extern`, and
only one that the OCaml FFI's table in `lib/ffi.ml` names (section 42).
The mark is recorded and changes nothing else: the runner has no FFI,
and runs each `extern` function's model, or native code proved to agree
with it (above). A file's top level
has size one, or ends in a statement and produces nothing (section 27).

Every name may be bound, special forms included (section 19); a binder
of a built-in name warns. A list whose head names a binder in scope is
an application of it, and a list whose head is itself a list is an
application of the head's value. `Special` and `Sharing` are built-in
enums, and a special form's name not bound in scope is its `Special`
constructor; a head bound to an entry the elaborator knows is a
`Special` constructor, by its value at run position or by the term a
`let` in a body binds it to, dispatches as that form. A
`Special` value prints as `%` and the form's name.

Pragmas (section 4): `;! warn`, `;! suppress warn` and `;! restore warn`,
written where a statement may stand. Warnings are printed to standard
error, without a position, and do not change the verdict.
`(compile-warn m)` and `(compile-error m)` take a string literal, or an
expression whose result is a `Settled`, non-erased `String` (section 4);
in run position the expression is run as it is elaborated, and inside a
body it must be a name that forwards such an entry. `(dump-context)`
stops elaboration with an error that names what is in scope, with each
entry's type where the elaborator knows it, its multiplicity, whether
it is `Settled`, and its `is` rule.

## Differences from MINIMAL.md

1. A `def-adts` signature may mention an entry only when the elaborator
   knows its type: an entry the top level has made by an earlier form,
   whose type the checker's context gives, a level, a function a
   `def-fns` defines, a function's parameter, a result of a call to such
   a function, or a `let` binder written with a type; or when the entry
   is a `let` of a term or an `is` parameter, which is put in its place.
   Any other entry is refused.

## Beyond MINIMAL.md

- Multiplicities (DESIGN.md sections 13 and 14), `erased`, `many` and
  `unique`, on telescope entries, `let` binders, a `match`'s mode, a
  `def-fns` or `def-unique` function and a `def-adts` constructor. A non-erased position may not mention an erased entry: the callee and
  the arguments for non-erased parameters of a non-erased call, the
  scrutinee of a non-erased match, a non-erased result, a non-erased
  `let` binder; a field of a constructor is a non-erased position
  exactly when the field is. A call whose binders are all erased, an
  `erased` match and the body of an `erased` function are erased
  throughout. A constructor declared `erased` is phantom (DESIGN.md
  section 21): only an erased position may build or hold it, and its
  branch under a non-erased match is erased throughout. An `erased` match whose results
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
  expects. `_` in place of a type is filled the same way: in a `let`
  binder's type, against the type of what it binds, and in a telescope
  entry, from the entry's own type application. An unsolved `_` is an
  error. The checker then checks the program as filled in, so the
  inference is not trusted.
- Literals (section 45). Each literal of a program is one entry, made at
  the top level before the first form that mentions it, and so are the
  proofs the form asks for. A numeral is a `Nat` of the prelude, a
  number in the stripped run and its `Succ`s in the full run, with no
  rule, so the checker sees it as opaque. A numeral that a proof form
  below names goes up to 100000, since its proof is built in unary. A character literal is an entry with the
  rule that it is `(MkChar (MkU8 n p))`, `n` its code's numeral and `p`
  the proof that `n` is below `u8-modulus`. A string literal is a
  `String` with no rule, its characters' entries consed up at run time.
  `(numeral-of l)` names the `Numeral` proof of a numeral or of a
  character's code, `(prove-literal-lt a b)` a proof of `(Lt a b)` for
  numerals `a` below `b`, and `(unary a b)` and `(unary a)` are a
  `let-match` on a proof of `(Eq (Nat) a (Succ ... b))`. Each such proof
  is a `prim (.assert t A)`: `t` is a closed derivation the elaborator
  builds from the prelude's constructors, and `A` the fact it states
  about the literals' entries. The checker accepts it when every entry
  `A` mentions has a known value (`Ctx.fixed`) of a type whose values
  are their own stripped values (`Prog.simple`: no erased field, no
  phantom constructor, every field of such a type), and `A` with those
  values in place is the type of `t`. A literal's value prints as the
  literal it reads back from.
- A result of the program whose type mentions the program's own entries
  is returned after those entries, which inference adds to the final
  results as erased ones (`Prog.hidden`), so that the result telescope
  is closed and `checked_runs` speaks of the result's type; the runner
  does not print them. Where the checker cannot build that telescope,
  the result is checked as a result of any type (`ArgsTy.anyCons`), and
  `checked_runs` says nothing of its type.
- `coerce` and the proof forms `coercible-refl`, `coercible-sym`,
  `coercible-trans`, `coercible-share`, `coercible-wrap` and
  `coercible-ctor` (sections 33 and 34). `Coercible` is a built-in type
  with no constructors and no `Matchable`. `VTy` reads a proof of
  `(Coercible sa A a sb B b)` as: a stripped value stands for `a` exactly
  when it stands for `b`. Each proof form is a primitive whose typing
  rule establishes that (`prim_sound`). `(coerce a p)` is, in the full
  run, `b`, read from the type of `p` by inference, and in the stripped
  run the value of `a`; it has the rule that it is `b`. It uses `a` at
  the multiplicity of its source side and yields its result at that of
  its target side (section 34), each of which is canonically
  `(Unique)` or `(Shared)`. `coercible-wrap` takes a constructor named
  by its declaration or listed by an opened `newtype` `Matchable`, and
  `coercible-ctor` any constructor whose signature is written out, a
  first-class one included.
- `unique` (sections 13 to 16, 22, 23 and 32). In the core a `unique`
  entry is a non-erased one that carries the mark in its telescope
  entry, so a type tells `unique` from `many`, and a stripped value
  stands for a full one as for `many`; only the machine run
  (`machine_main`) relies on a value having one reference, when it
  writes a cell in place. The elaborator checks the uses: on each path a `unique`
  entry has one non-erased use at unique or any number of uses through
  `share`, never both, a match joining its branches; a `unique` value
  in a `many` position needs `(share e)`; a value made `many` is not
  used at unique; a destructure gives its fields by the table of
  section 22; a `def-fns` body uses a `unique` entry of its scope only
  erased or through `share`. `(def-unique L $ (unique f : ...) body)`
  defines one function of the former `(UniqueFn L ... -> ...)`, which
  the core marks on its `Fn` type, born `unique`; its body may use a
  `unique` entry of its scope at unique, and its own name is not in
  scope in its body; a call through a head of `UniqueFn` type uses the
  head at unique, so a shared one is callable only erased.
  `coercible-wrap` and `coercible-ctor` give a `unique` field its
  proof's own side, and `delegate-of` gives a `UniqueFn` side
  `(Unique)`.
- A non-erased match on a `newtype` is elaborated to a `case` marked
  `nt`, which the stripped run takes without looking at the scrutinee,
  with the scrutinee's value as the one non-erased field; the checker
  allows it at most one real branch, as for an erased scrutinee.
  `comptime-match` and the checker's known values look through no
  newtype.
- `Matchable` types and `(matchable-of T)` for a declared type or a
  `let` alias of one (section 24). A `Matchable`'s type names a declared type, its tag,
  marks and constructors in order (`VTy.mtbl`); its value is a token.
- Run position (sections 27 to 29). The elaborator runs each
  run-position statement, by the stripped run, as soon as it is
  elaborated, and keeps the values; an entry so known and non-erased is
  `Settled`. A head bound to a `Settled` entry whose value is a `Special`
  constructor, and whose type when it was made is `(Special)` by the
  facts in force at the top level, dispatches as that form; so does a head that is itself a form in run position whose value
  is one. The checker keeps, beside its context, the
  stripped values of the entries the top level has made so far
  (`Ctx.fixed`), computing each by the stripped run (`stepS`), and
  `EnvOK` carries that each stands for the full run's value (`FixOK`).
- `comptime-match` (section 28), in run position, `many` or `unique`, on an enum and
  a constructor that is not phantom; its pattern may bind a cell. In the core it is a `case` with one
  branch inside `chk .cm`, under which a constructor with no branch is
  accepted when the checker's known value of the scrutinee is headed by
  another (`BranchOK.fixedOut`). The branch's fields are known values too.
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
- `delegate` (sections 19 and 41), with the `at f` its function's header
  carries, which names a function in scope at the header, an earlier
  one of the block included: the call must be to `f`, in tail position,
  passing the function's non-erased parameters straight through in
  order, each either itself or a `coerce` of it. In the core it is an
  ordinary call, and the function records its target (`FnDef.dele`).
  The body is checked with every entry made before the function's
  parameters erased, its target aside, and the checker requires its
  post-erasure code to be the one call, as above (`Group.deleOK`):
  renames, constants that allocate nothing, erased code, erased
  `let-match`es and other run-free statements before and after it, and
  a final result of variables that returns the call's non-erased
  results in order. A non-erased delegate to a `UniqueFn` is itself
  unique, and a target in the delegate's own block is not
  (`Group.sidesOK`).
- `Delegate`, `(delegate-of g)` and `(coercible-of d)` (sections 19, 33
  and 34). `Delegate` is a built-in type with no constructors and no
  `Matchable`, read by `VTy` as `Coercible` is. `def-fns` records, for
  each non-erased function with a `delegate` body in a non-erased
  block, its pair with its target and their sides, `(Unique)` for a
  `UniqueFn` and `(Shared)` for an `Fn`, fixed from the two functions'
  types there (`Ctx.deles`); `(delegate-of g)` names that pair's proof,
  `(Delegate sg G g sf F f)`, in the bodies of the block and after it, and `(coercible-of d)` turns it
  into the `Coercible` proof between the same sides. `EnvOK` carries
  that a stripped value stands for each such `g` exactly when it stands
  for its `f` (`DeleOK`). `def-fns` makes the proof once, after its
  block; `delegate-of` in a type names that one, so it is refused in a
  signature of the block itself.
- `tail` and `notail` (section 19): the call must, or must not, be in
  tail position: the final expression of a function body, of a branch of
  a match in tail position, or of a `let`'s right-hand side when the
  rest of the body returns its binders in order, or a `coerce` of its
  one binder, after `let`s whose binders are all erased. Neither is
  accepted in an erased position.
- `def-opaque` and `def-prim` (INTERNALS.md sections 1 and 2), in the
  prelude or under `--no-prelude`. An opaque type is a declared type
  with no constructors and no `Matchable`, which no match goes through;
  `VTy` lets any value inhabit it (`VTy.opq`), so `no_false` leaves it
  out. The runner implements no primitive, so a `def-prim` must have
  every return erased: a call checks each argument against its
  parameter's type and makes each return an axiom (`Prim.axm`), which
  the checker accepts only at an opaque type.
- Slots and `at` (DESIGN.md sections 35, 36 and 41). `Slot` is a
  built-in type with one constructor and no `Matchable`, and
  `vacant-slot` is that constructor; a value prints as `_`. In the core
  a slot is an entry of type `(Slot)`, made by `Prim.atom`, which
  evaluates to the constructor; the core knows nothing of locations,
  and two slots are one exactly when they canonicalize to one entry.
  The elaborator makes an entry's automatic slot the first time it is
  needed, or just before a `def-lvl` for an entry that a later
  `slot-of` of the same sequence names, at the entry's erasure, and puts an entry at its source's
  slot where section 36 has one: a forwarding `let`, `share`, `coerce`,
  an `else` binder, a newtype's construction and destructure, the
  delegate annotation, a cell binder, a cell invocation and
  `cell-write` at `unique`. A telescope entry written `at v`, or whose
  slot a `slot-of` or an `at` of the same telescope names, is preceded
  in the core by a hidden erased entry (`Tm.fn`'s mask): its slot, a
  `(Slot)` entry, or for `at v` an `is` entry that it is `v`'s slot.
  A call passes each such argument's slot there, binding an argument
  that is not a variable first, so an argument written `at` that is not
  a variable is refused; a body returns its results' slots, so the
  core checks each promise canonically. `(slot-of x)` is the slot of
  `x`, erased when `x` is, and of a hidden entry erased always;
  `(slot-of vacant-slot)` is `vacant-slot`, and a `let` of
  `vacant-slot` puts its binder there.
  `(slot-self s)` makes `s` its own slot, and is refused once the slot
  of `s` is in use. `at` changes no value: the runner computes an
  `at` result like any other. Not done: the slot a forcing unification
  gives otherwise than through the core's own rules, `slot-of` naming
  an entry of an enclosing telescope in an `at`, `_` for an argument
  whose slot is named (its slot is `_` too), and `prove-predates` on a
  slot first needed after the level other than through such a
  `slot-of`.
- At-functions and at-matches (sections 39 and 40), checked by the
  elaborator: the returns or annotation entries are erased or `at`, and
  the body or each branch makes no non-erased call that is not skipped,
  no constructor application that is not a newtype's, and no
  allocation, write or store of a cell. A call is skipped when its
  callee is a function of an at-function's own block or one whose
  `AtFn` proof is opened by `open-at-fn`; `(at (f ...))` requires it,
  and `tail` and `notail` refuse it. `AtFn` is a built-in opaque type;
  `def-fns` makes the proof of each at-function after its block, an
  axiom, and `(at-fn-of f)` names it. A skipped call and an at-match
  run like any other. A non-erased match on a union with several real
  branches is refused even as an at-match.
- Cells (sections 37 and 38). `(Cell C s ...)` is, for each
  constructor `C`, a declared opaque type of one `(Slot)` parameter per
  non-erased field, made when first named; a newtype's, an extern
  type's and a phantom constructor are refused. A cell is an axiom of
  its type (`Prim.axm`, which the checker accepts at a non-erased
  position too, since any value inhabits an opaque type), and holds
  nothing. `cell-alloc`, `cell-write`, a pattern's cell binder and
  `cell-match` make cells and read their slots from their types; an
  invocation `(u a ...)` is the application of `C`, and `(at)` before
  an argument, or `(at (u a ...))` for all of them, asks the core that
  the argument's slot canonicalizes to the cell's; in the latter `u`
  may be an expression whose value is a cell, such as a `cell-match`. The elaborator
  accounts for the uses of the cell as section 37 has it. The core marks
  an invocation, a pattern's cell binder, `cell-alloc`, `cell-write` and
  an at-match (`Chk.mark`), and an at-function (`FnDef.atf`). The full
  and stripped runs ignore them; the uses pass reads the marks, and the
  machine run writes a cell invocation or `cell-write` at `unique` into
  its block in place and allocates at `cell-alloc`. Skipping what costs
  nothing (at-function calls, at-matches, `at` entries) is not done
  (HANDOFF.md).
- `else` branches (DESIGN.md sections 21 and 23): an `else` stands for
  every constructor neither listed nor refuted, is checked with no
  forced facts, and is an error when it stands for no constructor.
  Under a non-erased scrutinee, an `else` that stands only for phantom
  constructors is elaborated as one erased branch for each, so it adds
  no real branch.
  `(else x2 body ...)`, with more than one item after `else`, binds
  `x2` at the scrutinee's multiplicity, with the rule that it is the
  scrutinee.
- `_` as a `def-fns` level (DESIGN.md section 46).
- `_` as a match annotation (section 47) in the final expression of a
  function body, of a branch, and of a `let` whose binders all carry a
  type or `is` clause, and as an argument of a constructor named
  directly or of a function whose type the elaborator knows and whose
  signature has no hidden entry (below), against the parameter's type.
  Elsewhere it is refused.
- A call in a body with no decrease annotation, or with `(predates _)`
  or `(subterm _)` written anywhere in it (section 48): the checker
  supplies a `predates` proof when the callee's level does not
  canonicalize to the current one, which needs the callee's level to
  canonicalize to an entry made before the current level, and otherwise
  a `subterm` proof for the first `subterm` argument that differs from
  its counterpart, which needs it to be a strict subtree of the
  counterpart after canonicalization. A same-level call whose `subterm`
  arguments are all unchanged is refused. A written `(predates _)` asks
  for the first of the two, and a written `(subterm _)` for the second,
  for the argument it precedes.
- `(level-of f)` (section 53), in a term and as an argument of
  `prove-predates`, for an `f` that a `def-fns` in scope names, an
  earlier function of its own block included in a signature, directly
  or through `let` binders forwarding from one, and for a parameter
  written with an `Fn` type whose level is an entry.

## Shapes chosen here, for the owner to confirm or change

- An `is` entry of a telescope, `(m e is x)` or `(subterm m e is x)`, opens to an entry with the
  rule that it is `e`, and is typed through that rule, so its type is
  `e`'s (DESIGN.md section 12). An argument or a result supplied for it
  must canonicalize to `e`. In the core such an entry has no type of its
  own: its recorded type is a marker (`Tm.nil`) that the checker reads
  as "the type of its rule" and that every value has.
- The entries a `def-adts` block's signatures mention become
  leading `erased` parameters of each of its types and constructors. In
  the core they are part of the head: `Tm.tyc d ls` and `Tm.vc d c ls`
  carry them, so `String` alone is a `TyCtor` of its own parameters and
  `SCons` a `ValCtor` of its own fields, and both are first class. A
  constructor's value holds only its own fields, and its type carries
  the lifted arguments; the stripped run leaves them out of the head.
  The elaborator supplies them at every use, a pattern binds only the
  constructor's own fields, and the printer shows only those. A match on
  such a type goes through its declaration with the lifted arguments of
  the scrutinee's type. The core's declarations stay closed. `def-adts`
  blocks are elaborated in the order they are written. A block inside a body is declared in the
  program like any other, and its names are in scope to the end of the
  body.
- An application `(x args)` of a variable is a constructor application,
  a term, exactly when `x`'s type is written as a `TyCtor` or `ValCtor`
  where `x` is bound, `x` is a `let` binder of a constructor named
  directly, or `x` is a `let` binder of a result whose type the
  elaborator knows to be a `TyCtor` or `ValCtor`, a call's result
  through the callee's written return entry say; otherwise it is a
  call. A constructor value reached any other way is applied after a
  `let` binder written with its type. A `ValCtor`'s return
  must be an application of a type constructor that is not one of its
  own fields (ASSUMPTIONS.md 80). In the core every
  application is one former, `Tm.app`, whose head is a declared type
  constructor, a declared value constructor or a variable, and is typed
  through its head's type; a value of a `ValCtor` type is a declared
  constructor head whose signature, instantiated with the head's lifted
  arguments, is that type, and one of a `TyCtor` type likewise a
  declared type constructor head.
- A `let` binder written `(m T x)` or `(m e is x)` is checked, after
  canonicalization, against the type or the term written, and adds no
  rule of its own.
- A `let` binder forwards from its right-hand side, as DESIGN.md
  section 19 has it: a binder of a variable is that variable's entry,
  and a binder of any other term of the type grammar is a new entry
  with the `is` rule that it is the term. An `erased` binder of a
  `Settled`, non-erased entry is a new erased entry with the rule that
  it is that entry, so that it holds no value (section 19).
- A branch forces two equations: the scrutinee equals the constructor
  applied to the branch's field entries, and the scrutinee's type equals
  the constructor's return type.
- Unification decomposes every node of the same shape, binders included.
  Its atoms are the variables, the declared type and value constructors,
  `Type` and `Level`. When it equates a variable with an atom
  (`Ctx.atoms`), it contradicts if one opened `Matchable` lists the two
  at different positions; otherwise it unifies their signatures when
  both have one, as DESIGN.md section 7 has it for two atoms, and every
  `Matchable` that names either of them, as section 8's invariant has
  it. Two distinct declared atoms are not told apart by name: they
  contradict only when their declarations cannot be identified, by
  signatures and `Matchable`s and the atoms those mention in turn
  (`declIso`), and otherwise the equation adds no rule, the core having
  no rule for a declared name. `Type` and `Level` have no `Matchable`.
  The proof rests on a value having at most one such signature
  (`VTy.sig_det`) and on every `Matchable` naming a value being its
  declared type's (`Names.uniq`); two distinct declared atoms are never
  one value, so what is decided for them needs no proof.
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
- The body of a function with a `delegate` body is checked with every
  entry made before the function's parameters erased except its target,
  and `delegate-of` names only a non-erased function of a non-erased
  block. Without the first, the proof had no stripped environment for
  the delegate's body when the only stripped value at hand stood for
  its target; without the second, `Real.dele` could not relate a
  stripped value to the delegate in both directions.
- `unique` is checked by the elaborator, and again in the core by
  `usesCore` (`Minimal/Uses.lean`), which the runner requires of a
  checked program and which reads the marks the elaborator leaves
  (`Mark.uq`, `Mark.uqScr`, `Mark.rebind`, `Mark.reuse`, `Mark.write`):
  on each path a `unique` entry has one non-erased use at unique or only
  uses at many, a match joining its branches, a use at unique is of an
  entry born `unique`, and a `def-fns` body uses an entry of its scope
  at unique nowhere. `eval_sound` and `checked_runs` need nothing from
  it; `machine_main` takes the pass's success as a hypothesis, since a
  cell written in place must be reached by nothing else live. A `let` binder of a `unique` entry, or
  a `unique` binder, is an entry of its own that is the right-hand side,
  so that its uses are counted apart from those the right-hand side
  made. Where the elaborator cannot read a `coerce`'s side off the type
  of its proof, it takes the source side to be the source's own
  multiplicity and the target side to be what the position asks for.
