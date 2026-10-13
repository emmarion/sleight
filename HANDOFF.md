# Handoff

Work in progress handed from one session to the next. Written by a
Claude session; nothing here is a design decision.

## `lean/`: towards the full language (one session, with the owner)

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's (`unsupported`, `refuse`, `accept`,
`mismatch`, `stuck`); at the last run about 45 tests were accepted with
OCaml's value and none mismatched. `lean/prelude.py` regenerates
`lean/prelude.sl` from `lib/prelude.sl` (128 of 215 forms). A checked
program prints from the stripped run; `--full` runs `eval`, which
computes erased values and so is slow on the prelude (about 3 s).

Next, as this session planned it, none of it decided:

1. `Matchable` stage 2 (stage 1, the former `Tm.mtbl`, `VTy.mtbl` and
   `matchable-of`, is in). The plan: `Ctx.branch` takes the constructor
   term and the scrutinee type's head in place of `d` and `c`; a `Shape`
   relation lists (constructor term, signature, phantom mark) for a
   declared type (`vc d c`, `D.ctors[c]`) or for an opened `Matchable`
   (its listed constructors, signatures read from their `ValCtor`
   types); `mtch`, `case` and `BranchOK` are stated over a shape; a
   branch tuple's first component becomes the pattern's field count,
   which `realBr` needs, since `d` is unknown for an opened `Matchable`;
   `open-adt` is a new `Chk` kind that adds the entry to an `opened` list
   in `Ctx`, which only the checker consults. In `match_setup`, an opened
   `Matchable` gives, through `VTy.mtbl`, the declared type, and each
   listed constructor's value is `vc d c`, so its signature substitutes
   to `P.ctor d c`. Branch keys stay constructor positions, so `eval`
   and `RunS` do not change. Then stage 3, disjointness of the
   constructors of one opened `Matchable` in `unify`, and stage 4,
   `open-absurd`.
2. Equating the types of the two sides when unification assigns a
   variable, as the OCaml checker does. `VTy` does not give a value one
   type (`univ` and `top` hold of every value, and `.tok` of every true
   `Predates` and `Subterm`), so the proof would need a lemma for the
   types where a value's type is unique, or a narrower `VTy`. The owner
   asked whether it is really unjustified; this session overstated it and
   has not checked. For data values, value constructors (`VTy.vc` fixes
   the signature), type constructors, levels and closures a value's type
   looks unique, which may be enough: the narrow route is to prove that
   two entries with one value have one type outside `Type`, proofs and
   `.nil`, add the type equation to `unify` for those entries only, and
   see whether `UnifySound` goes through; the broad one is to narrow
   `VTy.univ` to type terms and have a proof value carry its statement.
   The session's one attempt at a counterexample, two proofs of
   different statements forced equal through `JMEq`, did not go through:
   the indices refute the branch first. What it would buy:
   `tests/is_for_type_refute.sl` (the `ctor-type-is` functions, two
   `ValCtor` variables forced equal) and the `Matchable` invariant of
   DESIGN.md section 8, as in `tests/open_tyctor.sl`'s `told`, which
   refutes `IsNat` through a constructor's signature.

## `read-file`, `symbol-eq` and the elaborator's world (one session, with the owner)

Done in both compilers, to the owner's design given in chat, with DESIGN.md
sections 62 to 65 in the owner's words; MACROS.md is gone, its content
there or settled. ASSUMPTIONS 219 has what the session chose. `slc`'s
elaborator threads a unique `ElabWorld`, a newtype over the `World` that
`compile` holds, through every function that can reach an expansion.
`self/bootstrap.sh` and `dune test` are clean. callgrind on `slc`
compiling `base.sl`, `heap.sl` and `reader.sl`: 1.7436G instructions for
the base, 1.7439G with the threading, 1.7487G with `read-file` and its
prelude declarations.

Left for later, none of it decided:

1. The owner suggested `ElabWorld` become a bundle of the elaborator's
   unique, run-wide state; the gensym counter and the literal table, now
   in `Env`, look like candidates. A second non-erased field would end its
   `newtype` shape, and with it, on this session's reading, the way
   `compile` gets its `World` back `at` the one it gave; `MacroState`'s
   slot index (ASSUMPTIONS 219) may serve there too.
2. A cache of what `read-file` reads, so every expansion in a run sees one
   content; the owner set it aside for now.
3. MACROS.md's section 5, a session's argument that reflection can only
   steer what a macro generates, was not carried into DESIGN.md; it is in
   git history.

## Bare-bones macros (one session, with the owner)

Done in both compilers, to the owner's design given in chat; DESIGN.md
sections 62 to 65 say what is implemented and ASSUMPTIONS 213 what the
session chose. `self/bootstrap.sh` is clean and now compares each side's whole
stderr. Measured with callgrind on `origin/main`'s `base.sl`, `heap.sl`
and `reader.sl` (`Pos` and `Raw` renamed, so nothing warns): `slc` built
from `origin/main` 1.393G instructions, from `raw-names` 1.482G, from this
work 1.519G, about 2.5% over its base; the owner accepted that.

## Literals outside every scope, `prove-predates` by binder (one session, with the owner)

Done in both compilers, on a design worked out with the owner in chat
and written into DESIGN.md 5, 7, 18, 19 and 45 in the owner's words:
every entry a literal stands for has one identity for the whole
program, met inside a body or branch or not, and `prove-predates` reads
its two arguments by their binders through an introduction order every
entry carries. ASSUMPTIONS 212 has the mechanisms, which differ between
the compilers because the reference drops an inner env wholesale where
`slc` has an explicit exit. `self/bootstrap.sh` is clean, and `slc` on
its own sources took 2.72 to 3.05s against 2.61 to 2.96s for the
previous `slc` over several runs, which this session read as noise; its
max RSS swings between about 108 and 132MB for one and the same binary,
so no memory comparison was drawn.

## The compile-time store: stamped values, a ghost history (`self/`)

Done, at the owner's direction and to the owner's design. `slc`'s
compile-time interpreter no longer addresses its values into a Braun-tree
store: a value refers to other values directly and carries a stamp, and
what makes the stamp trustworthy is an erased ghost history, the owner's
idea. `self/heap.sl` holds it -- `Hist`, `Value`, `Len`, `Suffix` and
`Ref` as one mutual (inductive-inductive) block, parametric in the block
type, which takes the *reference* type as its parameter so that it never
mentions the history; that is what keeps the block generic rather than
forcing it into `core.sl`. A `Store` is the next stamp alone and a `Ref`
is its target, both being newtypes over their one `many` field.

`suffix-unique` derives that a history has one suffix of each length, and
`ref-unique` that two references into one history at one position name
one value. That is this session's reading of what makes the emitter's
memo sound, and the reason the ghost history is there; nothing calls
either lemma. Measured rather than assumed: the reference and `slc` both
accept the shape, and `ref-widen`, the lemmas and `empty-suffix` extract
to no OCaml at all.

What this bought, on the session's reading: the host reclaims what is
unreachable, where the old store held every block for the whole run;
reading a reference is a projection rather than a tree walk, and `alloc`
a constructor rather than a rebuilt path; and the emitter walks only what
a Settled or a final reaches. Measured with an instrumented reference
extractor before the change, reachable values against the blocks
ASSUMPTIONS 148 counts: 1570 against about 20000 for `slc`'s own sources,
and 197, 181, 227 and 126 against 665800, 157418, 162987 and 44797 for
`mini_recursion`, `mini_axioms`, `mini_dependent` and `mini_elab`. Max
value depth was 226 and 13-19 respectively.

Things the session had to change course on, recorded so they are not
rediscovered:

- `deref` was deleted rather than kept. A call's result is `Hypothetical`, so
  calling it destroys the subterm relation, which is what stopped
  `rope-walk` and the printer recursing structurally. Both now match
  through `MkRef`/`MkValue` and need neither the store nor a fuel, and
  `ref-suffix`, erased, replaces what `deref` computed.
- Post-order DFS alone does not order the output. A group's body also
  names other Settled entries, and that edge is not in the value graph; today's
  emitter got the ordering from address order instead. Emission is now in
  stamp order, which orders every edge, since anything a block names was
  allocated before it. Adding those edges to the trace was considered and
  set aside: they jump to arbitrary Settled entries, so the walk would stop being
  structural.

The stamp sort is a generic merge sort, at the owner's request, and is
the first higher-order function in `self/`: `base.sl`'s `sort-factory`
takes the comparison as a parameter in the shape of `tests/map.sl`'s
factory. `merge` recurses lexicographically on the two lists -- the
first shrinks, or it is passed on unchanged and the second shrinks --
which is DESIGN 7's order directly, so it needs no fuel; the split is a
Braun-shaped pile built by insertion, so that recursion is structural
too. `merge` carries the output as an accumulator, newest first, and
hands it to `rev-onto` at the end, so it and `pile-of` are `tail` and
run in constant stack; what is left recursing is `pile-add` and
`pile-sort`, both down the pile, so the session reads the depth as the
pile's height rather than the list's length. The emitted OCaml for
`merge` and `rev-onto` is tail calls, which the `tail` marks require
anyway (DESIGN 9 makes an unhonoured claim a hard error).

Applying it to a type carrying an erased index took two things the
session got wrong first: the index has to be closed over rather than
taken as a parameter, a first-class `Fn` having to match arity exactly,
and the comparison's level has to be minted at the top level rather than
left to `_` inside the body, or the factory cannot relate it. `emit.sl`
mints `REF-CMP` and builds the sort there; `ref-le` is defined at that
level inside `emit-program`, closing over the history.

Widening is now an erased `*-widen` and a `coerce` at each call site,
the owner having pointed out that a call to a `many` wrapper extracts to
a real call where the inline `coerce` extracts to nothing. The eight
wrappers are gone and none of their names appears in the compiled
compiler. `st-widen` was added to match; the awkward part was placement,
a `coerce` needing a two-binder `let` before it, so a site nested in an
argument had to grow a statement in the nearest enclosing statement
position rather than be rewritten where it stood.

The trace is a tail recursive worklist, to the owner's design, who
supplied both moves the session had failed to find. Termination may rest
on erased state, which can be as inefficient as it likes: `base.sl`
gains `Bounded V m size max`, relating a trie to its size and a bound
its keys sit under, splitting that bound the way the trie splits keys
(0 here, 2m+1 in one, 2m+2 in two, so l + r = m1 with `Braun l r`). That
split is what makes `bounded-le` -- a trie bounded by max holds at most
max entries -- plain addition monotonicity rather than a counting
argument, and it is why the `Braun` arithmetic the old store carried is
exactly what this wanted: `half-lt-one` and `half-lt-two` already say a
halved key lands inside its child's bound. `idmap-set-bd` inserts a key
the trie lacks and returns the proof the size went up by one; `seen-add`
reads `bounded-le` off the *new* trie, which is the owner's second move,
so `Succ size <= max` gives `size < max` and no strict pigeonhole is
needed. `add-room` turns that into a strictly smaller `rest` in
`Add size rest bound`, and `lt-subterm` -- which `idmap-set` already
used this way -- into the `Subterm` the call wants. `ref-key` supplies
the side condition, every stamp being below the store's next, off
`suffix-len`.

The loop decreases on `rest` first and the worklist second: a fresh
value shrinks `rest` and may grow the worklist, an already seen one
passes `rest` through untouched and pops. In the compiled compiler
`trace-loop` takes five runtime arguments, both its self calls are OCaml
tail calls, and `bounded-le`, `add-mono`, `add-room`, `split-bound`,
`absent-one` and `absent-two` emit no code at all.

Measured against the binary from before the change (50097cf), best of
three runs each on this machine, wall and maxrss: `mini_axioms`
2.98s/139MB against 1.05s/36MB, `mini_dependent` 1.38/58 against
0.92/37, `mini_recursion` 1.26/61 against 1.03/35,
`bench/comptime_live` 0.16/38 against 0.12/33, `bench/comptime_garbage`
0.11/21 against 0.04/12. Two go the other way or level: `mini_elab` 0.98
against 1.03, and both compilers on the same (old) sources 1.32 against
1.28. The session reads the win as being in what a compile-time run
throws away rather than in compilation at large, the memory drop being
the steadier of the two. `bench/gen.py` writes the two samples: the same
list built at compile time, folded away in one and kept in the other,
emitting 361 and 24358 blocks.

The walks that scale with the number of blocks are tail recursive:
`trace-loop`, `emit-blocks`, `merge`, `rev-onto`, `pile-of`,
`roots-of-finals`, `frames-refs`. The rest of `emit.sl` recurses without
a `tail` mark, but on things that do not grow with the store: code depth
(`emit-code`, `collect-code`, `block-rope`), trie depth (`idmap-get`,
`idmap-set-bd`, `roots-of-entries`), pile height (`pile-add`,
`pile-sort`), a constructor's arity, or the declarations. The session
found none whose depth follows the block count, but that is an audit by
reading plus one measurement (24358 blocks emitted, 40358 in a larger
run off the bench), not a proof.

Where a big compile-time run still breaks is the interpreter, not
emission: at a list of 60000 both the old and the new binary overflow
the stack, and equally so when the list is unreachable and emission does
nothing. That is `self/README`'s standing exception -- structural
termination everywhere but the interpreter and the generated printer --
and this branch does not touch it. A later session did, for the tail
call half of it; see the last section.

Open, none of it decided:

1. `bench/bench.sh`'s pinned sources no longer compile. `PINNED` is
   4fda15f, which predates 52d869a and 193f2fd changing the prelude's IO
   shape, so `self/main.sl` at that commit is refused against today's
   prelude, by the old binary as much as the new one. Re-pinning would
   change what the benchmark measures, so the session left it. Since resolved
   at the owner's direction: the commit is now a required argument to
   `bench/bench.sh`, since the syntax is expected to keep changing.

## The minimal language and its semantics (`mini/`)

Done, in one autonomous session at the owner's request:

- MINIMAL.md records the cuts the owner decided and the decisions made in
  chat about the semantics (relational, algorithmic, simplest possible,
  written in the full language, axioms as special forms, error on
  SPEC-REVIEW 7, a positive `Fails`, `Term` and `Val` separate).
- `mini/` holds the relations and their deriving functions, bottom up:
  terms, canonicalization, the context, unification, core code and values,
  evaluation, elaboration. `mini/README.md` lists the shapes chosen and
  what is open.
- `tests/mini_*.sl` exercise each layer and run four programs of the
  minimal language end to end through `elab-program` and `eval`, plus
  refused programs with their `Fails` reasons.

Next, in the session's estimation:

1. Ask the owner to confirm or change the surface syntax and the shapes in
   `mini/README.md`, in particular the grouped telescopes and binders,
   `Univ` as a term, and malformed syntax deriving nothing.
2. A reader from text to `Raw`, so tests can be written as programs.
3. State the metatheory as types in `mini/` (theorems as erased functions
   with `absurd`-free bodies are the natural shape, but nothing is
   started).

## Fuel removed from `mini/` except `eval` (one session, autonomous)

Done, at the owner's request that everything in `mini/` but `eval` recurse
structurally, with the relations kept as they were:

- `term.sl`, `canon.sl`, `unify.sl`, `elabfn.sl` derive their relations
  without fuel; `mini/README.md` describes the measures and the
  well-formedness carried. `ctx.sl` grew the scope and growth machinery
  the elaborator threads (`Scoped`, `Ext`, `Grew`, `Covers`, and wrappers
  over `Ctx`).
- The relations changed in two places, both for the owner to confirm or
  reject: `Subst`'s `SubBeyond` (since removed, below) and `Unify`'s
  `Sided` merge of the left/right twin rules. The function-side
  `Oriented` lost its `OrStuck`.
- One non-syntax stuck remained, the type of a closed term
  (`type-of-term`, now in `mini/unify.sl`; since closed, below). A later
  session, funded to close it by a preservation argument, found the
  argument false as the relations then stood: a program reached the
  stuck (`tests/mini_untyped_rule.sl`, with the reading of why in its
  header). Two owner decisions followed. `ETValCtor` now requires
  ASSUMPTIONS 80 of a `ValCtor` former's return, which `lib/` and `self/`
  already did. And `UAssign` equates the assigned variable's type with
  the term's, pushed as the next equation. `lib/` and `self/` now do the
  same when solving a meta (DESIGN.md section 50, the owner's decision),
  but not when forcing: their forcing assigns without a type check, and
  their atom-against-atom case unifies signatures only where both are
  formers (ASSUMPTIONS 89); `Refine` and `Contradict` take one equation,
  the scrutinee against the pattern, the type equation following from
  it. So `mini/`'s forcing is stricter than the reference's: whether
  `lib/` and `self/` should follow there, and the sentence section 7 of
  DESIGN.md would need, are for the owner. One session's reading against
  following, not proved: types here can mention slots, and section 36
  says `is`-equality says nothing about slots, so equating the types of
  two atoms a forcing binds could turn an `is`-equality into a slot
  equality; and in the programs tried (every test, and slc's sources)
  the equation never changed an outcome, each forced atom's type
  seemingly being fixed by indices the forcing had already unified. For the function side this moved the stuck
  into unification (`RefStuck`, propagated as the `Stuck` constructors
  of the walk's result types, which only `Force` mode can be). This
  paragraph used to add that closing it would need the invariant that
  every application head in play has a former's type, carried through
  the elaborator and unification; the two sessions below took the other
  route, recording the former on the application itself, so
  `type-of-term` is total and `RefStuck` and that family are gone.
  `mini/preserve.sl` holds groundwork for the preservation argument
  `mini/README.md` still leaves open.
- `TOOLING-WISHLIST.md` logs the friction met writing `.sl` by hand at
  this scale, as the owner asked.
- The self-hosted `slc` (`self/`) accepts every file and all eight
  `tests/mini_*.sl` match the interpreter through it, but three of them
  (`mini_dependent`, `mini_axioms`, `mini_recursion`) overflowed the
  OCaml stack under the default 8MB limit, so `self/bootstrap.sh`
  reported them as failures. This paragraph used to place the overflow
  in `slc`'s compile-time interpreter; it was in the emitter, and the
  session below fixed it.

Next, in the session's estimation: the owner's verdict on the `Sided`
merge and on the `type-of-term` hole (since closed, below), then the
items above.

## The three `mini/` tests `slc` refused (one session, at the owner's request)

Done. The overflow was in the emitter, not the compile-time interpreter:
`emit-blocks` (`self/emit.sl`) and `addrs-from` (`self/heap.sl`) each
recursed once per address the compile-time store holds, and the store is
as long as the compile-time run is (157418, 162987 and 665800 blocks for
the three tests, against 44797 for `mini_elab`, which passed). Both take
an accumulator now and are marked `tail`. `lib/extract.ml`'s sharing
table had a related non-tail scan, also fixed. ASSUMPTIONS 148 records
the measurements and TOOLING-WISHLIST 15-16 what would have found it
sooner. `self/bootstrap.sh` is green at the default stack limit.

Open, in the session's estimation, none of it urgent and none of it
decided:

1. `lib/extract.ml`'s `value`/`plain` still recurses once per node of the
   value it walks, which no accumulator fixes; an explicit worklist
   would, at the cost of reordering the `shared_N` definitions it emits.
   Whether that reordering is acceptable is the owner's call.
2. The same file's sharing lookup is linear in its bucket, so extracting
   a deep self-similar value is quadratic in its depth. Whether to keep
   the structural hash (which cannot tell the suffixes of such a value
   apart, so no deeper hash helps) or key the table some other way is a
   design question this session did not attempt.
3. Nothing bounds the compile-time store: every value the interpreter
   allocates keeps an address, so the emitter's walk is as long as the
   whole run, not as long as the result. The walks are flat now, so
   nothing fails for it; it is why they were the deepest thing in `slc`.

## `SubBeyond` removed and the `Bound` stuck closed (one session)

Done, at the owner's word after a chat analysis of `SubBeyond`: a binder
past the substitution list is not a case substitution has an answer to,
the rule kept the index unshifted where a shifted one would have been
right, and it was harmless only because elaboration never builds such a
term. So the rule is gone and the closedness that made it harmless is
carried:

- `Scoped` gained a depth index (`Scoped ents d t`, with `ScopedTele`
  giving the depth a telescope ends at); `Closed d t` in `term.sl` is its
  entry-free half, which `subst` requires and refutes the missing index
  from. `base.sl` holds `Length`, `Layout` (the shape of a substitution
  list) and `Plus`, which the depth bookkeeping needs.
- The unification walk carries the depth of the equation it is on;
  `assign` tightens to depth zero from `Assignable`; the elaborator's
  telescope-threading functions (`mint-tele`, `elab-term-args`,
  `check-rets`, `elab-expr-args`, `elab-tele`) carry the depth their
  remaining entries sit at, `Cov` and `ScS` record their lists' layout,
  and `inst-ret` in `ctx.sl` instantiates a former's return from
  arguments of its arity. `LenMismatch`, `LenDec` and `len-dec` moved to
  `ctx.sl` so that `type-of-term` can decide arity.
- `type-of-term`'s `Bound` case is an empty match; its one remaining
  stuck is an application whose head's canonical type is not a former of
  the application's arity, the head-type hole above unchanged. No
  relation of the semantics changed except the removal of `SubBeyond`.
- `tests/mini_term.sl` and `tests/mini_unify.sl` build the new evidence
  by hand; the other `mini_*` tests are unchanged and pass.

Next, in the session's estimation: the head-type stuck, by one of the
routes discussed with the owner (a well-typedness invariant carried
through unification, or recording an application's former or type on the
term as DESIGN.md section 5's entries do).

## The head-type stuck closed by `TyApp` and `ValApp` (one session)

Done, at the owner's word after a chat comparison of the two routes
above: `Term`'s one `App` became `TyApp head params args` and
`ValApp head params ret args`, DESIGN.md section 9's productions 2 and 3
each with the former it applies recorded on the node, so that
`TypeOfTerm` needs no head type and `type-of-term` is total;
`mini/README.md` has the shape and what it leaves to the metatheory (the
recorded former's agreement with the head's type is checked nowhere).

- Every relation over `Term` gained the twin rules; `Canon` and `Unify`
  ignore the record, `Scoped` also asks arity (`LenEq`, now in
  `base.sl`). `ShapeOf` gives `ValApp` the code 7, after the formers.
- With `type-of-term` total, the `Stuck` constructors that only it fed
  are gone: `TotStuck`, `RefStuck` and the walk's `WalkStuck` family
  and `EqsStuck` in `unify.sl`; `TypedStuck`, `MTStuck`, `RDStuck`,
  `RefStuck` and `CovStuck` in `elabfn.sl`. The `Stuck` answers for
  malformed syntax stay, as `mini/README.md` says they should.
- `elab.sl`'s rules that build an application record the head's
  canonical former; the built-ins' telescopes are `predates-ps` and
  `subterm-ps`, shared with `init-ctx`. The rules that read a type's
  shape match `TyApp` and count a `ValApp` as not having the shape
  (`NotTyApp`); `StrictSub` walks through either kind by `AppParts`,
  as section 18 says. New erased fields on these rules (the params
  read, `hps`/`tps`/`aps`) are the only other change to the relations.
- `tests/mini_term.sl` and `tests/mini_unify.sl` build the split terms
  by hand; every test and the bootstrap pass.

Next, in the session's estimation: the owner's verdict on the `Sided`
merge, then the metatheory (MINIMAL.md's list and the agreement above).

## Interpreting a tail call as a tail call (`self/eval.sl`)

Done, at the owner's request: `slc`'s compile-time evaluation should not
grow the stack, or at the least interpreting a tail call should be a
tail call. It is now the second of those, and the paragraph above about
a list of 60000 is out of date -- that program, and the two `bench/`
compile-time samples at 60000, run in constant stack.

The emitted OCaml was where the diagnosis came from rather than reading
the source: `eval`'s `CLet`, `CLetRec` and `CMatch` were already bare
tail calls, the normalizer having dropped the `let` that bound their
results, and only two places were not. `eval` returned `Vals ms` and
`apply` a plain list of addresses, so `CApp` fitted `apply`'s result to
the call's index *after* the call and `apply` stripped `eval`'s result
to a list *after* the call. Each conversion held a host frame per
interpreted call, and that was the whole of it.

The fix is to have the two hand back the same thing: the list of many
results, with the index carried as an erased `Picked` beside it rather
than as the shape of the data. `Vals` and `vals-widen` are gone from
`core.sl`; `mults-same` and `picked-lockstep` join `picked-same` and
`picked-along` there. Where a call's index and the callee's declared
returns differ in erased entries, which the normalizer makes possible,
`apply` decides `ManySame` *before* running the body and moves the proof
across with `picked-same` after, which is erased and so does not disturb
the tail call. ASSUMPTIONS 150 has the details and the measurements:
400000 compile-time iterations in a 256KB stack against 60000
overflowing 8MB, benches unchanged within noise, `bootstrap.sh` green
and at its fixpoint.

`tests/comptime_tail.sl` guards it, and the `slc` from before refuses it
with a stack overflow. An earlier draft of this section said no test
could: that reasoning rested on the reference growing its stack too,
which it does not. The test decreases an erased `Nat` tied to a
non-erased binary counter by the prelude's `Numeral`, to the owner's
suggestion, so its 131071 iterations build no unary `Nat` and it costs
7MB with the extern `Nat` or without; counting a `Nat` down instead
wanted 80MB under `--no-extern`.

Open, in the session's estimation, none of it decided:

- The remaining half of the owner's ask. A *non-tail* call in
  interpreted code still holds a host frame, which is correct as the
  interpreter stands and can only be removed by making `eval` a machine
  over an explicit, heap-allocated continuation -- the shape
  TOOLING-WISHLIST 15 once wanted for the wrong reason. That is a much
  larger change than this one: the continuation would need its own
  indexed type and its own widening as the store grows, as `St` has.
  Whether it is worth it is the owner's call; the session's reading is
  that the tail case was the one carrying the practical cost.
- `eval-fuel` is still 1000000, two per interpreted call, so a
  compile-time loop now meets "out of fuel" at about 500000 calls rather
  than a stack overflow at 60000. Raising it costs nothing at runtime
  now that the stack does not bound such a loop, but the constant is
  user-visible and the session did not touch it.
- `lib/eval.ml` was not touched and needs nothing: its `eval` and
  `apply` both return a plain `value list`, so every tail position was
  already an OCaml tail call and the reference runs four million
  compile-time tail-recursive steps in a 256KB stack. This branch is
  `slc` catching up to that shape. An earlier draft of this section
  claimed the reference grew its stack too; it does not, and the
  measurement behind the claim was the unary printer, not the
  evaluator (ASSUMPTIONS 150).
- `apply-extern` returns `None` for `ExNatCmp` and `ExStrCmp`, so `slc`
  runs those two models at compile time where the reference runs the
  extern; `nat-cmp`'s model recurses once per unit of its smaller
  argument, in a match scrutinee, so `(nat-cmp 200000 200000)` alone
  overflows `slc`'s stack. Pre-existing and untouched here, and the one
  thing that bit the session while testing.

## `Program`, `Request` and `world-do` (one session, with the owner)

Done in both compilers, with DESIGN.md sections 8, 27, 32, 42 and 54 in
the owner's words: the prelude's `Program`, `Request` and `Stopwatch`,
the built-in `World`, and the special form `world-do`. What a later
session should know:

- `slc --interpret` performs requests as evaluation reaches them: every
  function of `self/eval.sl`'s evaluator threads a world of a type it is
  generic in, with a `Performer` for it (ASSUMPTIONS 188). The request
  handling (`perform-request`) and the answer helpers sit in
  `self/eval.sl` ahead of `perform-lvl`, since the closure the
  interpreter builds at that level is called from inside evaluation.
- Both compilers' call elaboration ends in a return handler a form uses
  without a callee (`call_returns`, `call-returns`), as `world-do` does
  and as the macro-world forms do. In `slc`, a
  call's `CCSame` mark is computed only in a non-erased position: built
  for every call, its `qshow` cost about 24% more allocation in `slc`
  compiling the part of its own sources both versions accept, and with
  the condition the two measured within noise of each other.
- `test/runtest.ml` extracts before it runs a test's final
  (ASSUMPTIONS 187): a run may update a unique Settled in place that the
  extractor would otherwise embed after the update.

Open, none of it decided:

1. A discrepancy between `slc` and the reference, not reduced: an
   erased call `(le-refl h1)` written as an erased argument inside a
   `def-unique` at a later level, `h1` the erased history from a
   `destruct` before it, was accepted by the reference and refused by
   `slc` compiling `slc` with "`_134395` was not in scope when level
   io-lvl was minted"; binding the proof once outside the closure
   satisfied both. Two smaller programs of the same shape, an erased
   call on an erased `let` binder inside a later-level `def-unique`,
   are accepted by both, so the trigger is finer than that.

## TODO: the diagnostic path is a reconstruction, not a proof (one session)

Not done; recorded so it is not lost. The notes a refusal carries about
numeral and character literals (`literal_notes` and `forced_notes` in
`lib/elab.ml`, `literal-notes` and `forced-notes` in `self/elab.sl`) are
worked out after the fact, on the error path, rather than reported by
the check they explain. For a failed check they walk the two canonical
sides to where they first differ (`differ`), which the session believes
can disagree with where the unifier actually failed: an occurs check, a
meta already solved, or a telescope `differ` does not enter. For a
branch left standing they compare each literal's canonical form before
and after the forcing trial, which infers what the trial bound rather
than observing it. So a note may, in principle, explain something other
than what happened.

The owner's direction is that the real fix is to prove, with the
language's own dependent types, that the explanation agrees with the
check; the session that wrote this did not have the context to attempt
it. A cheaper step the session considered and set aside is a recording
mode in the unifier, used only on the error path, which would make the
explanation observed rather than reconstructed; in `slc`, whose
unifier is pure, it would mean threading the record through every
unification function.

## The `at` redesign (one session, autonomous, with a subagent for `self/`)

Done, at the owner's direction: DESIGN.md sections 35 to 41 and section 44's
`array-unpluck`, in `lib/` and in `self/`, on the branch `at-redesign`.
The specification files were not changed;
ASSUMPTIONS 200-210 hold the readings this session made where the
proposal and AT_REDESIGN_REVIEW.md are silent, and the tests named there
and under `tests/at_*`, `slot_*`, `cell_many_*`, `cell_binder_*`,
`at_fn_*`, `at_match*`, `delegate_at*`, `vacant_slot` and
`array_unpluck` pin the behaviour. `self/README.md` says what the port
chose where the reference left it room.

What the owner still has to decide, none of it settled here. (Two
items that were here are resolved: the cell binder being optional,
decided in chat, is now DESIGN.md section 23; and the default slot of a
`(Slot)`-typed binder, which the code has and the spec does not, is now
BUGS.md 3, which names the line to revert.)

- Whether `tail`, `notail` or `delegate` on a skipped at-call should be
  the error it is now (ASSUMPTIONS 207) or be ignored (OPEN.md 21).
- OPEN.md 2's tier-1 list, and OPEN.md 18 to 20.

Done after that, in the same session: sections 35, 36 and 39
as the owner approved them, in `lib/` and in `self/` (the port by a
subagent), with `origin/at-redesign`'s `0af18f3` (a `(Slot)`-typed
binder is its own slot; the at-parameter rename fix) merged in at the
owner's request, the slot-self rule reaching erased binders too and
metas not (ASSUMPTIONS 201). Every entry now carries a slot at its own
erasure; an erased entry may be `at` any variable and the claim is
checked in every position; `erased` with `at`, and the `(at (f ...))`
assertion in an erased position, are refused; the argument for a
slot-named parameter is bound first (ASSUMPTIONS 211). `dune test`: 750
tests, 0 failures; `self/bootstrap.sh`: 709 matched, 829 refused, 0
failed, fixpoint reached. Worth knowing: the port's first version built
two of its new messages before testing their conditions, spelling a
keyword and naming a term through a scope walk on every call, and slc
took fifteen times as long on its own sources; both are built on the
failing branch now (rule 17), found with callgrind on
`bench/wide_scope.sl`.

Timing (rule 17) after the merge, slc on its own sources, five
alternating runs, minimum and median wall time, noise about 0.4s: the
branch's tip before this change (`fd851d4`) on the new sources 4.08s and
4.29s, 100 MB; the merged slc 4.17s and 4.56s, 113 MB; origin/main's on
its own sources 3.11s and 3.35s, 103 MB. This session reads the
difference from the tip as one entry per erased binder, inside the run
spread by minimum and about six percent by median; the note below on
representing slots as entries at all stands.

Timing (CLAUDE.md rule 17), each compiler on its own sources, five
alternating runs, minimum and median wall time, on a machine whose
noise was about 0.3s: origin/main's `slc` 2.70s and 2.96s; the ported
`slc` 3.29s and 3.80s, about 25 percent slower (3.34s and 3.48s again
after the `(Slot)` default landed, three runs). The reference compiling
the same sources: origin/main's 4.7s, this branch's 3.8s, faster
because a polymorphic comparison of terms over every opened object on
every rule added, more than half of the reference's run before, is an
integer comparison now (5ed34ef); `slc` indexes its opens and had no
such cost to recover. A differential profile of `slc` (callgrind, old
against new) puts the whole increase in proportional work: 72 percent
more fact-table inserts (one slot entry per non-erased binder, section 35), a
rule-out per placement (nearly every binder is placed, section 36's writers), a
larger live table for every lookup and for the GC, with no single hot
function and the `slots-in` pass at about one percent of the run. The
placement of a fresh slot is a direct rule rather than a forcing in
both compilers (25629a9, 81c8d64), which recovered a few tenths; what
remains is this session's reading of the cost of representing automatic
slots as fact-table entries at all. Closing it would mean another
representation, a slot class keyed by its entry and materialized only
when a `(slot-of x)` is canonicalized, which changes `self/core.sl`'s
table invariants and is the owner's to weigh against rule 17; recorded
as an unresolved regression, not as noise.
