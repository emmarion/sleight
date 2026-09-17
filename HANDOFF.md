# Handoff

Work in progress handed from one session to the next. Written by a
Claude session; nothing here is a design decision.

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
  the term's, pushed as the next equation, which neither `lib/` nor
  `self/` does (their forcing assigns without a type check, and their
  atom-against-atom case unifies signatures only where both are formers,
  ASSUMPTIONS 89); `Refine` and `Contradict` take one equation, the
  scrutinee against the pattern, the type equation following from it.
  So `mini/` is now stricter than the reference: whether `lib/` and
  `self/` should follow, and the sentence section 18 of DESIGN.md would
  need, are for the owner. For the function side this moved the stuck
  into unification (`RefStuck`, propagated as the `Stuck` constructors
  of the walk's result types, which only `Force` mode can be); closing it
  would need the invariant that every application head in play has a
  former's type, carried through the elaborator and unification, in the
  session's reading. `mini/preserve.sl` holds groundwork for that.
- `TOOLING-WISHLIST.md` logs the friction met writing `.sl` by hand at
  this scale, as the owner asked.
- The self-hosted `slc` (`self/`) accepts every file and all eight
  `tests/mini_*.sl` match the interpreter through it, but three of them
  (`mini_dependent`, `mini_axioms`, `mini_recursion`) overflow the OCaml
  stack inside `slc`'s compile-time interpreter under the default 8MB
  limit; `ulimit -s unlimited` fixes it, and the fuel-based `mini/`
  before this change overflowed the same way, so it is a limit of `slc`
  rather than a regression. `self/bootstrap.sh` runs with the default
  limit and will report these three as failures.

Next, in the session's estimation: the owner's verdict on the `Sided`
merge and on the `type-of-term` hole, then the items above.

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
term as DESIGN.md section 3's entries do).

## The head-type stuck closed by `TyApp` and `ValApp` (one session)

Done, at the owner's word after a chat comparison of the two routes
above: `Term`'s one `App` became `TyApp head params args` and
`ValApp head params ret args`, DESIGN.md section 5's productions 2 and 3
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
  as section 8 says. New erased fields on these rules (the params
  read, `hps`/`tps`/`aps`) are the only other change to the relations.
- `tests/mini_term.sl` and `tests/mini_unify.sl` build the split terms
  by hand; every test and the bootstrap pass.

Next, in the session's estimation: the owner's verdict on the `Sided`
merge, then the metatheory (MINIMAL.md's list and the agreement above).
