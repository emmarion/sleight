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
  reject: `Subst`'s `SubBeyond` and `Unify`'s `Sided` merge of the
  left/right twin rules. The function-side `Oriented` lost its `OrStuck`.
- One non-syntax stuck remains, in `type-of-term` (see `mini/README.md`).
  A later session, funded to close it by a preservation argument, found
  the argument false as the relations then stood: a program reached the
  stuck (`tests/mini_untyped_rule.sl`, with the reading of why in its
  header). The cause was `ETValCtor` accepting any type as a `ValCtor`
  former's return, which `lib/` refuses (ASSUMPTIONS 70 and 80); the owner
  had item 80 restored in `mini/`, which refuses the program. Neither
  `lib/` nor `self/` equates a variable's type with its term's when
  forcing assigns a rule (only atom-against-atom unifies signatures, and
  only where both are formers, ASSUMPTIONS 89); the owner's hunch is that
  under item 80 that equation is derivable, so `UAssign` needs no change.
  Unverified: the session's reading is that verifying it is exactly the
  typed-rules lemma the preservation argument needs.
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

Next, in the session's estimation: the owner's verdict on the two relation
changes and on the `type-of-term` hole, then the items above.
