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
- One non-syntax stuck remains, in `type-of-term` (see `mini/README.md`);
  the session judged closing it to need a type-preservation argument and
  did not attempt one. Whether the owner wants that argument, a change to
  `MintTele`, or the hole left as is, is an open question.
- `TOOLING-WISHLIST.md` logs the friction met writing `.sl` by hand at
  this scale, as the owner asked.
- The self-hosted `slc` (`self/`) accepts every file and all eight
  `tests/mini_*.sl` match the interpreter through it, but three of them
  (`mini_dependent`, `mini_axioms`, `mini_recursion`) overflowed the
  OCaml stack under the default 8MB limit, so `self/bootstrap.sh`
  reported them as failures. This paragraph used to place the overflow
  in `slc`'s compile-time interpreter; it was in the emitter, and the
  session below fixed it.

Next, in the session's estimation: the owner's verdict on the two relation
changes and on the `type-of-term` hole, then the items above.

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
