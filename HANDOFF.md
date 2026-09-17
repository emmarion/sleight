# Handoff

Work in progress handed from one session to the next. Written by a
Claude session; nothing here is a design decision.

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
a Const or a final reaches. Measured with an instrumented reference
extractor before the change, reachable values against the blocks
ASSUMPTIONS 148 counts: 1570 against about 20000 for `slc`'s own sources,
and 197, 181, 227 and 126 against 665800, 157418, 162987 and 44797 for
`mini_recursion`, `mini_axioms`, `mini_dependent` and `mini_elab`. Max
value depth was 226 and 13-19 respectively.

Things the session had to change course on, recorded so they are not
rediscovered:

- `deref` was deleted rather than kept. A call's result is `Dyn`, so
  calling it destroys the subterm relation, which is what stopped
  `rope-walk` and the printer recursing structurally. Both now match
  through `MkRef`/`MkValue` and need neither the store nor a fuel, and
  `ref-suffix`, erased, replaces what `deref` computed.
- Post-order DFS alone does not order the output. A group's body also
  names other Consts, and that edge is not in the value graph; today's
  emitter got the ordering from address order instead. Emission is now in
  stamp order, which orders every edge, since anything a block names was
  allocated before it. Adding those edges to the trace was considered and
  set aside: they jump to arbitrary Consts, so the walk would stop being
  structural.

Open, none of it decided:

1. The stamp sort is an insertion sort, quadratic in the blocks emitted
   (4372 when `slc` compiles itself, 2668 for `mini_recursion`). Whether
   the traced order is near-sorted, which would keep it cheap, was not
   measured. An MSB-first trie over the bijective spelling would sort in
   one structural pass, in-order traversal being sorted because a shorter
   bijective spelling is always the smaller number; a balanced tree and a
   merge sort were the other two the session weighed, the latter needing
   a measure `merge` does not have.
2. The trace itself descends by value depth rather than being tail
   recursive. The owner asked for tail recursion where a reasonable
   measure exists; the session did not find one that is both erased and
   proof-free, the seen set bounding the walk rather than any structure.
3. The `-weaken` wrappers in `heap.sl` are marked TEMPORARY. The owner
   asked that widening be an erased proof and a `coerce` at the call
   site, a call to a `many` wrapper extracting to a real call where the
   inline `coerce` extracts to nothing; that pass is not done, and the
   nested call sites need hoisting for it.

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
