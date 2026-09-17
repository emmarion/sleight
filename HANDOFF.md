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
and this branch does not touch it.

Open, none of it decided:

1. `bench/bench.sh`'s pinned sources no longer compile. `PINNED` is
   4fda15f, which predates 52d869a and 193f2fd changing the prelude's IO
   shape, so `self/main.sl` at that commit is refused against today's
   prelude, by the old binary as much as the new one. Re-pinning would
   change what the benchmark measures, so the session left it.

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
