# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision, and the claims
below that `lake build` does not check are that session's reading, which
may be mistaken.

## Where things stand

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's; a test's `; needs:` files are read
with it under `--shared`. At the last run 322 tests were accepted with
OCaml's value, none mismatched, 474 refusals agreed, and 80 + 89 were
refused as unsupported; 23 tests OCaml accepts are refused, 11 of them
for a `_` the inference does not solve. No test the OCaml suite
refuses is accepted. Four tests it accepts time out at ten seconds,
among them `comptime_tail.sl`, which finishes in about a minute, and
`extern_tail.sl`, which ran out of memory on one session's machine.

`lean/prelude.py` regenerates `lean/prelude.sl` and
`lean/prelude-full.sl` from `lib/prelude.sl`, keeping the `extern` marks. It takes several minutes, because it runs
`--full` on every prefix.

`unique` is done, checked by the elaborator (`lean/README.md`).
`delegate-of`, `coercible-of` and the `Delegate` type are done, with the
stripped run passing only non-erased arguments and results and binding a
delegate to its target (`lean/README.md`). One consequence for the
elaborator: a run-position call whose callee's type it does not know
records no view of the callee's erasures (`Core.call`'s `ve` is `none`),
and the stripped run then uses the callee's own; inference fills it in
before checking, and the checker requires it.

## Under way: the machine run (the owner's direction, from chat)

The owner's goal, given in chat: a run stripped not only of erased code
but of everything the language says costs nothing at run time, proved to
end in the same values as `RunS`, and so, through `eval_sound`, as the
full run. That is OPEN.md 2's first step. In that run, on the plan
agreed in chat:

- an `at` parameter or return is not passed; its word is read from its
  target's;
- an at-function's call and an at-match are skipped;
- a cell invocation at `unique` writes its block in place, `cell-write`
  at `unique` stores in place, and `cell-alloc` allocates;
- `share`, `coerce`, the placings and `slot-of` are renames;
- a slot's value is a word: a block's address, or an immediate.

Arrays, `Bytes` and `Placed` come after cells, `at`, slots and
at-functions.

What the theorem needs, on this session's reading:

1. Section 15's use discipline checked in the core checker rather than
   the elaborator alone, closures included: a `def-fns` closure does not
   capture a `unique` entry at unique (the elaborator refuses that today,
   "`def-fns` cannot capture a unique value at unique"; the checker does
   not), and a `def-unique` consumes what it captures. The owner asked in
   chat that the checker disallow the first.
2. An ownership invariant: a block written in place is reached by
   nothing the rest of the run reads non-erasedly, through the current
   frame, the callers' frames or a live closure, except through the cell
   being written.
3. Slots mean words: every slot fact the checker holds (`at` promises,
   forcings, `slot-self`, the writers of DESIGN.md section 36) is true of
   the words, or reading an `at` entry back from its target gives the
   wrong value. That is OPEN.md 3, which the owner believes holds;
   forcing through a type indexed by `(Slot)` is the case it names. The
   owner confirmed in chat that this lemma is part of the task. Should it
   need the checker tightened, that is the owner's to decide.
4. An at-function's body and an at-match's branches erasing to nothing,
   checked in the core rather than the elaborator alone.

Stages, each committed once it builds and `test.sh` passes:

1. Core forms for what the new run treats specially: a cell invocation
   into a block, a pattern's cell binder naming its scrutinee's block,
   `cell-alloc`, `cell-write`, and `at` entries marked as not passed.
   `RunS` reads them as it does today, so the existing proofs stand.
2. Items 1 and 4 in the checker.
3. The machine run: a heap, words, skipped calls.
4. The agreement theorem, with items 2 and 3 as its lemmas.

## Next, none of it decided

0. **Native arithmetic, one proved extern at a time.** The owner's
   plan, from chat: no extern's native code is ever trusted as an
   axiom; each extern gets native code only with a Lean proof that it
   agrees with its model, and a model that is not the proved one runs
   with a warning (WARNINGS.md 1). Done: `add`, `nat-cmp`, `mul`, `sub`,
   `divmod`, `nat-mod` (`Minimal/Native.lean`). The templates are the
   prelude's elaborated bodies at their fixed places; a change to those
   prelude forms means regenerating them (a session dumped the groups
   with a small Lean script and pasted them in). Next, by a session's
   ranking: `nat-halve`, then `shl`/`shr`, the bitwise ones, and last
   the `u62-*` ones. Numerals are numbers from the start (`Prim.num`),
   but the proofs that `numeral-of`, `prove-literal-lt` and `unary`
   ask for are still unary derivations the checker types, so a numeral
   one of them names is capped at 100000; lifting that would mean
   proving, for each relation, that a generated derivation has its type,
   once the prelude's declaration is found to have the expected shape,
   as `Prog.natOK` does for `Nat`.
1. **A signature that mentions an earlier function of its block** other
   than through `level-of` (section 53). `delegate-of` in a type names the
   proof that `def-fns` mints after its block, so it is refused in the
   block's own signatures.
2. **What `at`, slots and cells still lack** (`lean/README.md` lists
   what is done): `Placed` (section 66; `placed-slot` needs a slot
   semantics the core does not have, and the placings are `def-prim`s
   with non-erased returns), arrays and bytes (cells of extern types
   inside extern bodies; `inExtern` is never set), `World` and
   `Program`, a cell binder in `comptime-match`, the full-`at`
   invocation counted as erased by the `tail` check, a non-erased
   at-match on a union, and the gaps the README's slot item lists.
   The user asked that mutation state be left until everything else is
   done, so the non-mutation items here come first.
4. **The full evaluator on the prelude.** `u62-modulus` is `2^62` in
   unary, so `prelude-full.sl`, which `--full` and `--unchecked` load,
   leaves out it and everything over `U62`. `prelude.sl` has them, since
   the stripped run never computes it.
5. **A result typed with the program's own entries** is checked as a
   result of any type (`ArgsTy.anyCons`), so `checked_runs` says nothing
   of its type. The printer finds such types separately (`retTypes`,
   untrusted), since the stripped run holds a newtype's value as its
   field and printing needs the type.
6. Settled head dispatch reads a head's type through the facts of
   top-level `let-match`es on `Eq` proofs only, a stand-in for
   canonicalizing against the facts of the innermost run position.
7. `comptime-match` and the checker's known values do not look through
   a newtype: on one, `comptime-match` is a `case` the stripped run takes
   without looking, and `BranchOK.fixedOut` is refused.
8. `dump-context` shows a type only where the elaborator knows it, which
   is not the case for a `let` binder written without one.
9. Macros and handles (sections 62 to 65), which need `at` for `MacroWorld`.
