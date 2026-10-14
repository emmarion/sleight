# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision, and the claims
below that `lake build` does not check are that session's reading, which
may be mistaken.

## Where things stand

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's; a test's `; needs:` files are read
with it under `--shared`. At the last run 327 tests were accepted with
OCaml's value, none mismatched, 474 refusals agreed, and 85 + 97 were
refused as unsupported; 19 tests OCaml accepts are refused, 7 of them
for a `_` the inference does not solve. No test the OCaml suite
refuses is accepted. Three tests it accepts time out at ten seconds:
`comptime_tail.sl`, which finishes in about a minute, `extern_tail.sl`,
which ran out of memory on one session's machine, and
`mini_preserve.sl`. One refusal reads as an internal error rather than
a verdict, `palindrome_manacher.sl`'s "unbound entry 1099511627776";
no session has looked into it.

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

Progress: stage 1 is done (`Chk.mark`, `FnDef.atf`, and the `Mark.uq`,
`Mark.uqScr` and `Mark.rebind` modes); stage 2's use discipline is
`usesCore` (`Minimal/Uses.lean`), which the runner requires, though no
theorem uses it yet and `Checked` does not include it; "erases to
nothing" is not yet in the core. `Minimal/Machine.lean` holds a first
machine run (`RunM`): a heap, cell invocations at unique written in
place (`Prog.reuse`), `cell-alloc` allocating, and `at` entries,
skipped calls and slots not yet treated specially; and `MDec`, a
machine value standing for a stripped one.

`Minimal/MachineSound.lean` holds the pieces of the agreement theorem
proved so far, all without `sorry`: what a built runtime term's machine
value reaches and owns (`rt_build_ok`, `list_ok`), the `ret` case
(`machine_ret`), and the frame lemmas for a step that runs a
sub-computation and binds its results (`MFrame.split`, `MFrame.bind`).
Ownership (`Spine`, `WO`) is keyed on the full run's value as well as
the stripped one, so that a unique newtype wrapper around a shared
field (16's `coercible-sym`) owns nothing. `Live`, `Own`, `MFrame` and
`MOut` take the context's erasure map and ask nothing of an erased
entry.

`Minimal/MachineRun.lean` states the theorem one core form at a time:
`MRun P b G ru rets c ρ vs` says that wherever the uses pass accepts `c`
in `G` and the stripped run of `c` ends, the machine run from a frame
standing for the stripped environment ends too, in an `MOut`. `GOK` is
what the machine state owes the pass's context: the pending mark, the
unique scrutinee, the rebinding, `uq` below the context's length, no
filling, no ghost. Proved so far, without `sorry`: `machine_seq`,
`machine_defLvl`, the erased call, match and primitive
(`machine_callE`, `machine_mtchE`, `machine_primE`), and the checks
that change nothing the machine reads (`machine_chkPlain`, `machine_cm`,
`machine_uq`, `machine_uqScr`, `machine_skip`). Each takes the steps
after it as hypotheses (`MRun` of the rest, and for `seq` the body's
`Sim`), so the final theorem is an induction like `eval_sound`'s that
discharges them from `CoreTy`, `EnvOK` and `eval_sound` itself. A
static lemma, `usesCore_uq`, says that every use at unique the pass
records names an entry of `uq` or one made after the context; the
`seq` step needs it to tie a use of a new binder to `ents`.

Left, on this session's reading: the non-erased call (the callee's
frame, the closure's captures and `Group.caps`), the non-erased match
and `case` (the scrutinee's view, branch contexts, the cell binder),
the non-erased primitive including the pending marks (`reuse`, `alloc`,
`cellOf`, `write`, where the in-place writes and `Res` come in), the
rebinding of an `else` scrutinee, `defFns`, `open-adt` (`machine_same`
covers its success; on failure the core continues with `.dead`, which
no stripped run reaches), and the assembly.

The pass was tightened on the way, each change checked by a full
`compare.sh` run that changed no verdict (327 accepted with OCaml's
value, none mismatched, 474 refusals agreed): `use` refuses an index
out of range or erased; a `seq` body and an `else` branch start with no
cell to take and no pending rebinding; the code after a `cell-of` mark
has no cell to take; `UCtx.next` marks as unique only entries the
statement itself made; and a group's recorded captures must each pass
`use` where the group is defined.

On this session's reading, the agreement theorem cannot be proved by
induction on `RunS` alone: at a call, the caller counts an argument's use
by the callee's type as the caller sees it, while the callee's body is
checked against its own telescope, and only typing (`VTy`) ties the two.
So the plan is a theorem by the same induction as `eval_sound` (on
`eval`, under `CoreTy` and `EnvOK`), relating machine words to the full
run's values directly, with an ownership invariant: in each frame, the
blocks a `unique` entry that may still be used at unique owns (its top
block, and those of its unique-labelled fields) are reached by no other
entry the rest of the frame reads, nor by a caller's; and a closure is
read only through the entries its bodies use non-erasedly, which
`usesCore` computes. The closure value's stand-for relation will need
those reads rather than `G.ers`, which `MDec.clo` uses for now.

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
