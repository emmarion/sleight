# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision, and the claims
below that `lake build` does not check are that session's reading, which
may be mistaken.

## Where things stand

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's; a test's `; needs:` files are read
with it under `--shared`. At the last full run 422 tests were
accepted with OCaml's value, 532 refusals agreed, and 19 + 62 were
refused as unsupported; 7 tests OCaml accepts are refused, and one test
OCaml refuses is accepted (`macro_mint_numeral_of_bad.sl`, item 9).
`mini_axioms.sl` took about 20 seconds on this branch, at the edge of
the walk's 20-second limit; a session suspects the closures that slot
unions wrap around the rule maps (`Ctx.bindSlot`), not measured. The runner does not implement `cell-same`, so the prelude
leaves out `nat-same` and the other functions DESIGN.md section 42 builds
on it (item 9).

The tests OCaml accepts and this runner refuses, with a session's
reading of why:

- `at_match_union.sl`: a non-erased at-match on a union newtype with
  several real branches. The reference emits no code for it. Here the
  reader refuses it, and so does the core checker ("a match with an
  erased discriminant has more than one real branch"): the stripped run
  holds a newtype's value as its field, so nothing chooses the branch.
  DESIGN.md sections 21 and 40 allow it: an at-match on a union under
  a `many` or `unique` scrutinee does not dispatch, and its `at` entries
  are read back from their targets; the reference refuses the same
  match written without `at`. `lean/SLOTS.md` proposes how the Lean
  model could support it.
- The macro tests that `lean/README.md`'s macro item lists as not
  supported, and `macro_gensym_eq.sl` and `macro_mint_settled.sl`,
  which pass a `match` with a `_` annotation as an argument.

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

## The machine run

The owner's goal, given in chat: a run stripped not only of erased code
but of everything the language says costs nothing at run time, proved to
end in the same values as `RunS`, and so, through `eval_sound`, as the
full run. That is OPEN.md 2's first step. On the plan agreed in chat:

- an `at` parameter or return is not passed; its word is read from its
  target's;
- an at-function's call and an at-match are skipped;
- a cell invocation at `unique` writes its block in place, `cell-write`
  at `unique` stores in place, and `cell-alloc` allocates;
- `share`, `coerce`, the placings and `slot-of` are renames;
- a slot's value is a word: a block's address, or an immediate.

Arrays, `Bytes` and `Placed` come after cells, `at`, slots and
at-functions.

`Minimal/Machine.lean`'s `RunM` does the third and fourth items: a heap,
cell invocations at unique written in place (`Prog.reuse`), `cell-alloc`
allocating, and a call building only its non-erased arguments. `at`
entries, skipped calls and slots are not treated specially yet. The
core marks what the run treats specially (`Chk.mark`, `FnDef.atf`), and
section 15's use discipline is `usesCore` (`Minimal/Uses.lean`), which
the runner requires. `machine_main` (`Minimal/MachineAsm.lean`) proves
the agreement for what `RunM` does, without `sorry`.

Not done, on this session's reading:

1. Slots mean words: every slot fact the checker holds (`at` promises,
   forcings, `slot-self`, the writers of DESIGN.md section 36) is true of
   the words, or reading an `at` entry back from its target gives the
   wrong value. That is OPEN.md 3, which the owner believes holds;
   forcing through a type indexed by `(Slot)` is the case it names. The
   owner confirmed in chat that this lemma is part of the task. Should it
   need the checker tightened, that is the owner's to decide.
2. An at-function's body and an at-match's branches erasing to nothing,
   checked in the core rather than the elaborator alone.
3. A `def-unique` consuming what it captures, checked in the core.

`Minimal/MachineSound.lean` holds the base lemmas: what a built runtime term's machine
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
filling, no ghost. One lemma per step: `machine_seq`,
`machine_defLvl`, the erased call, match and primitive
(`machine_callE`, `machine_mtchE`, `machine_primE`), the checks that
change nothing the machine reads (`machine_chkPlain`, `machine_cm`,
`machine_uq`, `machine_uqScr`, `machine_skip`), a non-erased primitive
that no pending mark changes (`machine_prim_inert`, with `prim_val`
for every non-erased primitive but `coerce` and `coerce_val` for it), a non-erased `mtch`
that takes a constructor's branch or its `else` (`machine_mtch_fld`,
`machine_mtch_els`), `case` in its three forms (`machine_caseE`,
`machine_case_fld`, `machine_case_els`, `machine_caseN`), the many
cell marks (`machine_markMany`), the pending marks at unique
(`machine_markU` for `reuse` and `write`, which moves the target's
top block into the reserved set, `machine_cellOf`, `machine_alloc`),
and a primitive under a pending mark (`machine_prim_pend`, with
`machine_prim_reuse` for a cell invocation written in place,
`machine_prim_cell` for `cell-of`/`cell-write`, `machine_prim_alloc`;
`machine_prim_inert` is its corollary), the takeover of a unique
scrutinee by an `else` binder (`machine_rebind`, and
`machine_rebindSkip` when the mark does not apply), and a successful
`open-adt` (`machine_opn`; a failed one is ruled out by
`EnvOK.openFail`), `defFns` (`machine_defFns`, with `clo_vals` for
the closures' values), and the caller's side of a non-erased call
(`machine_call`, which takes the callee's run and its results'
ownership over the call's own uses as a hypothesis); toward the
callee's side, `args_val`, `MDec.clo_inv`, `WO.clo_inv`,
`clo_vals_many` (a non-unique sibling closure reads only captures
recorded at many and owns nothing) and `callee_frame` (the frame a
callee's body starts in, built from the caller's frame for the call's
own uses, the closure's captures, the sibling closures and the built
arguments, given which captured entries the body reads and owns,
together with how that frame's owned and live blocks sit in the
caller's) and `callee_out` (the body's results' ownership in the
caller's terms, through the spreading of the outputs), and
`call_body`, which puts these together into what `machine_call` asks
of the callee for a closure that is not a delegate, given the body's
`MRun` and uses in its own context, which captured entries the body
reads and owns, and how arguments and outputs are spread.
`callee_frame` is `body_frame`, a frame for any body whose entries
before its parameters are described by facts about their words
(`MDec`, feet and spines inside the callee's, `WO`, disjointness), with
those facts supplied from a closure's captures and siblings.

A call through a delegate (`Minimal/MachineDeleg.lean`) is a call of
its target on the machine and in the stripped run, and of the
delegate's own body in the full run. `dele_body` gives `machine_call`
the target's run: the delegate's body runs, by its `MRun`, from a frame
whose entries before its parameters are erased but the target's, which
holds the callee's word (`body_frame`), and `walkM1`, the machine
counterpart of `walk1`, finds in that run the target's run from the
same heap to the same heap, its results those of the delegate's body.
The heaps match because the machine builds only a call's non-erased
arguments (`RunM.call` masks the rest by the call's erasures, as the
compilers evaluate no erased argument), and because `delegWalk` admits
in a delegate's body only primitives that allocate nothing
(`Prim.inert`: renamings and constants) and a return of variables.
`dele_sim` is the stripped frame for the same body, shared with
`eval_sound`. `GOK.pend` says the block a pending mark names is
reserved and is not the unique scrutinee's; `cellTy_tok` says an entry
of cell type has full value `tok`. Frames and results carry a set
`Shr` of blocks no unique spine reaches and no reserved block is in,
which a result may reach: an `else` branch puts there the part of its
scrutinee's foot outside its spine, which the binder that takes the
scrutinee over shares, and `GOK.rebind` asks for it. A closure reads
the entries its group captures (`Prog.rd`) and owns those captured at
unique (`Prog.rdU`), both per function: a non-unique function reads
only the non-unique captures and owns nothing, and a unique delegate
owns what its target owns (`Spine.dele`, `WO.dele`). Each takes the
steps after it as hypotheses (`MRun` of the rest and of the branch, and
the body's `Sim`), so the final theorem is an induction like
`eval_sound`'s that discharges them from `CoreTy`, `EnvOK` and
`eval_sound` itself. A static lemma, `usesCore_uq`, says that every use
at unique the pass records names an entry of `uq` or one made after the
context; the `seq` step needs it to tie a use of a new binder to
`ents`.

In `machine_mtch_fld` the scrutinee's value is built, its fields are
bound as the branch's entries (`MOut.fields`, then `MFrame.bindR`), and
under a unique match the scrutinee's top block, which no field reaches,
is left reserved for the branch (`Res`), which is what `GOK.uscr` asks
for a cell binder to take later.

`coerce` rests on how the compilers make coercion sound, an account a
session read and the owner agreed with in chat. A `coerce` emits no
code: the result is the source's word, in the interpreter, the
extractor and `slc` alike. Uniqueness has one runtime effect, in-place
mutation: a cell write or invocation at `unique` writes the block
itself, where at `many` it copies first, and the `Array`/`Bytes`
externs that take their array at `unique` write the OCaml array in
place. So soundness is that memory reachable from a `unique` holder
through unique-labelled fields has no other live reference (§15, §22),
and a coercion keeps that because of its sides (§33, §34):
- `(Unique)` to `(Unique)` consumes the source, and the two ends reach
  the same memory through unique-labelled fields;
- a `(Shared)` target cannot mutate;
- `(Shared)` to `(Unique)` arises only from `coercible-wrap` of a
  many-labelled field, whose unique wrapper hands the field out at
  `many`;
- `coercible-trans`'s equal middle sides keep a shared value from being
  carried into a unique-labelled field.

In the Lean model, "reach through unique-labelled fields" is `Spine`.
`Twin P a b` says two full values have the same `Spine` and equivalent
`WO` over every heap, machine word and stripped value, and `NoSpine P
a` that `a` has no `Spine` at all. `VTy.coer` carries `CoerOwn` of the
proof's sides and ends: a `Twin` when both sides are `(Unique)`, and
`NoSpine` of the `(Unique)` end when only one side is
(`coercible-trans` may pass through a `(Shared)` middle). `tm_sound`
proves it for each proof former (`CoerOwn.refl`, `.symm`, `.trans`,
`.shared`, `.wrap`, and `Twin.ctor` for `coercible-ctor`), and for
`delegate-of` from `DeleOK`, which records it for each delegate pair of
the context (`dele_own`). `coerce_val` is `prim_val`'s conclusion for
`coerce`: the machine builds the source, and when the result is unique
the target side is `(Unique)`, so `MOut.twin` moves the source's
ownership to the target, or the target owns nothing.

A delegate pair in a context (`Ctx.deles`) carries its two sides,
fixed when `def-fns` makes it, as on this session's reading the
reference does (`sharing_of_fn`), so a later refinement of the target's
type does not change them. `Group.sidesOK`, in the checker's `GroupOK`,
says of each delegate of a non-ghost group: a non-erased delegate to a
`UniqueFn` is itself unique, an earlier target has a function type, and
a target in its own block is not unique. On this session's reading the
reference refuses the same programs (a `many` function cannot use a
captured `UniqueFn` at unique, and `sharing_of_fn` asserts a function
type). A unique delegate closure owns what its target owns (`Spine.dele`,
`WO.dele`); the uses pass's `UCtx.defOK` has its group capture an
earlier target at the target's own multiplicity when the delegate is
unique and at `many` otherwise, which `clo_vals` uses to put that
ownership among the group's owned captures.

`coercible-wrap` needs the constructor's signature written out, as
`coercible-ctor` does; in the reference, on this session's reading,
`ctor_type` reads a `ValCtor`'s telescope, which is always a list of
entries. `ProgOK` records that no
constructor field is both erased and unique, which the reference cannot
express (an entry has one multiplicity), and `checkProg` checks it.

The uses pass refuses a non-erased `coerce` whose sides are not
canonically `Unique` or `Shared`, and one whose result is used at
unique when its target side is `(Shared)`, which on this session's
reading is what the reference does (`sharing_mult`).

The assembly takes the checker's success on a core (`checkCore … = .ok
…`) as its hypothesis rather than an arbitrary `CoreTy` derivation.
On this session's reading typing is relational (a primitive's, a
callee's or a scrutinee's type is not unique), so the context a
`CoreTy` derivation gives the rest of a core need not be the one the
pass used, while the checker computes those types with the same
functions as the pass (`checkPrim`, `checkTm`, `checkArgs`,
`shapeOf`).

`Minimal/MachineAsm.lean` holds the assembly. `MSound P μ ρ cnt c` is
the statement for one core: from the checker's success on `c` in
`G.Γ`, `EnvOK`, the level and measure facts, and `CloOK` of the
environment, an `eval` of `c` that succeeds gives `MRun` for `c`, and
`CloOK` of the results when the context is ghost or the pass accepts
`c`. `machine_sound` proves `MSound` for every core by induction over
`eval`, without `sorry` (`#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`). `machine_main` states it for the
program: when the checker and the uses pass accept `P.main`, the
machine's run of it from the empty heap ends where the stripped run
does, with the results' ownership and values in an `MOut`. Its only
hypothesis about the program besides the checker's and the pass's
success is `ProgOK`. The induction carries, for a non-erased primitive,
`MSound` of the code after it, which a `rebind` mark needs.

One lemma per form: `MSound.ret`, `.seq`, `.prim`, `.defLvl`,
`.defFns`, `.chk` (every check and mark; `open-adt` through
`checkCore_opn`; and a `rebind` mark with the primitive after it),
`.mtch` (erased, a listed branch, `else`), `.case` (erased, newtype, a
listed branch, `else`, the newtype's `else` through
`machine_caseN_els`) and `.call` (erased, through `call_body` for a
closure, and through `dele_body` for a delegate). `CloOK` asks every closure for a certificate (`Cert`): the
group's typing and the checker's success where the group was defined,
always; and, when the group is not ghost, the uses pass's result there.
A group's ghost flag is its defining context's (`GroupOK`), so the
uses pass runs at every `def-fns` of a non-ghost group. `Cert` is what
the `call` step applies the induction to: `checkGroup_body` gives the
checker's success on the callee's body, and `call_setup_ctx`, run in
the certificate's context, gives its environment. `checkBranches_live`
inverts the checker's success on a listed branch, and `match_setup`
says which context it picks for the branch, so the two can be matched.
`mtch_setup`, `call_simb` and `call_step` are the parts of `eval_sound`
the machine steps share; `call_step` also gives the stripped
environment after a non-erased call for whichever run of the callee's
body is given.

Beside counting uses, the pass requires: `use` refuses an index
out of range or erased; a `seq` body starts with no cell to take and
no pending rebinding, and an `else` branch with no cell to take; the
code after a `cell-of` mark has no cell to take; `UCtx.next` marks as
unique only entries the statement itself made; a group's recorded
captures must each pass `use` where the group is defined; and an `else`
branch's binder is taken over from the scrutinee without a use only
under a unique match of an entry, and is otherwise an ordinary use of
the scrutinee; a newtype branch and an erased `case`'s `else` have no cell
to take; a cell binder is taken only under a unique match (`cellOf`
needs the unique scrutinee, and the reader emits the mark only
there); and an in-place write or invocation at unique needs a cell
type (`cellTy`), whose entries' full values are `tok` (`VTy.opq`) so
that their blocks are owned through `Spine.cell`/`WO.cell`; a group
that captures an entry at unique has at most one unique function; and
a delegate's target, when it is an entry before the group, is among
the group's captures, at many when the delegate is not unique, and
when it is a sibling, that sibling is not unique; a function body
starts with no pending marks, unique scrutinee, rebinding or cell to
take, whatever the context the group is defined in; a function body
uses no unique function of its own group, its own closure included
(the reader leaves a unique function's name unbound in its body, and
OCaml treats it as erased); and a group's recorded captures name the
same entries at the same uniqueness as its bodies' uses.

The agreement theorem is by the same induction as `eval_sound` (on
`eval`, under `CoreTy` and `EnvOK`) rather than on `RunS`, because, on
this session's reading, at a call the caller counts an argument's use
by the callee's type as the caller sees it, while the callee's body is
checked against its own telescope, and only typing (`VTy`) ties the two.
It relates machine words to the full run's values directly, with an
ownership invariant: in each frame, the blocks a `unique` entry that may
still be used at unique owns (its top block, and those of its
unique-labelled fields) are reached by no other entry the rest of the
frame reads, nor by a caller's; and a closure is read only through the
entries its bodies use non-erasedly (`Prog.rd`), which `usesCore`
computes.

## Next, none of it decided

The owner chose to model slots as words, with a heap in the full
semantics, as `lean/SLOTS.md` lays out; that work is on the long-term
branch `claude/slots` and its per-stage sub-branches, and takes
precedence over the order below until it is back to `main`'s parity.

The owner's tentative order, from chat: (a) the two soundness gaps,
a handle used against its multiplicity (item 9, step 5, done) and item 5
(since deferred);
(b) item 13; (c) items 2 and 11, mutation included, and the two `at`
tests listed above (on this branch only `at_match_union.sl` is left); (d) the rest of item 9, step 5; (e) item 12;
(f) item 9, step 4.

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
   what is done): a non-erased at-match on a union, and
   the gaps the README's slot item lists.
4. **The full evaluator on the prelude.** `u62-modulus` is `2^62` in
   unary, so `prelude-full.sl`, which `--full` and `--unchecked` load,
   leaves out it and everything over `U62`. `prelude.sl` has them, since
   the stripped run never computes it.
5. Deferred by the owner. **A result typed with the program's own entries** is checked as a
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
9. Macros and handles (sections 62 to 65), which `lean/README.md`
   describes. The plan a session proposed and the owner agreed to
   resume, in order:
   1. Done: `elabProgram` reads whether the program ends in a statement
      after its last top-level form is expanded.
   2. Done: a match on `MacroWorld` or `Gensym` outside the prelude is
      refused, as the reference refuses it for want of a `Matchable`.
   2a. Done: a handle made by `settled-type` splices as a name the
      reader resolves to the handle's type. The reader's checker context
      for top-level entries is stepped after inferring the form's holes,
      so it holds the type of an entry the reader inlines.
   3. Done: the prelude is regenerated for `main`'s latest.
   3a. Deferred by the owner: `cell-same` (DESIGN.md section 68). Its `EONonErased` carries a
      `JMEq` of two cells from their slots being equal, and the core
      here knows nothing of locations (two slots are one only when they
      canonicalize to one entry), so the checker has no rule giving that
      equality. A session's reading is that supporting it would mean the
      proofs tracking slots as locations (live cells whose slot entries
      canonicalize to one entry being equal values), not a case beside
      the existing ones. The call's `at` requirement is already checked
      by the core, as for any at-function. `lean/SLOTS.md` proposes how
      to support it, with at-matches on a union newtype and mutation;
      not adopted.
   4. Not started, and to be proposed to the owner first: make
      `MacroWorld` (and `Gensym`) opaque again, as DESIGN.md has them,
      with the macro-world primitives a core form answered by an oracle,
      as `world-do` is. Here they are data types without constructors,
      which types the primitives as functions with refuted bodies.
      DESIGN.md section 65 lets an erased macro world escape an
      expansion (`mint-settled-erased`), which the reference accepts;
      with an empty `MacroWorld` the checker would refuse such a
      program (or a new core rule for it would not be provable), so
      the encoding cannot express the design there.
   5. Then: positions (a macro sees `NoPos`), handles as run-time values
      (a new term; `settled-mult` and `settled-value` outside a macro's
      function),
      `read-file`, `mint-settled-erased`, a minted macro bound by a
      `let`, and `settled-eq` on terms the reader's canonicalization
      does not make identical.
      `mint-settled` of a number or a string gives that literal's
      handle here, where the reference mints a fresh opaque constant:
      so `macro_mint_nat_distinct.sl` finds two mints of 3 equal, and
      `macro_mint_numeral_of_bad.sl`, which the reference refuses
      (`numeral-of` takes a literal), is accepted. A session's reading
      is that the value is still the literal's, so this accepts more
      than the reference, not a false result.
10. A computed head inside a type other than a variable or `(share x)`
   whose settled value is a `Special` constructor: types are elaborated
   by `elabTm`, which runs no statements.
11. An `at` naming an entry of an enclosing telescope that is not a
   `(Slot)`. One naming a `(Slot)` entry, as a constructor field's
   function type written `at` a sibling slot field does
   (`tests/at_field_fn_sibling.sl`), is supported.
12. **The `Program` driver's requests.** `Prog.perform` does
   `WriteOut`, `WriteErr`, `ReadLine`, `ReadRemaining`, `GetEnv` and
   `GetCwd`; the others, the confinement of file requests and output,
   and the reference's command-line flags for them are not done, and
   `--full` does not drive a `Program`. The theorems take the oracle as
   a hypothesis (`Prog.OracleOK`); a session's reading is that the
   driver, running `runAM` in `IO`, is the run they describe for the
   answers it gave, which is not proved.
13. **Decisions the reader makes by name, ahead of elaboration.** A macro
   can rebind a name or produce a form, and an alias can rename a
   special form, so a decision about what a form is belongs where the
   elaborator handles it, with the scope there. These are still made by
   scanning syntax for names first, and an alias, a shadowing binder or
   a macro's output can mislead them:
   - Literals are interned where the elaborator needs them: a lookup
     that finds one missing throws a marked error carrying what it needs
     (`throwNeed`), and the nearest interning site restores its state
     and elaborates again with it (`retrying`). The scan
     (`internLits`) remains as the first guess. Slots are core terms
     and need no minting.
   - Still decided by scanning: `dropFinal` under `--shared`; the
     `let` analyses `returnsBinders` and `renamesOf`; and the scan that
     declares `World`.
   - Probed against the reference's test runner: a needs file ending in
     a macro call that expands to a `let`, or in an alias of `values`
     with no arguments, is refused by both. The scan that declares
     `World` sees the prelude's own mention of it, so with the prelude
     it is always declared, and without it there are no macros.
   - `returnsBinders` diverges: in a body
     `(let ((many y)) (tail (id x))) (v y)`, with `v` an alias of
     `values`, the reference accepts the `tail` and this runner refuses
     it. The reference checks `tail`, `notail` and `delegate` after
     elaboration, on the erased code with renaming lets and lets that
     return what they bind folded away (`check_marks` and `normalize` in
     `lib/elab.ml`); here they are checked while elaborating, against a
     syntactic reading of the rest of the body. `lean/TAIL.md` proposes
     checking them on post-erasure code and proving tail calls as a
     theorem; not adopted.
   A related difference, also older than macros: `values` in a call's
   argument position splices its values into the call's arguments here,
   so `(nat-add (values 1 2))` gives 3, while the reference refuses it
   (`nat-add` expects 2 arguments, got 1); likewise through an alias of
   `values`.
