# Review of AT_REDESIGN.md

A reading of AT_REDESIGN.md by a Claude session, asked whether the
proposal is implementable today as stated and where it is ambiguous or
unsound. Written in the manner of SPEC-REVIEW.md: nothing here is a
design decision, every item is a reading of the text that may be
mistaken, and every suggested answer is a question for the owner. The
proposal's items are cited as A1-A14, DESIGN.md's sections as §, and
UNIQUE.md's as §U. Items here are numbered once and never renumbered
(CLAUDE.md rule 15).

What was checked. On the proposal's branch, which is `origin/main` plus
AT_REDESIGN.md: `dune build`, `dune test` (701 tests, 0 failures) and
`self/bootstrap.sh` (653 programs matched the interpreter, 787 refused
with the expected message, fixpoint reached, 2m15s). The at-database and
cell machinery of `lib/env.ml`, `lib/elab.ml`, `lib/term.ml`,
`lib/value.ml` and `lib/eval.ml`, the tests under `tests/at_*`,
`tests/cell_*` and `tests/slot_*`, ASSUMPTIONS 156-183 and `audit/`.
Eleven probe programs run against today's compiler, listed in part 7
with what each showed; three of them are quoted where a claim rests on
them.

## 1. Verdict, in brief

1. **Implementable today, with today's machinery, as far as this
   session can tell.** Every mechanism the proposal needs has a
   counterpart in `lib/` already: the fact table and forcing (§18) for
   slot equality, `Term.entry.place` for `at`, the `tail`/`delegate`
   normalizer (`Elab.check_marks`) for "erases to nothing", the
   `Delegate` proof and `delegate-of` for `AtFn` and `at-fn-of`, §19's
   open list for `open-at-fn`, `Prelude.null` for `vacant-slot`, and
   the caller-side word reconstruction of an `at` return
   (`Elab.location_var`) for omitted entries. Part 3 maps each item to
   the code it would change. No new theory is needed; the change is
   large but mechanical, and the self-hosted compiler gets simpler in
   one place (ASSUMPTIONS 169's separate location partition goes away).

2. **Three places where an implementer would have to invent semantics**
   (part 4): the meaning of "erases to nothing, or to a reordering of
   variables" (A9, A10); a recursive or mutually recursive at-function,
   whose own calls have no proof yet (A10); and what a call site checks
   and passes for a parameter written `at` (A3, A5), including how the
   `delegate` and `tail` checks read such a signature (A11). The owner
   answered the second in chat after the first version of this review
   (item 33). The rest of part 4 is wording that admits two readings.

3. **No unsoundness found in the stated core.** Part 5 states the claim
   this session believes A13.6 needs, lists every writer of a slot
   equality under the proposal and why each looks honest, and names the
   two restrictions that carry the weight: A8's "a cell at `many` mints
   its value only at `many`", and `slot-of` being read by binder rather
   than through an `is` rule. A7's "cannot happen" is slightly too
   strong as worded: it holds in a consistent context, and a probe shows
   today's unifier can force a type constructor equal to `Slot` in an
   unrefuted branch; the consequence is harmless either way.

4. **The owner's direction of subsuming `coerce` is already reachable
   at `unique` today.** An earlier draft on the branch (its A16, added
   in commit 8ed570d and removed in 7e49a39 as an unapproved reading)
   gave an `unwrap` over a list of a newtype as an at-function; written
   against today's rules over a *unique* list it is accepted, extracts
   to a traversal that stores and allocates nothing, and the call site
   reads the result off the argument's own word (part 7, P4). A8 adds
   the `many` case and A10 the licence to skip the traversal. That makes
   the soundness burden of A9/A10 small and well placed: skipping is
   transparent exactly when the body check is right (part 5, item 32).

5. **The largest practical cost is A8's mandatory cell binder at
   `many`.** An upper bound, counted syntactically: about 3000
   `match`/`let-match`/`comptime-match many` sites and 356 `else`
   branches in `self/`, 800 in `mini/`, 460 in `tests/`, 125 in
   `bench/`, 55 in `pal/` and 50 in `lib/prelude.sl` would gain a binder
   wherever the type has cells (part 6).

## 2. The model, as this session reads it

Stated so the owner can correct the reading before the rest is judged
against it.

6. A `(Slot)` value is a machine word, a pointer or an immediate, as
   §U10 has it. Every non-erased variable `x` has a word; its automatic
   slot `σx` (A2) names that word as a `(Slot)`-typed atom in the fact
   table, and `(slot-of x)` is a reference to `σx` (A6). `x at y` means
   `σx` and `σy` canonicalize to one atom: one word. `σx` is `at`
   itself because a slot's word is the slot (A2's "an automatic slot is
   `at` itself"), which is also what `slot-self` says of a user-bound
   `(Slot)` variable (A7). The null slot's word is whatever
   `cell-alloc` fills a vacant slot with.

7. Contents are governed by `is`, words by `at`, and the two stay
   separate because `σx` is a different atom from `x`: a forced `x is
   y` says nothing about `σx` and `σy`, and `σx is σy` nothing about
   `x` and `y`. This is §U8's "a forced rule between two ordinary atoms
   says nothing about location", carried over; `tests/cell_at_not_is_bad.sl`
   and `tests/at_is_independent_bad.sl` remain the tests of it.

8. The redesign's content, then, is to make the at-database a part of
   the fact table rather than a second union-find beside it: slot
   equality becomes ordinary canonical identity of §5's production 1
   (variables), forcing on slots becomes the ordinary atom-against-atom
   case of §18, and the scoping of a slot fact becomes §18's "a fact
   ends with the scope it was minted in" rather than §U8's "a
   membership ends with the scope that minted it". `SlotHolds v`
   becomes `(slot-of v)`, a fetch form in the manner of SUGAR.md 9's
   `level-of` and `matchable-of`, which already elaborate to a variable
   reference inside a type.

## 3. Is it implementable today?

Each entry names what exists and what would change; the session's
reading of `lib/` at commit ab64de0.

9. **Slot terms and the at-database.** `Term.SlotHolds` and the
   `~location` hook in `Term.map_vars` and `Env.canon` would go, with
   `Env.locations`, `Env.location_term`, `Env.at_merge` and
   `Env.at_equal`. A slot is then `Var σ`; equality is `equal (canon
   a) (canon b)`; a merge is `Env.add_rule`, or `unify_in ~force` where
   a forcing does it. `Term.entry.place` stays, holding a slot term (a
   `Bound` into the telescope for an earlier entry, a `Var` for a
   closed-over one), which is what it holds today under `SlotHolds`.
   Whether the automatic slots are literal hidden telescope entries
   (A2's mental model) or minted at binding time with `place` pointing
   at them is an implementation choice; the second is closer to today's
   data and keeps every zip over a telescope and its arguments as it is.

10. **Binding.** `Elab.open_tele`, `Elab.elab_tele` and the `let`,
    pattern and temporary binders (`bind_args` in `check_args`,
    `elab_head`, `scrutinee`) would mint `σ` beside each non-erased
    binder and record `place`. Today's `at_merge env (Var x) p` at
    those sites becomes a rule equating `σx` with `p`.

11. **Written `at` on parameters and earlier returns (A5).**
    `elab_tele`'s `places` flag and `place_scope` check (which refuse
    `at` on parameters and on sibling returns today,
    `tests/at_param_bad.sl`, `tests/at_sibling_return_bad.sl`) would
    admit them. For a return at an earlier return, `elab_call`'s
    reconstruction (`location_var`) must bind the target before the
    dependent entry; for a parameter, `check_args` must check the
    argument's slot against the target argument's and drop its code
    from `codes` (A3). Both are local changes.

12. **What reaches runtime (A3).** A call already omits an `at` return
    physically and reconstructs it (`elab_call`, `location_var`); a
    function body already projects its `at` returns away
    (`project_code`). A match's `at` annotation entries are produced
    physically by the branch today (`elab_match` does not project;
    probe V12 shows the extracted `let` receiving the branch's word), so
    A3 changes that: the `let` binding a match's result would
    reconstruct them as a call's are. Mechanical.

13. **Cells at `many` (A8).** `elab_match`'s `extra` is `smult = Unique
    && cells_allowed env mid` today; it becomes `smult <> Erased &&
    ...`, with `pattern_cell` binding the cell at the scrutinee's
    multiplicity (probe E1 shows the binder refused at `many` today).
    `cell-write` and the non-full-at invocation on a `many`
    cell need a copying code node: today `Value.CCellWrite` stores in
    place (`Eval`: `fs.(i) <- s`) and both extractors emit a store, so a
    `many` cell needs a `CCellCopy` or a flag, in `lib/eval.ml`,
    `lib/extract.ml` and `self/emit.sl`.

14. **At-matches and at-functions (A9, A10).** `result_tele` would
    recognize the `(at ...)` wrapper; the `def-fns` header parser the
    `at` mark; the body check would run `check_marks`'s normalizer
    (`norm`) on the post-erasure code with at-function calls and
    full-at invocations treated as erased, and require what is left to
    be renames and a final `values` of variables (part 4, item 24 says
    why that definition is a guess). The proof is minted as
    `Delegate`'s is (`witness` with a new `Prelude.atfn` type
    constructor), fetched as `delegate-of` fetches, and opened by
    adding a kind to `Env.opened` beside `` `Matchable ``. Skipping a
    call drops the `CApp` and keeps the argument uses.

15. **`slot-of`, `slot-self`, `vacant-slot` (A1, A6, A7).** `slot-of`
    joins `fetched` beside `level-of`; `slot-self` is a statement
    adding one rule under forcing and reporting a `Contradiction` as
    an error; `vacant-slot` names `Prelude.null`, which already exists
    anonymously and already prints as `(SlotVacant)` (ASSUMPTIONS 196).

16. **The self-hosted compiler.** About a hundred lines of
    `self/core.sl` and `self/elab.sl` mention the location partition
    (ASSUMPTIONS 169), which has erased invariants of its own. Folding slots into the fact
    table removes it and reuses the table's termination proofs
    (ASSUMPTIONS 93, 94) for slot unification, which this session reads
    as a simplification, not a cost. The bootstrap fixpoint must be
    re-established after the source rewrite of part 6, and CLAUDE.md
    rule 17 asks for slc timed on slc, since the fact table roughly
    doubles its non-erased entries.

## 4. Ambiguities and questions, by item

17. **A1.** "Treated like `Level`" is a partial likeness: `Level` is
    erased by kind, `Slot` is `many` and reaches runtime. Two things an
    implementer must know: the runtime word of `vacant-slot` must be
    the word `cell-alloc` writes into a vacant slot (`V.VToken` in
    both today), or a full-at invocation that passes `vacant-slot` into
    a `(Slot)`-typed field would be wrong; and whether `vacant-slot` is
    its own `at` (the prelude would say `(slot-self vacant-slot)`, or
    A2 would say so of the constant).

18. **A2, which binders.** "A `let` needs nothing of its own here" is
    read as: a `let` binder takes the `at` of the right-hand-side entry
    it binds (a forwarding `let` is at its source, a binder of a call's
    non-`at` return is at that return's automatic slot) and mints no
    slot of its own. The text could equally mean a fresh slot equated
    with the source. The two agree on every word and differ only in
    how many atoms the table holds; worth one sentence. Likewise
    unstated: fields of `let-match` and `comptime-match` (read as
    destructures, so slots as a `match`'s fields), the `else` binder
    (read as `at` the scrutinee, as the cell binder is), and a
    run-position binder, whose slot would be `Const` beside it.

19. **A2, "twice as many non-erased entries".** Read as a mental
    model only. If taken literally as hidden telescope entries, two
    `Fn` types written alike still compare equal under §5 (both carry
    the same hidden entries), and two that differ in a written `at`
    differ, as today (`place` is part of `Term.blank`). Nothing changes
    in type identity; saying so would save an implementer a worry.

20. **A3, two descriptions of one set.** "What reaches runtime is
    exactly the automatic slots" and "the runtime signature of a
    function is the non-erased entries without a written `at`" name the
    same words only under item 6's identification of `σx` with `x`'s
    word. Read together they are consistent; read apart, the first
    seems to pass a slot per entry *and* the entry.

21. **A3 and A5, parameters written `at`.** Unstated: what the call
    site does. This session's reading, from §U2a: each argument is
    bound first; for a parameter `y at x` the argument for `y` must
    have a slot canonically equal to the argument for `x`'s, and
    nothing is passed for `y`. Also unstated is the motivation; the
    one idiom found is item 27's `(many (Slot) s) (many A a at s)`,
    where the slot is the word passed and the value rides on it.

22. **A3 and A11, `tail` and `delegate`.** §9's pass-through check
    compares a `delegate` call's non-erased arguments with the
    function's non-erased parameters on the post-erasure code
    (`check_marks`). With parameters written `at` omitted, the branch's
    earlier draft read the check as judged on A3's runtime shape; the
    current text says nothing. An implementer must choose; the earlier
    reading seems the only workable one.

23. **A4.** Replaces `at_equal`, which is structural on location
    representatives today (`audit/M6`), with canonical identity; the
    self compiler's variable-only `at_equal` and the reference's agree
    again under the proposal. Scoping is unchanged in effect (item 8).

24. **A5, `r at s` for a `(Slot)`-typed `s`.** Decided (commit
    fc8b63a): the entry's `at` is `(slot-of s)`, not `s`. A reader
    would expect `r at s` to put `r` in the slot `s` denotes; under the
    decision that needs `(slot-self s)` first. Recorded as a trap, not
    an objection.

25. **A5, returns at earlier returns and parameters at closed-over
    variables.** Both refused today (probe E6; `tests/at_sibling_return_bad.sl`).
    The first needs the caller's `let` to bind the target before the
    dependent entry (item 11). The second is already §U8's rule for
    returns, and §18's "no fact outlasts an entry it mentions" keeps
    such a function inside the variable's scope, as §U8 notes.

26. **A5, the constructor-telescope ban.** "Neither `at` nor `slot-of`
    may appear in the telescope of a type constructor or a value
    constructor" is read as not forbidding `vacant-slot`, a plain
    variable, in a constructor's return type: today's `AllUninit`
    writes `(Uninit A (SlotVacant))` there and would write `(Uninit A
    vacant-slot)`. Nor is a `(Slot)`-typed field forbidden
    (`MaybeUninit`'s `Uninit`). Worth saying.

27. **A6, `slot-of` as a value.** The text says `(slot-of x)`
    "denotes" `x`'s at and "may appear in type-like positions". The
    prelude also uses a slot as a *value*: `array-pluck` writes
    `(Uninit _ (SlotHolds hd))` into a `many (Slot)` field and returns
    `(SlotHolds hd)` as an erased `(Slot)`. Read as: `(slot-of x)` in a
    non-erased position is a reference to the `many` binder `σx`, so it
    is an expression as any variable is, at `many`, and not a use of
    `x`. If so, a function `(many (Slot) s) (many A a at s) -> ...`
    with `(slot-self s)` in its body can write a full-at invocation
    into an abstract cell `(Cell C s)`, which today's §U10 idiom
    `(erased (Slot) s) (unique (Cell Pair2 s s) u)` cannot (inside the
    body `a`'s class is its own). That is a genuine new capability,
    worth naming in the proposal.

28. **A6, by binder.** `(slot-of x)` must resolve to `σx` by `x`'s
    binder, never by canonicalizing `x` first, or a forced `x is y`
    between two separately built equal values would make `σy` stand
    for `σx` and break item 7. Today's `SlotHolds` elaboration resolves
    by binder (`var env`, not `named`), so the habit exists; the text
    could state it, since it is what the whole separation rests on.

29. **A7, "cannot happen".** `σs is s` with `σs` a fresh atom
    contradicts only if `σs` or `s` already carries a rule to a
    constructor-headed term, and `Slot` has no constructors. The
    belief holds in every consistent context. It is not unconditional:
    probe E3 shows today's unifier forcing `(Foo) is (Slot)` for a user
    type constructor `Foo` in an unrefuted branch (two type-constructor
    atoms with unifiable signatures alias, §18), after which `(MkFoo)`
    is accepted where a `(Slot)` item is wanted. In such a branch
    `slot-self` could meet a contradiction. Since a true fact
    contradicting the facts in force refutes the branch, the owner may
    prefer that outcome to the error A7 specifies; the error is the
    conservative choice and costs only a refusal in dead code. The
    probe:

    ```scheme
    (def-adts $ (Foo : -> Type) enum (many MkFoo : -> (Foo)))
    (def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
    (def-fns _ $ (many weird : (erased (Eq Type (Foo) (Slot)) e) (many (Nat) n) -> (many (Nat) r))
      (let-match erased e (Refl _ _))
      (let ((unique c)) (cell-alloc MkBox))
      (let ((unique d)) (cell-write c (MkBox (MkFoo))))
      n)
    ```

    accepted; calling it with `(Refl Type (Foo))` is refused by the
    non-forcing check, so the branch is unreachable.

30. **A7, a possible default.** Every non-erased variable whose
    declared type is `(Slot)` could be its own `at` without a
    statement, `slot-self` remaining for a variable whose type only
    canonicalizes to `(Slot)` under branch facts. A question, since
    the explicit statement is uniform and the default is only a
    convenience.

31. **A8.** (a) The mandatory binder is the whole of part 6's cost.
    (b) A `cell-write` at `many` yields a fresh block no one else
    references. The text has it "itself at `many`"; in chat after this
    review's first version the owner decided it is at `unique`
    instead, so a write whose items are all `_` is how a shared block
    is copied into a unique cell. This session reads that as sound: the
    block is unreferenced, and a unique-labelled slot still holding a
    shared word cannot be filled `(at)` at `unique`, no unique variable
    being at a shared word but the newtype-wrapper aliases §U1 permits,
    which have no cell (audit Q4), so completing such a copy at `unique`
    supplies fresh unique values there. Open, by the same reasoning:
    whether a non-full-at invocation of a `many` cell, which also
    copies, may mint its value at `unique` where its position asks.
    (c) A non-full-at invocation of a `many` cell copies; the text
    should add that its result is not `at` the cell. A write followed
    by a full-at invocation is one copy, since the written slots and
    the unchanged field slots are then all in place. (d) At
    `many` the `else` binder is `many`, `is` and `at` the scrutinee,
    mandatory and inert. (e) A `comptime-match many` binds a `Const`
    cell. (f) Inside the prelude's extern model bodies the extern mark
    does not count (§U12), so `Nat`'s `(Succ k)` patterns in `add`,
    `divmod` and the rest gain a binder too.

32. **A9 and A10, "erases to nothing, or to a reordering of
    variables".** The phrase has no definition in the text; the
    branch's earlier draft had one and it was stripped. This session's
    guess, from what probe P4 shows a unique `unwrap` compiles to today
    (`let n = m in unwrap tl` in one branch, nothing in the other):
    after erasure, with `at` entries omitted, full-at invocations
    dropped, at-function calls dropped and at-matches dropped,
    `check_marks`'s normalizer leaves only `let`s binding variables to
    variables and a final `values` of variables, or nothing. Stores,
    allocations and calls of ordinary functions are what it excludes.
    Field loads must count as nothing too: P4's body reads `m` and
    `tl` out of the block before the rename, and once the at-call is
    dropped those loads are dead, so a match every branch of which
    erases to nothing erases to nothing itself, dispatch and loads
    included; item 37's coverage argument is what makes dropping the
    dispatch sound, and today's `norm` does not yet fold such a match.
    Whether a `match` whose annotation is `_` (SUGAR.md 2) counts as an
    at-match when the reused telescope is all erased or `at`, as P4's
    `let-match` is, is unstated; A9 requires the `(at ...)` spelling.

33. **A10, recursion.** Within a `def-fns` block the block's functions
    are `Dyn` (§34) and no `AtFn` proof exists yet, so a recursive
    at-function's own call is neither skipped nor provably skippable
    while its body is checked, and the body then contains a call and
    fails item 32. The mark on the `def-fns` line is syntactic and
    known throughout the block, so the natural rule is that a call to
    a sibling marked `at` counts as skipped by the mark, and that
    `(at (f ...))` on such a sibling is checked against the mark. The
    earlier draft said as much; the current text does not. In chat
    after this review's first version the owner proposed minting the
    `AtFn` proof when a header claiming `at` is elaborated, before the
    bodies, with a compile error if the body then fails the check.
    This session agrees: the proof's one use is to drop calls, the
    check runs regardless, nothing escapes a refused block, and letting
    the body's own recursive call count as dropped is an induction
    whose well-foundedness is §7's termination measure, mutual
    recursion within the block included. A call through the function's
    name would then be dropped as `delegate-of` fetches by name, and
    `open-at-fn` would serve first-class uses.

34. **A10, what the proof licenses.** An at-function's returns are
    all erased or `at`, so a first-class call with no proof opened runs
    a body that performs nothing and returns no word, and the caller
    reconstructs the `at` returns as it would anyway. Skipping is
    therefore transparent, and `AtFn` licenses an optimization rather
    than a reinterpretation. Stating this would make the soundness
    story of A10 one sentence: the burden is item 32's check alone.

35. **A10, extern at-functions.** In chat after this review's first
    version the owner decided that a function marked both `extern` and
    `at` has no FFI implementation: the marks are a promise, and the
    compiler emits a function that does nothing, for a call made where
    no proof is opened. This session reads that as needing no separate
    dummy: the model body, having passed item 32's check, already
    compiles to a function returning no word, so compiling the model
    is the dummy; `Ffi.claim_fn` would skip such a function, and §41's
    conservativity holds vacuously. What `extern` buys such a function
    is §U12's cells over an extern type inside its body, not an
    implementation.

36. **A10, `open-at-fn` and forcing.** The open is keyed by `f`'s
    canonical atom, as §19's opens are by constructors, and a branch
    forcing `f is g` would make an opened proof for `g` cover `f`.
    That is justified exactly as §18's forcing is: two function atoms
    equate only in a branch that a proof of their equality reached.

37. **A12.1.** The relaxation of §12's one-real-branch rule matters
    for a `many` at-match on a *union*, refused today though no
    dispatch would happen; for an enum at `many` the rule never bites.
    The skipped dispatch is sound because coverage is still checked:
    every constructor is present or refuted, and each present branch
    proves the retyping for its own constructor.

38. **A12.5 and §U14.** Tier 1 "drops `at` annotations from
    telescopes" and makes the at-database vacuous; under A3 an `at`
    now decides what is passed, so dropping it must re-insert the
    word, turn at-functions into functions whose no-op bodies run, and
    give `slot-of` (a copy of the word), `slot-self` (no-op) and
    `vacant-slot` tier-1 meanings. The follow-up list should say so.

39. **The token `at`.** It now marks a telescope entry, wraps a
    full-at invocation, marks an argument `(at)`, wraps an at-match's
    annotation, marks an at-function on its `def-fns` line, asserts an
    at-call and annotates a delegate. The full-at and at-call wrappers
    share a spelling and are told apart by the head's type (§4's tier
    1 habit), and the at-match wrapper sits in a position only a
    telescope can fill, so no reading is ambiguous to the elaborator.
    CLAUDE.md rule 10 permits distinct names if the owner wants them;
    none is proposed here.

## 5. Soundness

40. **The claim A13.6 needs, as this session would state it.** In
    every context whose code runs, two `(Slot)` terms that canonicalize
    to one term denote one machine word. Nothing is claimed about
    contents: a unique value consumed and rewritten through its cell is
    at the same slot with different contents, and `is` alone speaks to
    contents (item 7). Every place that saves work rests on this claim
    and on nothing else: a skipped store in a full-at invocation (§U9),
    an omitted `at` return or parameter (A3), a skipped at-function or
    at-match (A9, A10).

41. **Writers of slot equality under the proposal, and why each looks
    honest.**
    - *Definitional*: the elaborator's own plumbing, the same writers
      §U8 lists today (a destructure's field at the cell's slot, a
      newtype's field at its wrapper, `share`, `coerce`, a call's `at`
      return, a forwarding `let`, a unique `cell-write`'s result at
      its input, an invocation's result at its cell, the `else` and
      cell binders at the scrutinee). Honest exactly when the runtime
      plumbing agrees, which is an implementation obligation already
      carried and tested (`tests/at_erased_word.sl`, ASSUMPTIONS 157,
      164, 171).
    - *`slot-self`*: honest by item 6, a slot's word being the slot.
    - *Forcing*, on `Cell` against `Cell` or on a user type indexed by
      `(Slot)`: honest in the sense §18 gives every forced fact, that a
      branch's facts hold in the branch that runs; for an erased
      scrutinee it rests on §10's consistency, as every erased forcing
      does. This is today's situation too (ASSUMPTIONS 183, audit Q5,
      `tests/at_slots_force.sl`); the proposal neither widens nor
      narrows it. `Slot` having no constructors, forcing never refutes
      on slots and nothing relies on two slots being distinct, which
      the stripped draft also observed and this session agrees with.
    - *`slot-of` by binder* (item 28) is what keeps `is` out of it.

42. **What cashes a slot equality, and the restriction each rests on.**
    - A full-at invocation at `unique`: as today.
    - A full-at invocation at `many` (A8): a reinterpretation of a
      shared block at a type built from the arguments' types, the
      `coercible-ctor` step of §38 without a proof object. Sound as a
      coercion is: by item 40 the fields hold the arguments' words, and
      each argument's type types its word. The load-bearing restriction
      is "mints its value only at `many`": a unique result at a shared
      word would be a unique alias of it, which today is refused
      (probe E2, `` `x`, declared `many`, used at unique ``) and must
      stay refused. A write or a non-full-at invocation at `many` copies,
      so the shared block is never written. One consequence to confirm
      deliberate: the same word is then live at two types that may
      differ in erased indices, as `tests/unique_typestate.sl` does at
      `unique`; at `many` that grants no new logical power, since a
      constructor application with any erased index was writable
      already.
    - At-function and at-match skipping: transparent given item 32's
      check (item 34), so the check is the whole burden. Its shape is
      §9's `tail` check, which the implementation already trusts.

43. **Probes that looked for a hole and found the existing rules in
    the way.** A slot value stored in data, read back as an abstract
    slot and unified against a cell's type works and stays honest (P7
    of part 7, output `1`). Two slots holding one unique word and both
    filled from it is refused by `conflicting non-erased uses` (P7b).
    A return promised `at` a `many` parameter at `unique` is refused
    (E2). None of these is changed by the proposal.

44. **Where the argument leans on §10.** Everywhere forcing on an
    erased scrutinee does: a false slot fact minted in an executing
    branch would corrupt memory rather than merely prove something
    false, which the stripped draft also noted. KERNEL.md's
    interpreter-trust obligation applies unchanged: a lying evaluator
    could fake the discriminant a `comptime-match` reads and so the
    facts downstream, slot facts included.

## 6. The cost of the source rewrite

45. Counted with `grep` over the branch, so an upper bound: every
    `(match many`, `(let-match many`, `(comptime-match many` and
    `(else` is listed whether or not its type has cells (extern types
    outside the prelude's models and newtypes have none, so `Nat`,
    `String`, `Array`, `U8`, `Char`, `Copy` and `MaybeUninit`
    destructures are exempt).

    | area | match many | let-match many | comptime-match many | else |
    |---|---|---|---|---|
    | `lib/prelude.sl` | 21 | 27 | 2 | 0 |
    | `self/*.sl` | 1503 | 1518 | 8 | 356 |
    | `tests/*.sl` | 260 | 115 | 85 | 39 |
    | `mini/*.sl` | 174 | 625 | 0 | 100 |
    | `pal/*.sl` | 15 | 41 | 0 | 8 |
    | `bench/*.sl` | 124 | 0 | 0 | 120 |

    `SlotHolds` and `SlotVacant` occur 4 times in the prelude, 69 in
    `self/` and 108 in `tests/`; `(at (` 27 times and `(coerce ` 116
    times across the three. The `coerce` sites do not change in
    version one (A12.4).

46. The rewrite is mechanical, and every edited test still has its
    `; expect:` and `; error:` lines to check it against; `self/`'s
    rewrite is checked by the bootstrap fixpoint. The edits are also
    where CLAUDE.md rule 5's succinctness and the proposal's uniformity
    pull apart: a `_` binder on every `many` pattern of a plain enum is
    noise to a reader. Whether the binder could be optional at `many`,
    or asked for by a mark on the match, is a question for the owner,
    not a recommendation; rule 8 says ergonomics is no goal.

## 7. Probes run

Each is a small program run against the reference compiler at ab64de0;
P4 was also run through `--extract` and through `slc`. "Refused" quotes
the message's operative words.

- **E1** A `match many` pattern with a cell binder: refused, `expects 1
  binder, got 2`. A8 is new behaviour.
- **E2** `(many (Nat) x) -> (unique (Nat) r at x)` with body `x`:
  refused, `used at unique`. Item 42's restriction holds today.
- **E3** Item 29's program: accepted; its call with `(Refl Type
  (Foo))` refused by `type mismatch`.
- **E4, E5** `SlotHolds` of a telescope binder, in a parameter type
  and in a `many` match's scrutinee type: refused, `cannot name a
  telescope binder`. A6 would admit `slot-of` there.
- **E6** A return at an earlier return: refused, `must name an
  argument or a closed-over variable`. A5 admits it.
- **P4** The earlier draft's `unwrap`, over a unique list whose head
  type is a newtype with a `unique` field:

  ```scheme
  (def-fns _ $ (many unwrap : (subterm unique (UL (Meters)) ms) -> (unique (UL (Nat)) ns at ms))
    (let-match unique ms (UCons _ m tl u) ((UNil _ u) (at (u _))))
    (let-match unique m (MkMeters n))
    (let ((unique r)) (tail (unwrap tl)))
    (at (u _ n r)))
  ```

  accepted; prints `(UCons _ 1 $ UCons _ 2 $ UNil _)`; extracts to a
  function whose one branch is `let n = m in unwrap tl` and whose other
  is `()`, called as `let _ = unwrap ms in ms`; `slc` agrees. Two
  earlier attempts failed on this session's mistakes (a `many`
  newtype field under a unique destructure, a `many` literal in a
  unique position), both refused correctly.
- **P7** A `(SlotHolds n)` stored in a `(many (Slot) s)` field, read
  back by a `many` match, used as a `cell-alloc` slot and the cell
  invoked with `n`: accepted, prints `1`.
- **P7b** Two slots of one cell holding one unique `x`, `x` moved
  through an `at` return to `y`, then `(c (at) y (at) x)`: refused,
  `conflicting non-erased uses`.
- **V12** A `unique` match whose annotation is `(((Box) r at x))`,
  bound by a `let` inside a function body, its one branch `(u 2)`:
  accepted, prints `2`; the extracted body is `let y = (match x with
  ... -> (let cell = x in (store; cell))) in ...`, the branch returning
  the word and the `let` receiving it (item 12).
- **P8** Part 8's pattern over a one-element toy array: a unique cell
  `(A1 (Un _ (SlotHolds x)))` holding the element `x`'s slot under a
  union newtype, `x` mutated in place to `x2` through its own cell, the
  toy array's cell reinvoked `(at (c (In _ x2)))`: refused at the
  invocation, `` `at` argument 1 is not in its slot's location class ``.
  Nothing today connects the destructured slot's *value* to the
  element's *location*, which is what `slot-self` would do.
- **P8b** The same with a plain store, `(c (In _ x2))`: accepted,
  prints `1`.

## 8. The owner's motivating example: pluck, mutate, put back

The owner gave this example in chat after the first version of this
review; the sketches below are this session's, written against the
proposal's rules as read in part 2, and checked by no compiler, since
nothing implements them.

47. **The pattern.** An element of an array (a jagged array's row, or
    any unique value mutated inside an outer array) is taken out with
    `array-pluck`, mutated in place through its own cells, and put back
    by an at-function whose call is erased, so that putting a value
    back costs nothing. Today's `array-pluck` returns the array with
    the element's word still in place under `Uninit`, an erased `(Slot)
    s`, and an `ASet` proof naming `(Uninit A s)`; the owner notes the
    signature must then say that `s` is exactly the slot of the value
    returned.

48. **Pluck's signature, as this session reads it.** With A6,
    `slot-of` may name an earlier return entry, so the separate slot
    return goes away and the proof names the value's slot directly:

    ```scheme
    (def-fns _ $ (many extern array-pluck : (erased Type A) (erased (Nat) n)
        (unique (Array (MaybeUninit A) n) a) (subterm many (Nat) i)
        (erased (MaybeUninit A) m) (erased (ANth (MaybeUninit A) n a i m) nth) ->
        (unique m is v) (unique (Array (MaybeUninit A) n) r at a)
        (erased (ASet (MaybeUninit A) n a i (Uninit A (slot-of v)) r) p))
    ```

    This cannot be written today: `SlotHolds` may not name a telescope
    binder (probe E5, `tests/slot_binder_bad.sl`), which is why today's
    `s` is abstract. In the body, `(Uninit _ (slot-of hd))` is a
    newtype application at `(slot-of hd)`, whose word is `hd`'s, so the
    one store today's body makes is of the word already there and may
    be marked `(at)`: pluck then reads a word and stores nothing, which
    is what the FFI already does (ASSUMPTIONS 167). It is not an
    at-function, since it returns the element.

49. **The put-back, as an `extern at` function** (item 35):

    ```scheme
    (def-fns _ $ (many extern at array-unpluck : (erased Type A) (erased (Nat) n)
        (unique (Array (MaybeUninit A) n) a) (subterm many (Nat) i) (unique A x)
        (erased (ANth (MaybeUninit A) n a i (Uninit A (slot-of x))) nth) ->
        (unique (Array (MaybeUninit A) n) r at a)
        (erased (ASet (MaybeUninit A) n a i (Init A x) r) p))
      (let-match unique a (ACons _ _ hd tl u) (absurd (ANil _ _) nth))
      (match many i (at (((Array (MaybeUninit A) n) r at a)
                         ((ASet (MaybeUninit A) n a i (Init A x) r) p)))
        ((Zero _)
          (let-match erased nth (NthZ _ _ _ _) (absurd NthS))
          (let-match unique hd (Uninit _ s))
          (slot-self s)
          (values (at (u _ _ (Init _ x) tl)) (SetZ _ _ _ _ _)))
        ((Succ i1 _)
          (let-match erased nth (NthS _ _ _ _ _ _ q) (absurd NthZ))
          (let ((unique tl3) (erased p1)) (array-unpluck _ _ tl i1 x _ q))
          (values (at (u _ _ hd tl3)) (SetS _ _ _ _ _ _ _ p1)))))
    ```

    In the `Zero` branch `nth` forces `hd is (Uninit A (slot-of x))`,
    which refutes `Init`; the newtype destructure puts `s` at `hd`
    (§U9); `(slot-self s)` makes `s` its own slot; and `s is (slot-of
    x)` was forced, so `hd`'s slot is `x`'s. `(Init _ x)` is at `x`,
    being a newtype application at its non-erased argument, so the
    invocation is full-at and stores nothing; the `Succ` branch's call
    is an at-call and `tl3` is at `tl`. The body then erases to nothing
    under item 32's reading: the outer destructure's loads are dead,
    the at-match is dropped, and what remains is renames. `x` is
    consumed once on each path.

50. **What the example needs from the proposal**, item by item: A6's
    `slot-of` on a telescope binder, an earlier return in pluck and a
    parameter in the put-back; A7's `slot-self` on the slot a newtype
    destructure hands out, which is exactly where today's rules stop
    (P8 against P8b); §U9's newtype rules unchanged; A8's binder on the
    `Nat` patterns inside the extern body; A9's at-match with dead loads
    (item 32); A10's header-minted proof for the recursive call (item
    33) and the `extern at` reading (item 35). The caller also needs an
    erased lemma from `ASet` to `ANth`, routine and not in the prelude,
    and relies on `(slot-of v)`, `(slot-of x)` and `(slot-of x2)`
    canonicalizing equal through the newtype destructure of `v` and the
    `at` return of the mutation, which they do under part 2's reading.

51. **Two observations.** The array holds the element's pointer under
    `Uninit` while the element is live and unique: that is already so
    today (the prelude's comment above `array-pluck` calls it a
    potential leak until the element is overwritten) and is harmless, a
    `(Slot)` being inert (§U10); overwriting index `i` meanwhile drops
    the pointer and with it the `ANth` fact the put-back needs, so a
    stale put-back is refused by typing. And the example is the
    strongest case this session has seen for item 30's default: every
    `slot-self` in it is on a `(Slot)` that a destructure has just
    bound. A jagged array, `(Array (MaybeUninit (Array B m)) n)`, is the
    same pattern with `array-place` as the mutation.
