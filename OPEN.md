# Open questions

These are questions about the language that DESIGN.md does not answer.
Each is stated as a question. Nothing here is a decision. Section
references are to DESIGN.md.

## Soundness and invariants, unverified

1. Consistency. Is the language sound with `Type : Type` and no
   positivity restriction (§10)? Termination is carried by the level
   and subterm order (§17), and types never compute (§9). The owner
   holds that it is sound. No soundness argument has been written.
2. Erasure conservativity. Take any program that compiles and collapse
   `unique` to `many`: a `UniqueFn` becomes an `Fn`, every cell
   operation becomes an allocation, `share` and `slot-of` become the
   identity, `at` entries become ordinary entries, and at-functions and
   at-matches become functions and matches whose bodies run. Does the
   result still compile and run to the same values? Then collapse
   `erased` to `many`, give `Level` and the proof types some non-erased
   representation, and replace each `coerce` by the value its proof
   names. Does the result still compile and run to the same values? In
   both steps the collapsed multiplicities would stay as inert markers
   that the unification of §7 still compares. Neither step is verified.
   The second step presupposes the first: collapsing erasure alone
   would turn an erased mention of a consumed unique value into a
   second use. The collapsed markers are kept so that every refutation
   and `open-absurd` of the original program survives.
3. Slot equality. What must the soundness claim for slots (§35) be,
   and does it hold? In particular, a user type indexed by `(Slot)` can
   make a forcing merge two slots in a branch that is not refuted.
   The owner believes it is sound.
4. Facts from stored values. A `comptime-match` trusts the evaluator
   (§29). Should a reference evaluator inside the checker arbitrate
   runs that produce facts, so that a wrong evaluation cannot produce a
   `(False)` token through an erased field?
5. Should the irreflexivity of `Subterm` and the strict creation order
   of `Predates` be stated as invariants? Both appear to be necessary
   for consistency.
6. Are the `is`-declared fields of a `comptime-match` or `let-match`
   and forced index unification one mechanism?

## Design directions not taken up

7. A unified lexicographic-decrease proof: one proof structure that
   represents the whole order of §17 as a nested disjunction, so that a
   call need not name the decreasing argument when which argument
   decreases is known only through an erased computation.
8. Macros. Open: macro termination beyond a global expansion limit,
   and hygiene, perhaps by letting `Raw` carry entry references as well
   as names, with a reference to an entry that is out of scope being an
   error rather than merged into the current scope.
9. Compile-time evaluation inside a body: a `comptime` form, and a
   `hoist` form `(hoist L body)` whose definitions count as made just
   before `L`, so that the factory pattern of §57 could be written
   inline. Where such a body would run, and what the fact table would
   need at each `def-lvl`, are undecided.
10. A rewriting engine without the atom requirement: rules from
    expression to expression rather than from atom to expression (§7).
    What would that do to the third failure mode of §7, to the occurs
    check, and to the self-consistency of the table?
11. Should the outer declaration syntax `name : signature` put the name
    last, as telescope entries do (§3)? Should `let` put its binders
    last?
13. Should `_` be accepted as an entry of a `values`, or as the
    scrutinee of a `let-match` (§50)?
14. A source-level way to declare extern types and functions, in place
    of the prototype's fixed table (§42). What should guarantee that an
    implementation agrees with its model, beyond the requirement stated
    there?
15. Should an `else` refine the scrutinee so that it excludes the
    listed constructors?
27. Should `List` declare `head` and `rest` `unique` (the owner's
    remark)? A construction at `many` would still take them at `many`,
    and one at `unique` would own its whole spine.

## `at`, slots and cells

16. May a `Coercible` be created from two variables that are in one
    slot (`at-coercible`), and under what restriction? As last
    proposed, the form is a use of both variables, a unique one being
    given back as a fresh binder `is` and `at` it, so that neither is
    consumed: a consumed variable's contents may have changed while its
    slot has not. As proposed it is potentially unsound, and it is not
    implemented.
17. Should there be a runtime comparison of two slots that answers with
    evidence when they are equal (`slot-eq`), with a compiler free to
    always answer that they differ? The owner's tentative view is that
    the unequal answer should carry no evidence: a refutation would be
    false wherever a compiler answered that two equal slots differ.
19. Should the function in an `(at (f ...))` call be allowed to be
    erased, as a `Coercible` proof is?
20. What becomes of `coerce`, `Coercible`, the `coercible-*` forms and
    `Delegate` once the `at` system can express what they express?
    The owner's tentative direction is for the `at` system to subsume
    them in stages, deleting them if that works out, with the prelude
    gaining further `extern at` functions over arrays.
    Should a `Cell` for the constructor of an extern type exist outside
    the body of an extern function (§43)?
21. Should `tail`, `notail` or `delegate` on a skipped at-function call
    (§39) be an error, as it is now, or be ignored?
23. Should a shadowing sugar replace rebinding under the same name,
    `(let ((unique x)) (f x))`, which is the current idiom?
24. The names of the forms above, and of `vacant-slot`, `slot-self`,
    `at-fn-of` and `open-at-fn`.
29. Should `at` be allowed on a `let` binder as a check (§19, §36)? A
    `let` binder takes its place from its value, so an `at v` there
    could declare nothing new; it could only assert that the value is
    already at `v`, checked after the binding as a return's promise
    is, in the way `(at (f ...))` asserts a skipped call (§39). Today
    it is refused.

## Argument temporaries

25. Is the anonymous binding of an argument (§15) `Const` in run
    position, as the binders of a run-position statement are (§29)? As
    a session read the code, both implementations make it so for an
    argument and for a computed head, so its value is computed at
    elaboration and embedded, which is how an `at` word is read from it
    after the call. They leave `Dyn` the temporary of a match
    scrutinee, of a `cell-match`, and of an argument bound only because
    a later entry names its slot. A computed head is still not
    dispatched as a special form, since dispatch looks at the head as
    written (§6). Is that what §6 and §28 mean, and should the
    scrutinee, `cell-match` and slot-named temporaries be statements
    too, and so `Const` in run position?

## Literal proofs

28. Should `prove-literal-lt` derive its `Lt` rather than assert
    it, through the bijective base-2 spellings of its two numerals? The
    idea is an order relation on `Bin` and a lemma, appended to the end
    of `lib/prelude.sl`, from that relation and the two literals'
    `Numeral` proofs to the `Lt`, at a cost that would seem to grow
    with the spellings' depth rather than with the numbers. Should a
    character literal's bound (§45), asserted today, then be derived the
    same way, from `(prove-literal-lt c 256)`, `c` its code, carried along an
    erased `(Eq (Nat) u8-modulus 256)` proved once at the end of the
    prelude? A session sketched that `Eq` from `u8-modulus-pow2` and
    the `Numeral` proof of `256` (eight `PS` steps over `DS`, then
    `pow2-fn`) and the checker accepted it; that proof's unfolding
    would need a place whose facts cannot escape, so that `256` stays
    opaque, and it is not known whether the prelude can hold a literal.
    Open as well: one proof for `256` or a general lemma for spellings
    of a power of two.

## Warnings

30. The unused-binder warning (WARNINGS.md 10) counts a function's
    recursive calls to itself as references, so a nested function that
    only calls itself is not reported. The owner's preference is that
    such calls not count; doing so is deferred. Open with it: whether
    calls among the functions of one `def-fns` block, none of which is
    referenced from outside the block, should count either.
31. The unused-binder warning does not count a use of a name as an
    annotation token, such as a local binder holding the special form
    `many` and written where a multiplicity goes, so such a binder is
    reported as unused, and the recommendation, if followed, breaks the
    program. A use as the head of a form does count. slc reads
    annotation tokens without returning an environment, so it has
    nowhere to record the reference; the reference leaves the case out
    to agree with it. Open: whether to restructure that lookup in slc
    so that these uses count.
32. Should the unused-binder warning check a binder that a macro
    expansion (DESIGN.md section 19) produced? Today one that the
    expansion gives a position is checked, and its warning points at
    that position, often the macro's call.
33. Should a type be allowed to be marked `newtype` when a constructor
    has a field written `at` beside its one non-erased field? Today
    §21 and §36 forbid it, and both compilers refuse it
    (`tests/at_field_newtype_bad.sl`). Such a field stores nothing
    (§36), so the constructor seems to hold a single real word, which
    is what a newtype is represented as (§33); whether that reading
    holds, and what the destructure and the facts of §37 would be for
    such a constructor, has not been worked out. Open: whether to
    allow it and under what restriction, or to keep the rule. It may
    bear on item 20.
