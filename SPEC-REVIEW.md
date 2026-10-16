# Spec review: bugs and ambiguities

A review of DESIGN.md as a handoff target: could an implementer build
an interpreter or compiler from it without inventing core semantics?
Written by a Claude session, not by the owner. Every item is a reading
of the text that may be mistaken, and every suggested option is a
question for the owner, not a decision. Nothing here changes the
design; it lists where the design appears to be inconsistent or
silent. Where an item says what the reference implementation does, that
was observed by running it and says nothing about what the spec
intends.

## 1. Apparent contradictions

2. **Forms filed as annotation tokens that head a list.** §54 files
   `tail`, `notail` and `delegate` under "annotation tokens, which
   annotate a form rather than heading a list", while the same entry
   calls them "marks that wrap a call", and §19 writes them
   `(tail (f ...))`. `subterm`, `predates` and `else`, under the same
   heading, also head a list. Probably wording only.

8. **"Only run-position forms run at compile time."** §7 says so
   without qualification. §27 adds that a macro's implementation runs
   each time a call of that macro is expanded, which can happen inside
   any body. Probably wording only.

## 2. Gaps an implementer could not fill without guessing

10. **Case and zero-return signatures.** §1 appears not to say whether
    names are case-sensitive; the reference treats `Foo` and `foo` as
    distinct. No signature with zero returns, such as `(Fn L ->)`, is
    shown; §26's "zero or more values" seems to allow one, and the
    reference accepts one (`tests/zero_return.sl`).

18. **Fetch-form arguments.** §14's list of erased positions does not
    include the arguments of the fetch forms of §53 (`level-of`,
    `matchable-of`, `delegate-of`, `numeral-of`, `slot-of`, `at-fn-of`),
    and §14 makes referring to an `erased` name from a non-erased
    position an error. Open: is a fetch form's argument an erased
    position, or is naming something there not a reference? The
    reference accepts `(matchable-of Box)`, with `Box` a type
    constructor, which enters scope erased, as a `many` argument inside
    a body.

20. **What a `def-fns` level may be.** §11 says only that a function's
    level is written on its `def-fns`. Open: must it be an entry
    created by `def-lvl`, or a `let` binder forwarding one, as §18
    requires of `prove-predates`'s `L`, or may it be any `(Level)`
    variable, such as an erased parameter? The reference accepts the
    latter (ASSUMPTIONS 13).

22. **`many` of type `Type`.** §21 says "A value of type `Type` is
    erased", and by §14 rule 2 type constructors enter scope erased, so
    a `many` field or parameter of type `Type` seems writable but never
    suppliable in a non-erased position. Open: is it an error at its
    declaration? The reference accepts the declaration and refuses
    every non-erased use (ASSUMPTIONS 31).

## 3. Smaller ambiguities and housekeeping

26. Return-telescope names are apparently not in scope in the body,
    while parameter names are; the spec appears not to say. The
    reference reports a return name used in the body as unbound.

## 4. From a bug sweep of the implementation

Found by a Claude session probing the implementation against
DESIGN.md; each is a reading that may be mistaken and a question for
the owner, not a decision.

32. **The cell `at` forms in an erased position.** §14 refuses in an
    erased position the forms "whose only claim or effect is about the
    run", a list that names §39's `at` wrapper around a call but not
    §37's `(at (u ...))` around a cell invocation or its per-argument
    `(at)`, and it says erased code obeys §36's `at` rules. That seems
    to mean the cell forms are checked there, but no sentence says so.
    Also unclear: whether §37's "The marked argument must be
    non-erased" means the field's multiplicity or the argument's
    position, since in an erased position every argument is erased.
    The reference checks both forms in an erased position as it does
    elsewhere, and accepts `(u (at) a b)` there.
