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

## 2. Gaps an implementer could not fill without guessing

## 3. Smaller ambiguities and housekeeping

## 4. From a bug sweep of the implementation

Found by a Claude session probing the implementation against
DESIGN.md; each is a reading that may be mistaken and a question for
the owner, not a decision.

32. **The cell `at` forms in an erased position.** §14 refuses in an
    erased position the forms "whose only claim or effect is about the
    run", a list that names §39's `at` wrapper around a call but not
    §37's `(at m (u ...))` around a cell invocation or its per-argument
    `(at)`, and it says erased code obeys §36's `at` rules. That seems
    to mean the cell forms are checked there, but no sentence says so.
    Also unclear: whether §37's "The marked argument must be
    non-erased" means the field's multiplicity or the argument's
    position, since in an erased position every argument is erased.
    The reference checks both forms in an erased position as it does
    elsewhere, and accepts `(u (at) a b)` there.
