# Q2. An erased-position `unique` match mints `SlotHolds` over erased binders

Status: open question, ASSUMPTIONS 183. No misbehaviour found.

## The rule

UNIQUE.md U5: on a type whose constructors have cells "every pattern adds
one binder after the fields, mandatory". U10: what a `SlotHolds` names
"must be declared non-erased, so that the word exists; since every
`SlotHolds` in a cell's type comes from such an expression or from a
destructure's field binders, none names an erased variable".

## The observation

The extra binder is required from the written mode, so a `match unique`
in an erased position still takes it, which reads right against U5 and
which `tests/unique_phantom_no_cell.sl` relies on. But there the fields
are bound erased, while `pattern_cell` builds the binder's type
`(Cell C (SlotHolds f1) ... (SlotHolds fn))` from the constructor's
declared non-erased fields. The result is a `SlotHolds` whose argument is
an erased binder, which the `SlotHolds` special form itself refuses.
`pattern_cell` builds the term directly and bypasses that check.

Everything in that position is erased, the branch environment and any
at-class merge in it are discarded, and the binder itself is bound erased,
so no exploit was found.

## The question

Should the extra binder be omitted, or bound at a type without slots,
when the match sits in an erased position; or is a `SlotHolds` over an
erased binder harmless there and U10's sentence to be read as being about
non-erased code only?
