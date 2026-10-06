# Bugs

Defects found in the implementation, for the owner to get to. Written by
Claude sessions; each entry says how it was reproduced, and nothing here
is a design decision. Remove an entry when it is fixed.

1. **A `tail` mark is refused in a function whose returns are all
   erased.** With `g : (unique (Nat) x) -> (unique (Nat) r at x)`, the
   body `(let ((unique y)) (tail (g x))) (Zero)` of a function returning
   `(erased (Nat) e)` is refused as not in tail position: `project_code`
   short-circuits on an empty list of kept results, so the trailing erased
   code never becomes `(values)` for `check_marks` to fold. Such a
   function is only ever called erased, so nothing runs wrongly.


2. **The two compilers disagree on whether a `cell-match` body is in run
   position.** `lib/elab.ml`'s `elab_cell_match` elaborates the body under
   the enclosing run position, while `self/elab.sl`'s `elab-cell-match`
   clears it, as both do for a match branch. So with a `cell-match` at a
   file's top level, `(comptime-match many o (Full w))` as a statement of
   its body is accepted by the reference and refused by slc (`` `comptime-match`
   is a run-position statement``), reproduced on 354d1aa; and slc writes one
   warning on `tests/lopsided_match_warn.sl` (line 94) that the reference
   does not. DESIGN.md §16 defines run position as under no function body
   and no match branch, which, as read here, would make the reference's
   behaviour the specified one; whether a `cell-match` body was meant to
   count as a match branch there is not settled.
