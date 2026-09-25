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

4. **The self-hosted compiler's prelude entries seem to disagree with the
   reference's.** `(dump-context)` alone in a file lists the prelude on
   both sides; with anonymous ids normalized, 42 erased prelude functions
   and proofs (e.g. `numeral-inj`, `init-witness`) read `Const` in the
   reference and `Dyn` under `slc`, and the 8 `%`-named special forms
   (`%match`, `%at`, ...) appear at different places in the scope order.
   Which side is wrong has not been checked.
