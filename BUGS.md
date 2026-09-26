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
   Both look to be on the `slc` side, though only `dump-context` has been
   seen to show either:
   - The 42 are the 38 erased functions of run-position `def-fns` blocks
     and the 4 anonymous `Delegate` proofs such blocks bind. DESIGN.md
     section 34 reads as making every name a run-position statement
     introduces `Const`, as `lib/elab.ml`'s `elab_def_fns` does. In
     `self/elab.sl`, `define-fns` leaves a `BErased` function out of the
     group that `env-close-group` (`self/eval.sl`) marks `Const`, and
     `define-fn` binds the `Delegate` proof with a plain `bind`. A user
     file's erased top-level function reproduces it.
   - `sp-table` (`self/core.sl`) says it follows `lib/special.ml`'s order
     but places `UniqueFn`, `match`, `matchable-of`, the cell forms,
     `coercible-share` and `at` differently; and `bind-specials` binds each
     `%` constructor next to its alias and the `Matchable` last, where
     `lib/prelude.ml` binds the constructors, then the `Matchable`, then
     the aliases. No order seems to be fixed by DESIGN.md.
