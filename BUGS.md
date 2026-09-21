# Bugs

Defects found in the implementation, for the owner to get to. Written by
Claude sessions; each entry says how it was reproduced, and nothing here
is a design decision. Remove an entry when it is fixed.

1. **A value of a type with no runtime discriminant prints differently in
   the interpreter and in extracted code.** A `union` whose constructors
   have unequal non-erased arities, say `(many UA : -> (U))` and
   `(many UB : (many (Nat) n) -> (U))`, with `(UB (Succ (Zero)))` as the
   final value: the interpreter prints `(UB (Succ (Zero)))`, reached
   through `Elab.show_value`'s untyped fallback when the first candidate's
   arity mismatches, and the extracted program prints `_`, rendering the
   first candidate. When the arities agree the interpreter prints the
   first candidate's rendering too, which may be the wrong constructor's.
   Neither design note says what such a value prints as, and a union
   carries no tag to decide it, so the rendering is a decision before it
   is a fix (ASSUMPTIONS 183).

2. **A `tail` mark is refused in a function whose returns are all
   erased.** With `g : (unique (Nat) x) -> (unique (Nat) r at x)`, the
   body `(let (unique y) (tail (g x))) (Zero)` of a function returning
   `(erased (Nat) e)` is refused as not in tail position: `project_code`
   short-circuits on an empty list of kept results, so the trailing erased
   code never becomes `(values)` for `check_marks` to fold. Such a
   function is only ever called erased, so nothing runs wrongly.
