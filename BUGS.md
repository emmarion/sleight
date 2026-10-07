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

2. **`share` is accepted inside the body of an `erased` function when
   it is bound by a non-erased `let` binder.** `tests/dump_context_stmt.sl`
   expects `(let ((many ys)) (share xs))` inside an `erased` function to
   be accepted. DESIGN.md §16 says a `share` in an erased position is an
   error, and the same `share` in that function's return position is
   refused (`tests/share_erased_pos_bad.sl`). The likely cause: `elab_let`
   takes the position from the binder's multiplicity instead of from the
   enclosing erased position, and the usage checks are switched off
   there. The same route probably bypasses two other rules: that a
   `match` in an erased position must be written `erased`, and that a
   `cell-match` is refused in an erased position. Nothing runs wrongly,
   because the whole body is erased.

3. **A binder whose declared type is `(Slot)` is made its own slot
   without `slot-self`.** `Env.bind` (`lib/env.ml`, the `self` flag)
   equates a new entry's automatic slot with the entry itself whenever
   the declared type is a variable or a nullary application that
   canonicalizes to `(Slot)`. `self/core.sl`'s `bind-as-raw` does the
   same. DESIGN.md §35 says `slot-self` is the only way a `(Slot)`
   variable becomes its own slot. Reproduced: `tests/slot_self.sl`
   prints its expected `2` with its `(slot-self s)` line deleted, and
   `tests/slot_default.sl` expects a word `at` a `(Slot)` parameter to be
   in that parameter's slot with no `slot-self` written, so that test
   pins the defect. ASSUMPTIONS 201 and 204 record the default. The fix
   is the one line in each compiler that creates the slot's rule. After
   the fix, `tests/slot_default.sl` should be refused or rewritten with a
   `slot-self`, and `tests/slot_self.sl` will then exercise the form.

4. **`(share u)` is accepted as the head of a type form.**
   `tests/type_head_unique_const_degrade.sl` expects it, although a type
   is an erased position, where `share` is an error. `elab_term` reads
   the head through `special_of` without the position check that
   `read_special` makes. Reported by a review session; not reproduced
   independently.

5. **A `cell-match` written with an `(at ...)` annotation is accepted
   and keeps its code.** The entries are checked to be erased or `at`,
   as for an at-match, but the code is neither skipped nor checked to
   erase: the `result_tele` call for `cell-match` in `lib/elab.ml`
   discards the at-match flag. Reported by a review session from the
   code; no test reaches it. OPEN.md 22 asks what the form should mean.

6. **The usage hints in `lib/specials.txt` disagree with the elaborator
   about cell binders.** The hint for `cell-match` shows the cell binder
   as optional, but it is mandatory at `unique`. The hints for a branch
   and for `else` show it as required, but it is optional. Reported by a
   review session from the file; not reproduced independently.
