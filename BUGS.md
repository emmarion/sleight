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

2. **`share` is accepted in an erased function's body under a non-erased
   `let` binder.** `tests/dump_context_stmt.sl` pins
   `(let ((many ys)) (share xs))` inside an `erased` function as accepted,
   where DESIGN.md §16 has a `share` in an erased position as an error and
   the same `share` in that function's return position is refused
   (`tests/share_erased_pos_bad.sl`). The session's reading of the cause:
   `elab_let` takes the position from the binder's multiplicity rather
   than from the enclosing erased position, and the usage checks are
   suppressed there, so the rule that a `match` in an erased position must
   be written `erased`, and the `cell-match` refusal, look reachable by
   the same route. Nothing runs wrongly, the body being erased throughout.

3. **`tests/slot_self.sl` passes without its `(slot-self s)`.** Deleting
   that line leaves the test printing its expected `2`, so the test does
   not exercise the form it is named for: the pattern field `s : (Slot)`
   is its own slot by default (DESIGN.md §35), and the `MkBox` match
   already forces the cell's slot to `(slot-of n)`. The `(slot-self s)` in
   the prelude's `array-unpluck` may be redundant for the same reason;
   not checked.

4. **`(share u)` as the head of a type form is accepted.**
   `tests/type_head_unique_const_degrade.sl` pins it, although a type is
   an erased position where `share` is an error: `elab_term` reads the
   head through `special_of` without the position check `read_special`
   makes. Reported by a review session; not independently reproduced.

5. **A `cell-match` written with an `(at ...)` annotation is accepted
   and keeps its code.** The entries are checked to be erased or `at`, as
   an at-match's are, but the code is neither skipped nor checked to
   erase (`elab.ml`'s `result_tele` caller for `cell-match` discards the
   at-match flag). Reported by a review session from the code; no test
   reaches it. OPEN.md 22 asks what the form should mean.

6. **`lib/specials.txt`'s usage hints disagree with the elaborator on
   cell binders.** The hint for `cell-match` shows the cell binder as
   optional, but it is mandatory at `unique`; the hints for a branch and
   an `else` show it as required, but it is optional. Reported by a
   review session from the file; not independently reproduced.
