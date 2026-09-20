# B3. `tail` refused in a function whose returns are all erased

Status: open defect, BUGS.md 3. Severity: rejects a valid but unreachable
program.

## The rule

UNIQUE.md U8: "a call whose only non-erased results are `at` returns is a
tail call from a function returning none". DESIGN.md section 9 judges
tail-ness on the post-erasure code.

## The observation

```scheme
(def-fns _ $ many g : (unique (Nat) x) -> (unique (Nat) r at x) x)
(def-fns _ $ many h : (unique (Nat) x) -> (erased (Nat) e)
  (let (unique y) (tail (g x)))
  (Zero))
```

is refused with "a tail-marked call is not in tail position". Post
erasure both `g` and `h` return nothing. The cause is that `project_code`
short-circuits when every result is kept, which includes the empty list
of kept results of an all-erased return telescope, so the body's trailing
erased code never becomes `(values)` for `check_marks` to fold the `let`
away.

## Why no fix

With every return erased, every call to `h` sits in an erased position
and never runs, so nothing misbehaves at runtime. A candidate fix is to
short-circuit only on a non-empty all-kept list; its consequences
elsewhere were not verified, so it was left alone. The runnable variant,
one `at` return with `(let (unique y) (tail (g x))) y`, is accepted.
