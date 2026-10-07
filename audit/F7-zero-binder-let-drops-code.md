# F7. A zero-binder `let` inside a body drops its right-hand side's code

Status: fixed in `fa5747a` (`lib/elab.ml` `elab_let`, `self/elab.sl`
`elab-let`); covered by `tests/zero_size_tail.sl`. Severity: runtime
omission, companion to F5.

## The rule

DESIGN.md section 54: a zero-binder `let` is expected to matter for
"invoking a destructor, or similar". DESIGN.md section 37: a placement invocation
performs stores; section 36: a call whose only results are `at` returns has no
physical results.

## The defect

Inside a function body `elab_let` emitted the right-hand side's code only
when the list of non-erased binders was non-empty. With F5 making a
size-zero position non-erased, a call there is counted as a use, so a
function taking a unique argument and returning nothing consumes it, but
its code would still have been dropped and the call never run. In run
position the statement was run regardless.

## Reproducer

With `g` returning `(values)`, the body `(let (g n)) (Succ n)` of a
function extracted to code that never called `g`. After the fix it
extracts to `let _ = g n in ...`, and the interpreter's `CLet` with no
ids binds nothing and runs the call.

## The fix

Emit the code unless the position is erased. Self's `SLet` already
admits an empty frame and its emitter already had the zero-id arm, so
the mirror is one condition.

## Caveats

Whether a computation producing no value can be dropped at all is
arguable from section 14's justification of erasure, the language being
"immutable, effect-free, and total"; with section 37's stores and extern in-place
updates that argument no longer covers a zero-result call, which is why
the code is now kept. Tied to F5's reading.
