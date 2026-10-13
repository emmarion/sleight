# lean/ warnings

The warnings the Lean runner emits that the compilers do not (the
compilers' own are in `../WARNINGS.md`). Written by a Claude session;
the code that emits each warning is the authority. Each is printed to
standard error, without a position, and does not change the verdict.
Numbered items are never renumbered.

## 1. An extern with a native implementation whose model is not the proved one

`the extern `NAME` is not the model the runner's native `NAME` is
proved against, so it runs its model`, for `NAME` one of `add`,
`nat-cmp`, `mul`, `sub`, `divmod` and `nat-mod`. The runner's stripped
run computes such a function natively only when, after elaboration, its
body, its signature's erasures and its place in the program are exactly
those its native code is proved against (`Minimal/Native.lean`), and so
are those of the proved models it calls. When a function marked
`extern` under one of these names does not match, it runs its model,
and this warning says so. `Minimal/Reader.lean` (`def-fns`).
Example: `tests/extern_no_prelude.sl` under `--no-prelude`, whose
`add` returns no proof.
