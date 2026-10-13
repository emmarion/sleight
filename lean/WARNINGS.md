# lean/ warnings

The warnings the Lean runner emits that the compilers do not (the
compilers' own are in `../WARNINGS.md`). Written by a Claude session;
the code that emits each warning is the authority. Each is printed to
standard error, without a position, and does not change the verdict.
Numbered items are never renumbered.

## 1. An extern with a native implementation whose model is not the proved one

`the extern `add` is not the model the runner's native `add` is proved
against, so it runs its model`. The runner's stripped run computes
`add` natively only when the function marked `extern` and named `add`
has, after elaboration, exactly the body the native code is proved
against (`addBody` in `Minimal/Native.lean`), over the extern `Nat`.
When an `extern` `add` does not, it runs its model, and this warning
says so. `Minimal/Reader.lean` (`def-fns`).
Example: `tests/extern_no_prelude.sl` under `--no-prelude`, whose
`add` returns no proof.
