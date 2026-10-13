# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision.

## Towards the full language (one session, with the owner)

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's (`unsupported`, `refuse`, `accept`,
`mismatch`, `stuck`); at the last run 79 tests were accepted with
OCaml's value and none mismatched. `lean/prelude.py` regenerates
`lean/prelude.sl` from `lib/prelude.sl` (135 of 215 forms). A checked
program prints from the stripped run; `--full` runs `eval`, which
computes erased values and so is slow on the prelude (about 3 s).

Next, none of it decided:

1. `unique` (DESIGN.md sections 13, 15, 16 and 32) is what most
   unsupported tests need: about 170 name it, though only about 30 need
   nothing else. Open: whether the core models it, and with what
   theorem (a session's guess: on every path of the stripped run, a
   value bound `unique` is used at unique at most once), or the
   elaborator alone checks its uses and the core reads it as `many`.
2. Slots, `at` and cells (sections 35 to 41), and at-functions; most of
   the tests that name `at` also need `unique`.
3. `comptime-match` and `Settled` (sections 28 and 29).
4. `tests/extern_tail.sl` times out: the runner holds a `Nat` in unary.
