# special-lang

A prototype OCaml interpreter for the language recorded in DESIGN.md.
KERNEL.md and SUGAR.md are further design notes; SPEC-REVIEW.md lists
the spec's open points and ASSUMPTIONS.md the assumptions the
interpreter makes about them.

## Build and run

```sh
apt-get install -y ocaml ocaml-dune libzarith-ocaml-dev
dune build
dune exec bin/main.exe tests/list.sl tests/map.sl tests/coerce.sl
dune test
```

Files given on one command line share a scope, in order; with no file
the program is read from stdin, and `--repl` (after any files) reads
forms interactively. Every program starts in the scope of the source
prelude `lib/prelude.sl` (`Nat`, `U8`, DESIGN.md section 41), whose
`extern`-marked definitions run through `lib/ffi.ml` unless
`--no-extern` strips those implementations and runs the source models. A file is a sequence of statements,
optionally ending in an expression whose value is printed.

`dune test` runs every `tests/*.sl`, once with the FFI and once
without. A test's leading comments say what it needs: `; needs: list vec` runs those files first in the same scope,
`; expect: text` is the line the test must print, and `; error: text`
means it must fail with a message mentioning that text.

## How it runs a program

The reader turns the file into s-expressions. The elaborator walks
them with a scope of entries and a fact table (types and `is` rules,
read canonically), dispatching each form on its head as DESIGN.md
section 4 describes: constructor and function application by the
head's type, special forms by the head's Const value. Elaboration
produces, for every expression, the terms and types of its values and
a piece of post-erasure code in which erased positions are gone. A
statement in run position is elaborated, run at once by the evaluator,
and its binders are born Const with the resulting values (sections 16
and 34), which form the environment later code runs in; inside function
bodies and match branches statements compile to code instead. The
evaluator is a plain recursive interpreter over that code; a value is
its constructor's `many` fields, tagged only where section 38 says an
enum carries a tag, or a closure, or a token standing for anything
erased. Nothing is optimized.

## Layout

- `lib/reader.ml` — s-expressions with `$` (DESIGN.md section 2)
- `lib/term.ml` — the restricted type grammar (section 5), de Bruijn telescopes
- `lib/env.ml` — scope entries, the fact table, canonicalization, forced unification (sections 3, 18)
- `lib/value.ml`, `lib/eval.ml` — runtime values, post-erasure code, the evaluator
- `lib/special.ml`, `lib/prelude.ml` — the special-form registry (section 27) and built-ins
- `lib/prelude.sl`, `lib/ffi.ml` — the source prelude and the extern implementations (section 41)
- `lib/elab.ml` — the elaborator: head dispatch, erasure, levels, match, statements
- `bin/main.ml` — command line driver
- `tests/` — DESIGN.md's worked examples and further tests
