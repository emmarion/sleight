# special-lang

A prototype OCaml interpreter for the language recorded in DESIGN.md.
KERNEL.md and SUGAR.md are further design notes; SPEC-REVIEW.md lists
the spec's open points and ASSUMPTIONS.md the assumptions the
interpreter makes about them. HANDOFF.md records work in progress
handed from one session to the next. EXAMPLES.md indexes the tests that show the
features working together. `self/` is a compiler from the language to
OCaml written in the language itself, bootstrapped through this
interpreter's extractor (`self/README.md`, `self/bootstrap.sh`).

## Build and run

```sh
apt-get install -y ocaml ocaml-dune libzarith-ocaml-dev
dune build
dune exec bin/main.exe tests/list.sl tests/map.sl tests/coerce.sl
dune test
dune exec bin/main.exe -- tests/io_echo.sl --extract echo.ml
ocamlfind ocamlopt -package zarith -linkpkg echo.ml -o echo && ./echo
```

Files given on one command line share a scope, in order; with no file
the program is read from stdin, and `--repl` (after any files) reads
forms interactively. A file's final expression is printed, unless its
value is a function from `String` to `String`, when stdin is fed to it
and its result written to stdout (`tests/main_reverse.sl`), or an `IO`
value, when the driver performs its requests one by one
(`tests/io_echo.sl`; arguments after `--` on the command line are the
program's), or a function from no arguments to one value, when it is
applied and its result printed (`tests/thunk_list.sl`), which is how a
program asks for its final value to be computed by code rather than at
elaboration. Numerals, `#\c` character literals and `"..."` string
literals are prelude-backed sugar (ASSUMPTIONS.md 47-60). Every program starts in the scope of the source
prelude `lib/prelude.sl` (`Nat`, `U8`, DESIGN.md section 41), whose
`extern`-marked definitions run through `lib/ffi.ml` unless
`--no-extern` strips those implementations and runs the source models, and `--no-templates` extracts extern types
through their runtime views rather than the templates of `lib/ffi_templates.txt` (ASSUMPTIONS.md 133). A file is a sequence of statements,
optionally ending in an expression whose value is printed.

`--extract out.ml` elaborates the files as usual but, instead of
running their final values, writes the program out as standalone OCaml,
in the sense of Coq's extraction, to be compiled with ocamlfind against
zarith: each `def-fns` becomes a `let rec`, each ADT an OCaml type
tagged only where the interpreter tags, each match an OCaml match,
extern types and functions the same `lib/ffi_core.ml` implementations
the interpreter uses (or their source models under `--no-extern`), and
the driver mirrors `lib/program.ml`. Everything computed at
elaboration, a run-position `let`, a literal, a `comptime-match` field
and the final value itself, is embedded as data, closures included and
sharing kept, rather than recomputed; a final function from no
arguments is the form whose result is computed by the extracted code. The result is meant to behave as the
interpreter does on the same files, which `dune test` checks
(ASSUMPTIONS.md 61-67); every value is an `Obj.t`, so the output is not
typed OCaml.

`dune test` runs every `tests/*.sl`, once with the FFI and once
without, and extracts, compiles and runs every test that runs, both
ways, against the same directives. A test's leading comments say what it needs: `; needs: list vec` runs those files first in the same scope,
`; expect: text` is a line the test must print, `; stdin: text` a
line of its input, `; args: a b` its arguments, `; stderr: text` a line
it must write to stderr, `; exit: n` the code an `IO` program must exit
with, and `; error: text` means it must fail with a message mentioning
that text.

## How it runs a program

The reader turns the file into s-expressions. The elaborator walks
them with a scope of entries and a fact table (types and `is` rules,
read canonically), dispatching each form on its head as DESIGN.md
section 4 describes: constructor and function application by the
head's type, special forms by the head's Const value. Elaboration
produces, for every expression, the terms and types of its values and
a piece of post-erasure code in which erased positions are gone. A
statement in run position is elaborated, run at once by the evaluator,
and its binders are minted Const with the resulting values (sections 16
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
- `lib/prelude.sl`, `lib/ffi.ml`, `lib/ffi_core.ml` — the source prelude, the FFI registry, and the extern implementations it and extracted programs share (section 41)
- `lib/literal.ml` — numeral and character literals and what they expand to
- `lib/elab.ml` — the elaborator: head dispatch, erasure, levels, match, statements, literal hoisting
- `lib/driver_core.ml`, `lib/program.ml` — running a `String -> String` or `IO` final value against the world, the first shared with extracted programs
- `lib/extract.ml` — OCaml extraction of the traced run-position statements and final expressions
- `bin/main.ml` — command line driver
- `test/runtest.ml` — the test runner, interpreting and extracting each test
- `tests/` — DESIGN.md's worked examples and further tests
