# special-lang

A prototype OCaml interpreter for the language recorded in DESIGN.md
and UNIQUE.md (excluding the deferred forms in U15).
KERNEL.md and SUGAR.md are further design notes; SPEC-REVIEW.md lists
the spec's open points and ASSUMPTIONS.md the assumptions the
interpreter makes about them, which is the whole of what it is for: a
choice a session had to make on its own, because the spec was silent
and the code had to do something. A decision the owner made is recorded
in DESIGN.md or UNIQUE.md, never here, and an entry that stood in for
one is removed when the owner decides it. HANDOFF.md records work in progress
handed from one session to the next. BUGS.md records defects found in the
implementation and TOOLING-WISHLIST.md the friction met writing programs in
the language. EXAMPLES.md indexes the tests that show the
features working together, and DEMOS.md proposes programs that are not
written yet. `self/` is a compiler from the language to
OCaml written in the language itself, bootstrapped through this
interpreter's extractor (`self/README.md`, `self/bootstrap.sh`).
MINIMAL.md records a minimal fragment of the language, and `mini/` its
semantics written as relations in the language itself (`mini/README.md`).
`pal/` holds certified longest-palindrome programs (`pal/README.md`).

## Build and run

```sh
apt-get update
apt-get install -y ocaml ocaml-dune ocaml-findlib libzarith-ocaml-dev python3 time
dune build
dune exec bin/main.exe tests/list.sl tests/map.sl tests/coerce.sl
dune test
test/one.sh tests/list.sl
self/bootstrap.sh
dune exec bin/shape.exe -- tests/list.sl
dune exec bin/main.exe -- tests/io_echo.sl --extract echo.ml
ocamlfind ocamlopt -package zarith,unix -linkpkg echo.ml -o echo && ./echo
_build/self/slc --interpret tests/io_echo.sl
```

Files given on one command line share a scope, in order; with no file
the program is read from stdin, and `--repl` (after any files) reads
forms interactively. A file's final expression is printed, unless its
value is a function from `String` to `String`, when stdin is fed to it
and its result written to stdout (`tests/main_reverse.sl`), or an `IO`
value, when the driver performs its requests one by one, applying each
request's continuation, a `UniqueFn`, once
(`tests/io_echo.sl`; arguments after `--` on the command line are the
program's), or a function from no arguments to one value, when it is
applied and its result printed (`tests/thunk_list.sl`), which is how a
program asks for its final value to be computed by code rather than at
elaboration. Numerals, `#\c` character literals and `"..."` string
literals are prelude-backed sugar (LITERALS.md, ASSUMPTIONS.md 47-60), and a printed
value of one of those three types is spelled as the literal it reads back
from (ASSUMPTIONS.md 154) rather than as its prelude model. Every program starts in the scope of the source
prelude `lib/prelude.sl` (`Nat`, `U8`, DESIGN.md section 41), whose
`extern`-marked definitions run through `lib/ffi.ml` unless
`--no-extern` strips those implementations and runs the source models, and `--no-templates` extracts extern types
through their runtime views rather than the templates of `lib/ffi_templates.txt` (ASSUMPTIONS.md 133).
`--no-prelude` starts from the built-in special forms alone, without `lib/prelude.sl`, for a program that
declares what it needs itself; it has no literals and no `String -> String` or `IO` final, those resting on
the prelude's types, and slc takes the same flag. A file is a sequence of statements,
optionally ending in an expression whose value is printed.

`--confine-dir dir` confines a program's file requests to `dir`: a path is
resolved against the working directory and through any symlinks, and a
request whose path lands outside `dir` answers `Fail` without being
performed, while one inside it behaves exactly as it would unconfined.
Without the flag the fence is `/`, so the same check admits every path.
A path whose symlinks cannot be followed to the end, the resolution
giving up after 1000 links, counts as outside every fence, `/` included.
A program narrows its own fence with the `ConfineDir` request, which
refuses a directory outside the current one (`tests/io_confine.sl`).
Nothing is resolved at compile time: under `--extract` the directory is
embedded in the OCaml written out as it was given, and the compiled
program confines itself to it when it starts, a relative one resolving
against the directory the program runs in, and exits with the error if
it cannot. slc takes the same flag, and under `--interpret` confines
itself once it has read its sources (ASSUMPTIONS.md 198).

`--confine-output-bytes n` crashes a program, exit code 1, before the
request that would take its output past `n` bytes: everything it writes,
plus 4096 per file or directory it creates. It lowers its own limit with
`ConfineOutputBytes`; a `Nat` too large for an OCaml `int` means no limit
(`tests/io_output_limit.sl`, ASSUMPTIONS.md 199). Like `--confine-dir`,
it is embedded under `--extract`, and slc takes it too.

`--no-env` hides the environment from the program: `GetEnv` answers
`None` and `GetEnvs` the empty list. Like `--confine-dir`, under
`--extract` it is embedded in the program written out, and slc takes
the same flag.

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

`self/bootstrap.sh` extracts the self-hosted compiler with the reference
extractor, compiles every `tests/*.sl` with it and compares what each program
does with the interpreter on the same files, runs every test again under
`slc --interpret`, which performs the program itself in place of writing
it out (`self/interp.sl`), then compiles the compiler with
itself and again with that result and requires the two outputs to be identical
(`self/README.md`). `test/one.sh tests/a.sl ...` runs just the named tests
through both: `test/runtest.ml`, which takes the same names, and
`self/bootstrap.sh one`, which reuses the last `slc` built when its sources
and the reference binary are unchanged. `bin/shape` reports where a file's forms open and close:
`shape file` lists every form spanning more than one line with the line it
closes on, and `shape --closers file` what each run of `)` closes, which is
for locating a misplaced paren where the checker's own error names only the
end of the file. It reads the same `lib/reader.ml` the checker does, so
comments and string literals are skipped rather than counted, and a file the
lexer cannot finish is reported as far as it got.
`--no-shape-note` leaves out the note naming the `bin/shape` command that a file
with a parenthesis mistake otherwise gets; slc takes the same flag.

`--hints file` reads the hints that diagnostics attach to special forms
and pieces of grammar from `file`, in place of `lib/specials.txt` and in
its format; slc takes the same flag. `--first-error`, slc's alone, stops
its report after the first error, where it would otherwise list every
error it recorded (`self/README.md`, "Errors are values").
`--warnings-as-errors` fails a run that warns, exit code 1, once every
file has been read and every message written: nothing is run and no
`--extract` output or OCaml is written. A warning silenced by `;! suppress`
does not count. slc takes the same flag, and `self/bootstrap.sh` builds slc
under it.

`bench/bench.sh <commit>` times the self-hosted compiler on a copy of its
own sources at that commit and on the sample programs under `bench/`, and
`bench/selfbuild.sh` rebuilds it from `self/` with an existing binary;
`bench/gen.py` writes the samples. `dune test` runs every `tests/*.sl`, once with the FFI and once
without, and extracts, compiles and runs every test that runs, both
ways, against the same directives. A test's comment lines say what it needs, read wherever in the file
they sit; one that names a line of the test itself is written at the end, so
that adding it does not move the lines it names. `; needs: list vec` runs those files first in the same scope,
`; expect: text` is a line the test must print, `; stdin: text` a
line of its input, `; args: a b` its arguments, `; env: NAME=value` a
variable of the environment it runs with, which holds those alone,
`; stderr: text` a line it must write to stderr, `; warns: text` a line the
file must warn with, from elaborating it or from checking its indentation,
whether or not it is then refused,
`; exit: n` the code an
`IO` program must exit with, `; externs: only` runs it with the FFI alone,
for a test whose source model is too slow to run, `; prelude: none` runs it
under `--no-prelude`, and `; error: text`
means it must fail with a message mentioning that text on one line. In
a `warns` or `error` line, `<**>` matches any run of characters, such as an
atom's id.

Every message either writes carries where it is about: the file, and the line
and column of the form it names, `path:line:col: error: text`, with `warning`,
`syntax error` or `note` in place of `error` for those. A position is where a
token's first character sits, both counted from one. A message about two
places writes the second as a `note` on its own line under it, which may be
in another file. A
message with nothing to point at — a contradiction that reached the driver, a
runtime error, whose code carries no positions — names the file alone
(ASSUMPTIONS 194).

Within a compile-time message a name, a term or a keyword of the language is
set off in backticks, `` `(List A)` `` or `` `share` ``, and a literal is left
bare, since it already reads as one: `3`, `#\a`, `"ab"`. Both compilers quote
through one function, `Env.tick` and `tick` in `self/core.sl`. Runtime errors
are not quoted. A term is shown canonically, each piece by the spelling that
means it where the message points:

- an atom by a numeral or string literal it equals, else by the newest name
  still in scope for it, else by a fetch form that yields it there with its
  argument a name, `(level-of f)`, else as `_1`, `_2` and on;
- an unsolved `_` (SUGAR.md 6) as `_?1`, `_?2` and on;
- a special form or annotation token, a fetch form's head included, by the
  newest name in scope that is `Const`, non-erased and holds it, else as `_`
  followed by its built-in name, `_Fn`, `(_level-of f)`.

Keywords in a message's prose follow the same rule where they stand for syntax,
alone in backticks, ``mark it `notail` ``, or inside quoted code, ``written
`(share x)` ``. Plain words naming a multiplicity, as in "used at unique", stay
as written. A keyword printed as `_` and its built-in name is noted at the
binder that shadows it, `` `_notail` is `notail`, shadowed here ``.

The two numberings follow order of first mention and hold for the whole run,
so `_3` names one entry in every message it appears in, and every message
that mentions one carries a note saying what it is: `` `_?1` is the `_`
written here ``, `` `_3` is anonymous, minted here ``, `` `_Fn` is `Fn`,
shadowed here ``. Which atom canonicalization keeps for a class is an
accident of minting order, so two numbers may turn out to denote one thing
under later facts, and a name is shown only where it still denotes that atom
(`Env.show`, `show-t` in `self/elab.sl`). A result that fails its return type
is reported where it is written, the entry of the body's final `values` or the
final expression.

`(dump-context)` stops elaboration where it is written and reports, as one
error, what the checker knows there: the goal, the level, every entry in scope
with its type, `is` rule, multiplicity and uniqueness state, and the
at-database. It can be used as an expression, a statement or a type;
`(dump-context x ...)` reports just the terms named. It's a debugging aid, so
its output isn't stable (ASSUMPTIONS 196).

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
evaluator is a plain recursive interpreter over that code; a value contains
its constructor's non-erased fields, tagged only where section 38 says an
enum carries a tag, or a closure, or a token standing for anything
erased. Unique cells permit in-place updates, while `at` returns reuse
an existing word instead of returning it physically.

## Layout

- `lib/reader.ml` — s-expressions with `$` (DESIGN.md section 2)
- `lib/term.ml` — the restricted type grammar (section 5), de Bruijn telescopes
- `lib/env.ml` — scope entries, the fact table, canonicalization, forced unification (sections 3, 18)
- `lib/value.ml`, `lib/eval.ml` — runtime values, post-erasure code, the evaluator
- `lib/special.ml`, `lib/prelude.ml` — the special-form registry (section 27) and built-ins
- `lib/prelude.sl`, `lib/ffi.ml`, `lib/ffi_core.ml` — the source prelude, the FFI registry, and the extern implementations it and extracted programs share (section 41)
- `lib/literal.ml` — the spellings of numeral, character and string literals
- `lib/elab.ml` — the elaborator: head dispatch, erasure, levels, match, statements, literal hoisting
- `lib/dump.ml` — the report `dump-context` stops elaboration with
- `lib/driver_core.ml`, `lib/program.ml` — running a `String -> String` or `IO` final value against the world, the first shared with extracted programs
- `lib/extract.ml` — OCaml extraction of the traced run-position statements and final expressions
- `lib/indent.ml` — indentation read as a claim about paren nesting, and the claim checked
- `bin/main.ml` — command line driver
- `bin/shape.ml` — where a file's forms open and close, for locating a misplaced paren
- `bin/indent.ml` — `lib/indent.ml`'s check run on its own over the files named
- `test/runtest.ml` — the test runner, interpreting and extracting each test
- `tests/` — DESIGN.md's worked examples and further tests
