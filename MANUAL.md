# The implementations and their command lines

This file describes the implementations of Sleight, the language of
[DESIGN.md](DESIGN.md): the reference interpreter and compiler in `lib/`
and `bin/`, slc, the compiler written in the language itself under
[`self/`](self/), the test runner, and the agent harness. [README.md](README.md)
introduces the repository. DESIGN.md, the other notes and the code cite
this file by name.

## Source libraries

[`std/`](std/) holds source libraries a program names on the command line before its
own files. [`std/macro.sl`](std/macro.sl) holds helpers for writing macros, [`std/nat.sl`](std/nat.sl)
holds `Le`, the non-strict order on `Nat`, `Ne`, inequality as one of the
two strict orders, and the lemmas `lt-pred`, `lt-succ-left`, `lt-irrefl`,
`add-le-right` and `double-le`, [`std/list.sl`](std/list.sl) holds lemmas
about the prelude's `Length`, `Nth`, `SetNth`, `Repeat` and `NthLast`, and
[`std/tactics.sl`](std/tactics.sl), which needs `std/macro.sl` and `std/nat.sl`, holds proof
tactics written as macros.


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
value is a `Program`, when the driver runs it step by step, applying each
step's continuation, a `UniqueFn`, once to the world, whose requests
`world-do` performs as the code reaches them
(`tests/io_echo.sl`; arguments after `--` on the command line are the
program's), or a function, which must be one of the two forms of
DESIGN.md section 27: from `String` to `String`, when stdin is fed to it
and its result written to stdout (`tests/main_reverse.sl`), or from no
arguments to one value, when it is applied and its result printed
(`tests/thunk_list.sl`), which is how a program asks for its final value
to be computed by code rather than at elaboration. Numerals, `#\c` character literals and `"..."` string
literals are prelude-backed sugar (DESIGN.md section 45, ASSUMPTIONS.md 47-60), and a printed
value of one of those three types is spelled as the literal it reads back
from (ASSUMPTIONS.md 154) rather than as its prelude model. Every program starts in the scope of the source
prelude `lib/prelude.sl` (`Nat`, `U8`, DESIGN.md section 42), whose
`extern`-marked definitions run through `lib/ffi.ml` unless
`--no-extern` strips those implementations and runs the source models, and `--no-templates` extracts extern types
through their runtime views rather than the templates of `lib/ffi_templates.txt` (ASSUMPTIONS.md 133).
`--no-prelude` starts from the built-in special forms alone, without `lib/prelude.sl`, for a program that
declares what it needs itself; it has no literals, no `world-do` and no `String -> String` or `Program` final, those resting on
the prelude's types, and slc takes the same flag. Only the prelude, or a program run with `--no-prelude`, may mark
a definition `extern` (DESIGN.md section 42). A file is a sequence of statements,
optionally ending in an expression whose value is printed.

`--confine-read path` and `--confine-write path` confine a program's file
requests, its fence, to the paths they name, each flag given any number of
times: a path named by either may be read, and one named by
`--confine-write` written, and each covers everything below it, so a
directory grants its whole tree and a file grants itself alone. A path the
program names, and one a flag names, is resolved against the working
directory and through any symlinks, every component but the last of a
named path having to exist. `ReadFile`, `ReadFileIn`, `ListDir` and `Stat`
read, and are performed when their path is covered by a readable path.
`WriteFile`, `AppendFile`, `MkDir`, `DeleteFile` and `DeleteDir` write, and
are performed when their path is covered by a writable one, so a writable
path may itself be created, removed and created again. `MkDir`,
`DeleteFile` and `DeleteDir` do not follow a symlink in last position, so
a writable path that names a symlink lets a program write through it but
not remove it. A request the fence does not admit answers `Fail` without
being performed, while one it admits behaves exactly as it would
unconfined. Without either flag `/` is writable, so the same check admits
every path. A path whose symlinks cannot be followed to the end, the
resolution giving up after 1000 links, is admitted by no fence, and
neither is a path with a component before its last that cannot be
examined, such as one that does not exist. A program narrows its own
fence with the `ConfinePaths reads writes` request, which sets the paths
it may read and those it may write, and refuses a path to read that the
current fence does not let it read, and a path to write that it does not
let it write. With both lists empty it leaves the program no path at all
(`tests/io_confine.sl`).
Nothing is resolved at compile time: under `--extract` the paths are
embedded in the OCaml written out as they were given, and the compiled
program confines itself to them when it starts, a relative one resolving
against the directory the program runs in, and exits with the error if
it cannot. slc takes the same flags, and under `--interpret` confines
itself once it has read its sources (ASSUMPTIONS.md 198).

`--comptime-unconfine name` adds `name` to the names `read-file` may
read relative to (DESIGN.md section 65), beside the program's source
files, without reading anything: a read relative to it resolves against
the directory its text names, as for a source file (ASSUMPTIONS.md 219),
and one relative to a directory that does not exist answers `Fail`. A
name a `;! file` pragma gives a position (DESIGN.md section 4) is
readable relative to only through this flag. Each occurrence adds one
name, and the flag may be given any number of times. The fence
does not apply to `read-file`. slc takes the same flag.

`--confine-output-bytes n` crashes a program, exit code 1, before the
request that would take its output past `n` bytes: everything it writes,
plus 4096 per file or directory it creates, while it has a limit; what it
writes with none is not counted. It sets or lowers its own limit with
`ConfineOutputBytes`; a `Nat` too large for an OCaml `int` means no limit
(`tests/io_output_limit.sl`, ASSUMPTIONS.md 199). Like the fence,
it is embedded under `--extract`, and slc takes it too.

`--no-env` hides the environment from the program: `GetEnv` answers
`None` and `GetEnvs` the empty list. Like the fence, under
`--extract` it is embedded in the program written out, and slc takes
the same flag.

`--eval-fuel n` bounds the evaluator. An application spends one unit of
fuel, a call to a function interpreted from its body one more, and each
gives its units back when it returns, so `n` bounds how deeply
applications nest, a tail call nesting inside the call it replaces. A
run that would go further crashes with `out of fuel` (DESIGN.md section
31). It bounds every run the evaluator makes, at compile time and, in
the reference and under `slc --interpret`, the program's own; the OCaml
that `--extract` or slc writes out has no bound. Without the flag the
reference has none and slc's is 1000000000. A run-position form whose
evaluation crashes is refused, the reference naming the file alone, as
for any runtime error, and slc the form. slc takes the same flag, and
the two count alike in every run compared so far
(`tests/comptime_fuel.sl`).

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

`--goal mode` says what the unit's `goal` (DESIGN.md section 71) requires;
`mode` is `none`, the default, `open` or `proved`. Under `none` the driver
is as described above, whether or not a file sets a goal. Under `open` and
`proved` the driver is off: nothing is run, printed or written once the
files are elaborated, a final expression included. `open` fails a run in
which no file sets a goal or a file ends in an expression; `proved` fails
one in which no file sets a goal, a file before the last ends in an
expression, or the last does not end in one that checks against the goal.
When it succeeds, `proved` writes one `note` to stderr, in the format
below, at the `goal` form, with the goal shown canonically as the scope
there spells it (ASSUMPTIONS.md 223, 225): `` spec.sl:6:1: note: proved
`(goal many (Doubler))` `` (`tests/goal_proved_fn.sl`). The reference
refuses `--extract`, `--repl` and `--no-prelude` with `open` or `proved`;
slc takes the same flag and refuses `--interpret` and `--no-prelude` with
them, and then writes no OCaml. Warnings are reported as they are without
the flag, and `--warnings-as-errors` fails a run that warns before any
goal is checked.

`--hints file` reads the hints that diagnostics attach to special forms
and pieces of grammar from `file`, in place of `lib/specials.txt` and in
its format; slc takes the same flag. `--first-error`, slc's alone, stops
its report after the first error, where it would otherwise list every
error it recorded (`self/README.md`, "Errors are values").
`--warnings-as-errors` fails a run that warns, exit code 1, once every
file has been read and every message written: no final value is run and
no `--extract` output or OCaml is written. A warning silenced by `;! suppress`
does not count. slc takes the same flag.
`--warn-unused` adds the unused-binder warnings of WARNINGS.md 10, for the
prelude and every file named; slc takes it too. `self/bootstrap.sh` builds slc
under both flags, and `dune test` checks the prelude, and every file a test
needs from outside `tests/`, as `--warn-unused` does, failing on any warning.

`--fn-same` accepts `fn-same` (DESIGN.md §70), which is otherwise refused;
OPEN.md 36 asks whether it should be. slc takes the same flag.

`bench/bench.sh <commit>` times the self-hosted compiler on a copy of its
own sources at that commit and on the sample programs under `bench/`, and
`bench/selfbuild.sh` rebuilds it from `self/` with an existing binary;
`bench/gen.py` writes the samples; `bench/scale.py slc [shape ...]` times
slc on generated programs of doubling size, one shape each, with each
time's ratio to the previous size's. `dune test` runs every `tests/*.sl`, once with the FFI and once
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
`; exit: n` the code a
`Program` must exit with, `; externs: only` runs it with the FFI alone,
for a test whose source model is too slow to run, `; extract-bytes-at-most: n`
bounds the size of the OCaml that extracting it writes, `; prelude: none` runs it
under `--no-prelude`, `; goal: mode` under `--goal mode`, extracting nothing and
having no `slc --interpret` run when the mode is `open` or `proved`, `; flags: --f ...`
under further flags, which `test/runtest.ml` requires to be refused and which a
test naming a flag that only one implementation takes runs under that one alone, and `; error: text`
means it must fail with a message mentioning that text on one line. In
a `warns` or `error` line, `<**>` matches any run of characters, such as an
atom's id. `; confine-read: path`, `; confine-write: path`, `; comptime-unconfine: name`, `; confine-output-bytes: n`,
`; no-env: yes`, `; eval-fuel: n` and `; fn-same: yes` run the test under
the corresponding flags. Every test runs under `--warn-unused`, its own binders checked, unless it
says `; warn-unused: no`: the tests of DESIGN.md's worked examples, which keep
the examples' text, and a few macro tests, whose binders a macro reaches in
ways the warning does not count as uses.

Every message either writes carries where it is about: the file, and the line
and column of the form it names, `path:line:col: error: text`, with `warning`,
`syntax error` or `note` in place of `error` for those. A position is where a
token's first character sits, both counted from one. The file is the one a
`;! file` pragma in force there gives (DESIGN.md section 4), its lines counted
from the line after the pragma, and otherwise the file the form was read from. A message about two
places writes the second as a `note` on its own line under it, which may be
in another file. A
form a macro places at `NoPos` (DESIGN.md section 62) is about nowhere, and a
message about it carries no location at all, not even a file; a position a macro
gives with `MkPos` is written exactly as given. A
message with nothing to point at — a contradiction that reached the driver, a
runtime error, whose code carries no positions — names the file alone
(ASSUMPTIONS 194).

Within a compile-time message a name, a term or a keyword of the language is
set off in backticks, `` `(List A)` `` or `` `share` ``, and a literal is left
bare, since it already reads as one: `3`, `#\a`, `"ab"`. Both compilers quote
through one function, `Env.tick` and `tick` in `self/core.sl`. A name is
shown plain where that reads back as the same name, and raw otherwise, `` `#"x y"` `` (DESIGN.md section 1). Runtime errors
are not quoted. A term is shown canonically, each piece by the spelling that
means it where the message points:

- an atom by a numeral or string literal it equals, else by the newest name
  still in scope for it, else by a fetch form that yields it there with its
  argument a name, `(level-of f)`, `(slot-of x)`, else as `__1`, `__2` and on;
- an unsolved `_` (DESIGN.md section 50) as `__?1`, `__?2` and on;
- a gensym (DESIGN.md section 63) as `__g` and its number and `_`, followed by its
  text spelled as a name is: `__g1_tmp`, `__g1_#"a b"`;
- a special form or annotation token, a fetch form's head included, by the
  newest name in scope that is `Settled`, non-erased and holds it, else as `__`
  followed by its built-in name, `__Fn`, `(__level-of f)`.

Keywords in a message's prose follow the same rule where they stand for syntax,
alone in backticks, ``mark it `notail` ``, or inside quoted code, ``written
`(share x)` ``. Plain words naming a multiplicity, as in "used at unique", stay
as written. A keyword printed as `__` and its built-in name is noted at the
binder that shadows it, `` `__notail` is `notail`, shadowed here ``.

The two numberings follow order of first mention and hold for the whole run,
so `__3` names one entry in every message it appears in, and every message
that mentions one carries a note saying what it is: `` `__?1` is the `_`
written here ``, `` `__3` is anonymous, minted here ``, `` `__Fn` is `Fn`,
shadowed here ``. An automatic slot that no name reaches is noted at its
entry, where the source wrote one: `` `__2` is the slot of the `_` written
here `` or `` `__2` is the slot of the entry bound here ``. Which atom canonicalization keeps for a class is an
accident of minting order, so two numbers may turn out to denote one thing
under later facts, and a name is shown only where it still denotes that atom
(`Env.show`, `show-t` in `self/elab.sl`). A result that fails its return type
is reported where it is written, the entry of the body's final `values` or the
final expression.

`(dump-context)` stops elaboration where it is written and reports, as one
error, what the checker knows there: the goal, the level, every entry in scope
with its type, `is` rule, multiplicity and uniqueness state, and the slots
that two or more entries share. It can be used as an expression, a statement or a type;
`(dump-context x ...)` reports just the terms named. It's a debugging aid, so
its output isn't stable (ASSUMPTIONS 196).

## How it runs a program

The reader turns the file into s-expressions. The elaborator walks
them with a scope of entries and a fact table (types and `is` rules,
read canonically), dispatching each form on its head as DESIGN.md
section 6 describes: constructor and function application by the
head's type, special forms and macros by the head's Settled value, a macro
call being replaced by the forms its function returns (DESIGN.md section 62). Elaboration
produces, for every expression, the terms and types of its values and
a piece of post-erasure code in which erased positions are gone. A
form in run position is elaborated and run at once by the evaluator,
and the entries it leaves in scope are minted Settled with the
resulting values (sections 27 and 29), which form the environment later
code runs in; inside function bodies and match branches forms compile
to code instead. The
evaluator is a plain recursive interpreter over that code; a value contains
its constructor's non-erased fields, tagged only where section 33 says an
enum carries a tag, or a closure, or a token standing for anything
erased. Unique cells permit in-place updates, while an entry written `at`
another, a parameter, a return, a match annotation entry or a field, is neither
passed nor returned physically but read from the word it is at (section
36); an at-function's call and an at-match are skipped (sections 39, 40). Every
entry has an automatic slot in the fact table, erased where the entry
is, which `(slot-of x)` names, and a slot prints by that form.

## Layout

- `lib/reader.ml` — s-expressions with `$` (DESIGN.md section 2)
- `lib/term.ml` — the restricted type grammar (section 9), de Bruijn telescopes
- `lib/env.ml` — scope entries, the fact table, canonicalization, forced unification (sections 5, 7)
- `lib/value.ml`, `lib/eval.ml` — runtime values, post-erasure code, the evaluator
- `lib/special.ml`, `lib/prelude.ml` — the special-form registry (section 54) and built-ins
- `lib/prelude.sl`, `lib/ffi.ml`, `lib/ffi_core.ml` — the source prelude, the FFI registry, and the extern implementations it and extracted programs share (section 42), the reader's tree that the prelude's `Raw` holds among them
- `lib/literal.ml` — the spellings of numeral, character and string literals
- `lib/elab.ml` — the elaborator: head dispatch, erasure, levels, match, statements, literal interning
- `lib/dump.ml` — the report `dump-context` stops elaboration with
- `lib/driver_core.ml`, `lib/program.ml` — running a `String -> String` or `Program` final value against the world, the first shared with extracted programs
- `lib/extract.ml` — OCaml extraction of the traced run-position statements and final expressions
- `lib/indent.ml` — indentation read as a claim about paren nesting, and the claim checked
- `bin/main.ml` — command line driver
- `bin/shape.ml` — where a file's forms open and close, for locating a misplaced paren
- `bin/indent.ml` — `lib/indent.ml`'s check run on its own over the files named
- `test/runtest.ml` — the test runner, interpreting and extracting each test
- `tests/` — DESIGN.md's worked examples and further tests

## Agent harness

`agent/` runs LLM agents on Sleight programming tasks, over many sessions.

- `agent/pi.py` — the harness: runs one task for a configured provider and model (`PI_*` environment variables), with `slc` as the agent's compiler, carrying a handoff file from one session to the next
- `agent/run.sh` — starts, resumes, lists and follows `pi.py` runs on DigitalOcean droplets; `agent/deploy.sh` and `agent/ssh.sh` set up a box and deploy `HEAD` to it
- `agent/rea.sh` — builds an x86-64 Linux `slc` on a temporary droplet, and creates, lists and destroys `rea` droplets for reverse-engineering it: each has Java 21, Ghidra, binutils, OCaml, Node 24, Claude Code and [REA](https://github.com/morluto/rea) registered with it, and a copy of the `slc` binary but no Sleight source, and `create` ends by signing Claude Code in to your subscription and starting a Remote Control session there; `agent/do.sh` holds the DigitalOcean helpers it shares with `run.sh`
- `agent/tasks/*.txt` — task prompts; each one's `#!pi` first line gives the files the agent sees, its work directory and run settings
- `agent/tasks/<task>/` — a task's spec and acceptance files, such as `heapsort-fast/spec.sl`, which `heapsort/` is certified against
