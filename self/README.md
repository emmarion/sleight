# slc: a compiler from SL to OCaml, written in SL

`self/` holds a compiler for the language of DESIGN.md (tentatively
"SL"), written in that language and compiling it to OCaml. It was
written by a Claude session working autonomously at the owner's request
("let's self host"); everything here is that session's reading of the
design and of the reference implementation in `lib/`, and nothing here
is a design decision. Where this file makes a claim about the language,
the tests under `self/bootstrap.sh` are the evidence, and a claim the
tests do not make is a mistake in this file.

## What it is

A *trusting* compiler. The reference interpreter in `lib/` is the
checker: it verifies proofs, refutes branches, compares types and reads
levels. `slc` does none of that. It assumes its input was accepted by
the reference, and does only the elaboration that code generation
needs: name resolution, the kind and type of every head (constructor,
function, type, special form), erasure by position (DESIGN.md section
20), each match's `Matchable`, tag and discriminants (sections 12, 17,
38), the forced facts a branch adds so that a later match on a refined
type variable finds its `Matchable` (section 18), run-position
statements run at once (sections 16, 34), and literals. A proof is
elaborated only for its type; a decrease annotation is stripped; an
`(absurd C)` branch produces no code. Garbage in, garbage out: an
unchecked program may compile to OCaml that does anything.

The compile-time part is the "comp time / Const stuff" the owner asked
the compiler to interpret: `self/eval.sl` is a plain recursive
interpreter over the post-erasure code, run on every run-position
statement, and the values it computes are embedded in the OCaml output
as data, closures included, rather than recomputed (ASSUMPTIONS 61's
reading of the owner's intent). Extern types and functions run as the
host's own `Nat`, `U8`, `Bin`, `String` and `Dec` (section 41).

## Files

- `base.sl` — booleans, pairs, `Nat`/`Char`/`String` helpers over the
  prelude's externs, `Bin`-keyed identifiers with a trie map over them,
  a trie map keyed by names, list helpers, and a rope of output chunks.
- `reader.sl` — s-expressions with `$` (sections 1-2): a structural
  tokenizer and a fold over the tokens with a stack of open forms.
- `core.sl` — terms with de Bruijn telescopes (section 5), the
  special-form registry (section 27), runtime values and post-erasure
  code, the scope environment and fact table (sections 3, 18),
  canonicalization, instantiation, the recording half of forced
  unification, term identity, and the built-in entries.
- `eval.sl` — the compile-time interpreter.
- `elab.sl` — the elaborator: head dispatch, calls, matches, the five
  statements, literals, the post-erasure normalization behind `tail`
  and `delegate` (ASSUMPTIONS 72), and the top level.
- `runtime.ml` — the OCaml runtime every compiled program starts with:
  `lib/ffi_core.ml`'s implementations, one type `v` of runtime values,
  the extern functions, and the driver of `lib/program.ml`.
  `gen_header.py` turns it into `header.sl`, the same text as SL string
  literals; regenerate `header.sl` after editing `runtime.ml`.
- `emit.sl` — extraction to OCaml, and a generated printer per type for
  a final function's result.
- `main.sl` — the entry point, an `IO` program (ASSUMPTIONS 56).
- `bootstrap.sh` — builds and checks everything, below.

## Running it

```sh
dune build
self/bootstrap.sh          # extracts slc natively, checks the tests, self-compiles
_build/self/slc -- lib/prelude.sl tests/list.sl > list.ml
ocamlfind ocamlopt -package zarith -linkpkg list.ml -o list && ./list
```

`slc` takes the files to compile as its program arguments, the prelude
first, elaborates them in one scope in order as the interpreter does,
and writes the OCaml program to stdout; elaboration errors go to stderr
with exit code 1. The compiled program takes its own arguments after
`--` and behaves as `lib/program.ml` would: a final `String -> String`
function runs over stdin, an `IO` value is performed, a function from
no arguments is applied and its result printed, and any other value is
printed.

`self/bootstrap.sh` does three things. It extracts `slc` to a native
binary with the reference extractor (`--extract`), since running the
compiler under the reference *interpreter* takes seconds per file where
the native binary takes milliseconds. It compiles every `tests/*.sl`
that runs (those without an `; error:` directive, which need the
checker) with that binary, builds and runs the result with the test's
stdin and arguments, and compares stdout, stderr and exit code with the
reference interpreter run on the same files. And it compiles `slc` with
`slc`, then compiles `slc` again with the compiler that produced, and
requires the two outputs to be byte-for-byte identical, which is the
self-hosting fixpoint. At the time of writing all 116 runnable tests
match and the fixpoint holds; the whole script takes under a minute.

## Choices, and where they differ from the reference

Each of these is this session's choice, made without the owner, and
recorded so it can be revisited.

- **One OCaml type for every value.** `type v = Tag of int * v list |
  Tup of v list | Nat of Z.t | Str of slice | Fn of (v list -> v) | Mat
  of ... | U`. `lib/extract.ml` emits an OCaml variant type per ADT
  under `Obj.t`; this emitter keeps section 38's representation
  (a value is the tuple of its many fields, one bare, none `U`, a tag
  only for an enum with more than one non-phantom constructor, so
  `coerce` is the identity and a newtype is its field) but through
  typed constructors, so a wrong extraction is an OCaml type error or
  an `absurd ()` rather than a segmentation fault. Every function,
  first-class constructor and top-level definition is an `Fn`, and every
  call is `app f [args]`, which OCaml compiles to a tail call in tail
  position: three million `tail`-marked frames run in constant stack.
- **Identifiers are `Bin` numbers**, not `Nat`s: comparing two is
  logarithmic under the FFI, a fresh one is a successor, and the
  environment's maps are tries over their digits. OCaml names carry the
  digits, least significant first: `v22111222_length`.
- **Termination is by fuel where the recursion is not structural.**
  Canonicalization, the interpreter, the elaborator, the emitter's
  closure hoisting and forced unification each take a `Nat` that
  decreases along the call stack (not a step count), so a fuel of
  100000 bounds depth, not work. Running out returns an error value,
  never a wrong answer silently. Where recursion is on a constructor
  argument (the reader, maps, term traversals, evaluation of
  sub-expressions) it is the ordinary `subterm` decrease.
- **Errors are values.** The language has no exceptions, so an
  elaboration error is recorded in the environment and reported at the
  end, and the offending code becomes `failwith` in the output; a
  runtime error in the interpreter is a `VError` value that prints as
  `<error: ...>` and embeds as `failwith`.
- **Sharing inside embedded data is not preserved.** `lib/extract.ml`
  names a block met twice; SL has no physical identity, so a value
  reached twice inside one embedded constant is written twice. A
  top-level Const is still emitted once and referenced by name.
- **A final value printed at compile time is printed from its text**,
  not through a generated printer as ASSUMPTIONS 66 chose; the
  generated printer exists only for a final function's result, which is
  computed by the compiled code.
- **Output is a rope written chunk by chunk.** Consing a `String`
  copies under the FFI, so the compiler never builds a long string; the
  OCaml text is a tree of small chunks flushed through one `WriteOut`
  request each.
- **The driver's knowledge of the prelude is fixed in `runtime.ml`**:
  the constructor indices of `IO`, `Maybe`, `Result`, `List` and `Unit`
  and the shapes of `Nat`, `U8`, `Char` and `String` are written into
  `run_io`, `to_string` and `of_string`, where `lib/extract.ml` reads
  them off the prelude's constructors. A changed prelude needs a changed
  runtime.
- **`lt-dec` and `Dec` are extern** (ASSUMPTIONS 90), so that the
  compiler's comparisons of characters, digits and tags are constant
  time under the FFI; the source models are unchanged.
- **Not modelled**: `numeral-of` (its erased proof is never needed for
  code generation, so the form yields an erased placeholder), the
  `--no-extern` mode (the compiler's interpreter always runs the FFI's
  externs, and the output always uses them), and macros, which the
  reference does not implement either.
