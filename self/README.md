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

A compiler that checks what it compiles. The reference interpreter in
`lib/` is the arbiter of the language; `slc` does the same elaboration
(DESIGN.md sections 3-5, 9, 12, 16-20, 34, 38), with every check of
`lib/elab.ml` and `lib/env.ml` ported: canonicalize-then-compare
identity of types and values, erasure by position, the call-site level
and subterm proofs, forced unification that refutes a branch by
contradiction and the one-real-branch rule, `comptime-match`
verification against the stored value, `let-match` binding outward, the
tail and delegate marks on the normalized code, newtype shape, extern
claims, the opening of a `Matchable` or `Newtype` that every read of one
requires and the contradiction `open-absurd` cashes in (ASSUMPTIONS
139-142), and the reader's and literals' syntax errors; `unary` and
`distinct` (SUGAR.md 5) expand to the prelude calls the reference
writes down, in the prelude's scope as there; a `_` argument (SUGAR.md 6)
is solved as the reference solves it, by a meta the scope and the
type-directed lookups never see, and the unifier's forcing mode is a
flag. Its error messages are the reference's, and
`self/bootstrap.sh` requires every test that expects an error to be
refused with a message mentioning the expected text. What it does not
do: verify that the interpreter's evaluation is honest (KERNEL.md's
interpreter-trust obligation applies to it as much as to `lib/`).

The compile-time part is the "comp time / Const stuff" the owner asked
the compiler to interpret: `self/eval.sl` is a plain recursive
interpreter over the post-erasure code, run on every run-position
statement, and the values it computes are embedded in the OCaml output
as data, closures included, rather than recomputed (ASSUMPTIONS 61's
reading of the owner's intent). Extern types and functions run as the
host's own `Nat`, `Half` and `String`, and a `Rope` is flattened by the
host (section 41); a `U8` or a
`Char`, both newtypes, is its `Nat` (section 38).

## Files

- `base.sl` — booleans, pairs, `Nat`/`Char`/`String` helpers over the
  prelude's externs, a trie map over `Nat` identifiers walked by the
  prelude's `Half`, a trie map keyed by names, list helpers, and helpers
  over the prelude's `Rope` (ASSUMPTIONS 122). Since ASSUMPTIONS 121 its deciders and lookups return evidence: the
  orders on `Nat` and `String` are relations decided into the prelude's
  `Cmp`, so a match on `CEq` forces the two equal; a trie lookup returns
  `Hit` with a `MapsTo` proof or `Miss` with an `Absent` one; `list-nth`
  returns `Nth` or `OutOfRange` evidence, `length` a `Length` proof and
  `list-append` a `Concat` proof. `nat-eq`, `str-eq`,
  `list-length` and friends are forgetful wrappers over those, for the
  sites that combine several decisions with `and`/`or`.
- `heap.sl` — a store for the compile-time interpreter, parametric in
  its block type: addresses below a bound, carried as their bijective
  spelling with erased `Numeral` and `Lt` proofs, widened by a `coerce`;
  and a Braun tree of blocks sized by its count (the LSB-first trie on
  the spelling), whose `alloc` and `deref` the session reads as total by
  the size alone, the lemmas over the prelude's `Double` and `Numeral`
  doing the work.
- `reader.sl` — s-expressions with `$` (sections 1-2): a structural
  tokenizer, a word being a slice of the source cut by the prelude's
  `str-split` under an `Add` invariant counting the characters taken
  and remaining, a string literal a `Rope` of characters flattened
  once, and a fold over the tokens with a stack of open forms.
- `core.sl` — terms with de Bruijn telescopes (section 5), the
  special-form registry (section 27), runtime values and post-erasure
  code, the scope environment with its fact table and its list of opened
  objects (sections 3, 18; ASSUMPTIONS 139),
  canonicalization, instantiation, forced unification with its three
  contradictions (section 18), term identity, and the built-in entries.
- `eval.sl` — the compile-time interpreter over the store: every value
  is an address, every step returns the grown store with a proof of the
  growth by which what was held before is widened, and a run-position
  statement is a session that reads the store out of the environment
  and puts it back (ASSUMPTIONS 131). A tail position of the code being
  interpreted -- a `let`'s body, a match branch, a call's own tail call
  -- is reached by a tail call, so interpreting a tail call costs no
  host stack and the fuel, not the stack, is what bounds such a loop
  (ASSUMPTIONS 150). A non-tail call in interpreted code still holds a
  host frame, as the standing exception below says.
- `elab.sl` — the elaborator and checker: head dispatch, calls with
  their proofs, matches with refutation and `else`, the seven statements, literals
  with their `Numeral` proofs, the post-erasure normalization behind
  `tail` and `delegate` (ASSUMPTIONS 72) and their validation, the
  expansion of `unary` and `distinct`, and the top level.
- `runtime.ml` — what the OCaml runtime every compiled program starts
  with adds to `lib/ffi_core.ml` and `lib/driver_core.ml`: `absurd`,
  the phantom indices of narrowing, the identity `Matchable`, each
  extern type's unwrap and wrap over `Obj.t`, and the `world` the
  driver runs in. `gen_header.py` turns the three files into `header.sl`, the same
  text as one `Rope` of SL string literals; regenerate `header.sl`
  after editing any of them.
- `emit.sl` — extraction to OCaml in the reference's scheme: a walk
  collecting the shapes and narrowings a program needs, the blocks and
  groups as OCaml, the driver's operations, and a generated printer
  per type for a final function's result.
- `main.sl` — the entry point, an `IO` program (ASSUMPTIONS 56).
- `bootstrap.sh` — builds and checks everything, below.

## Running it

```sh
dune build
self/bootstrap.sh          # extracts slc natively, checks the tests, self-compiles
_build/self/slc -- lib/prelude.sl tests/list.sl > list.ml
ocamlfind ocamlopt -package zarith,unix -linkpkg list.ml -o list && ./list
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
with that binary, the tests in parallel: a test with an `; error:` directive must be refused
with a message mentioning the text, and any other is built (to bytecode,
whose compiler is the faster one at that size) and run with
the test's stdin and arguments, its stdout, stderr and exit code
compared with the reference interpreter run on the same files. And it compiles `slc` with
`slc`, then compiles `slc` again with the compiler that produced, and
requires the two outputs to be byte-for-byte identical, which is the
self-hosting fixpoint. At the time of writing all 151 runnable tests
match, all 98 error tests are refused with the expected text, and the
fixpoint holds; the whole script took under half a minute on the
machine the last session measured it on, most of it the bytecode
compiles of the tests' output.

## Choices, and where they differ from the reference

Each of these is a session's choice, made without the owner unless
the entry says otherwise, and recorded so it can be revisited.

- **The reference extractor's scheme, by the owner's decision** that
  `lib/extract.ml` is the specification of this emitter and the two
  back-ends agree; the purpose the owner stated is the runtime cost of
  the extracted program. Every value is an `Obj.t`, the casts free.
  A tagged type (an enum with more than one non-phantom constructor)
  is an OCaml variant declared once per *shape*, the sequence of
  `many`-field arities of its non-phantom constructors, so every ADT of
  one shape shares one type; an untagged type, a union and a newtype
  are their fields as they stand, `()`, the field, or a tuple, with no
  declaration; an extern type is its `Z.t` or slice under `Obj.t`,
  which the FFI unwraps one level into the shape its model's
  constructors describe and wraps back (`lib/ffi_core.ml`'s views,
  laid out as the model's own type, which the reference checks at the
  `extern` claim), so it is matched and built like any tagged type; since ASSUMPTIONS 133 an extern type with a template in `lib/ffi_templates.txt` is matched and built through the template instead, the view kept for held values, and `slc -- --no-templates ...` strips the templates. A constructor
  application whose head the elaborator sees is the direct build; a
  call whose head is a named function is a direct OCaml call; a match
  on a tagged type is a direct `match` on the shape, and when the
  elaborator's `live` set (the branches present and the constructors an
  `else` stands for) leaves constructors out, on a phantom-index GADT
  copy of the shape declared once per shape and live set, so that OCaml
  tests nothing for the refuted ones and a match with one live
  constructor is a bare projection; an exhaustive match without `else`
  has no default arm. A first-class constructor is its curried builder,
  a constant one the constant; a `Matchable` at runtime is an
  `Obj.t -> Obj.t`, the identity for a plain type and for an extern
  type the unwrap into the shape its constructors describe, so a match
  through a held `Matchable` is the same direct match on the unwrapped
  value; the elaborator mints that shape from the `Matchable`'s type.
  `absurd ()` remains only where the elaborator refuted every branch. A wrong refutation would misdispatch
  silently here, as ASSUMPTIONS 63 records for the reference; the
  interpreter is the checked path. Function calls in tail position are
  OCaml tail calls, so three million `tail`-marked frames run in
  constant stack.
- **Identifiers are `Nat`s**: comparing two is `nat-cmp`, a fresh one
  is `Succ`, and the environment's maps and the store are tries over
  their halves (the prelude's `Half`, whose `nat-halve` is the identity
  under the FFI), with `Double` in the evidence where the digits used
  to be; the bijective spelling (`Bin`, a plain type now) appears only
  where a numeral literal is spelled into its `Numeral` proof. OCaml
  names carry the id in decimal: `v1234_length`.
- **Termination is structural except in the interpreter and the
  generated printer.** Those two take a `Nat` that decreases along the
  call stack (not a step count), so a fuel of 1000000 or 100000 bounds
  depth, not work; running out returns an error value, never a wrong
  answer silently. The fuel decreases on a tail call too, so it, rather
  than the host stack, is what a long compile-time loop now meets
  (ASSUMPTIONS 150). Everything else recurses on a constructor argument
  by the ordinary `subterm` decrease the reference checks: the reader on
  its tokens and frames, maps and term traversals on their structure,
  the emitter on the closure whose code it emits (every piece of code
  carrying an erased proof that it lies inside it), and the elaborator
  on the raw it elaborates. What the elaborator parses from a raw before
  elaborating it (telescope entries, function and type headers, branch
  parts, a call's decrease annotation) is a structure indexed by that
  raw, whose entries carry erased proofs that the raws they hold lie
  inside it, so descending into one of them is a checked decrease; where
  a function hands its whole raw to another, a `Steps` budget decreases
  instead, one step per hop, its size fixed by the code's shape and
  stated in the type, so the zero case is refuted rather than reported
  (ASSUMPTIONS 96).
- **Canonicalization and forced unification terminate by proof**
  (ASSUMPTIONS 93 and 94). The fact table is a trie whose type index
  counts its rule-free entries; the rewrite rules are a list in the
  order they were appended, each canonical when appended; and erased
  invariants on the environment say the two agree and that no rule
  mentions a key at or before it. Canonicalization returns a proof that
  its result mentions only rule-free entries, a chase recurses on the
  rules after the one it follows, and the invariants make the lookup in
  that suffix total. Unification takes the count as its measure: a step
  is structural on canonical terms until a binding rules an entry out,
  which the elaborator sees as the count stepping down, and the rest is
  re-canonicalized at the smaller count. The table is also indexed by
  a bound on its keys, kept equal to the environment's id counter, so
  binding a fresh id refutes the position being taken (ASSUMPTIONS 97).
  All of it is erased, so the compiled compiler runs the same code as
  before.
- **Errors are values.** The language has no exceptions, so an
  elaboration error is recorded in the environment and elaboration goes
  on; every error is reported at the end and no OCaml is written. Where
  the reference stops at the first error, `slc` may report a few more
  that follow from it. A message names the file and the line of the
  innermost form being elaborated, in the reference's `path:line:
  error:` format; on every error test the first message is the
  reference's, line included. A runtime error in the interpreter is an error
  block that prints as `<error: ...>`.
- **The opened objects live in the fact table with their canonical
  names.** The table (`Table n f c`) holds, beside its proofs, the
  opened list (ASSUMPTIONS 139): each entry with its kind and the names
  its type holds canonically, the type constructor first, an index from
  name to the objects naming it, and the objects *touched* since section
  19's invariant was last restored. The list is indexed by the table's
  facts, `Opens n f`, and only the functions that change the facts mint
  one at a new index, each from the proof of the change (`Ins` for a
  fresh entry, `Out` for a ruling out), so the checker refuses a table
  whose opened objects are another table's; ruling a variable out
  (`rule-into`) refreshes the objects naming it and touches them. The
  invariant is then restored for the touched objects alone: a pair
  sharing a name after a forcing has a touched member, the rest having
  been disjoint before, and the pair chosen is the one the full search
  chose (the newest object sharing with an older one, and the newest
  such older one), so the output is unchanged; `listed`,
  `find-matchable` and `find-newtype` read the cached names. A forcing
  hands its environment back as a `Forced`, which only `merge-all` and
  `merge-opens` read an environment out of, so a forcing without the
  merge after it does not type-check; the printers force too and merge
  before reading (the reference's `Env.forced` is the same shape). What the
  index does not prove is that a cached name is canonical: `MkOpens` can
  be applied anywhere, so the discipline is that it appears only in the
  transports and the table functions of core.sl. The session that made
  this measured the compiler compiling itself going from about 66
  seconds to under 3; `bench/bench.sh` repeats the measurement.
- **Sharing is the store's.** `lib/extract.ml` names a block met twice
  by physical identity, which SL lacks; here every value the compile-time
  interpreter makes is a block in `heap.sl`'s store, and the emitter
  writes each block a Const or a final reaches once, in address order,
  each block's addresses being below its own (ASSUMPTIONS 131). A group
  is one top-level `let rec`, its members named by their entries
  qualified by the group's address, so a group's code is written once
  however many closures name it, and a function value is its member's
  closure; a group's captured frames are the names of the blocks and
  members it closed over.
- **A final value printed at compile time goes through the generated
  printer**, as ASSUMPTIONS 66 chose, a block carrying no constructor
  names; a function-valued final prints its name as the reference does,
  and the printer's memo keys a type with the variables minted during
  printing made a wildcard, as `lib/extract.ml` does.
- **Output is a rope written chunk by chunk.** Consing a `String`
  copies under the FFI, so the compiler never builds a long string; the
  OCaml text is a tree of small chunks flushed through one `WriteOut`
  request each.
- **The driver's operations are emitted per program**, as
  `lib/extract.ml` does: `lib/driver_core.ml` takes a record of direct
  builds and matches over the prelude's `Nat`, `U8`, `Char`, `String`,
  `Maybe`, `Result`, `Unit`, `List`, `Pair`, `EntryKind`, `Change` and
  `IO`, found by name in the
  prelude's scope, so no name is looked up while a program runs. A
  prelude renaming those needs a changed emitter.
- **The elaborator's group carries a budget of sugar expansions** as its
  first `subterm` parameter, ahead of the raw. `unary` and `distinct`
  write their prelude calls down when the form is reached, as the
  reference does, and the raw they then elaborate is of the elaborator's
  own making, which is no descent into the form; spending one unit of
  the budget is the decrease the checker sees instead. The forms are
  built as raws rather than text read back (ASSUMPTIONS 124). A
  generated form contains no sugar, so the budget is one; its zero case
  is reported as an internal error, not refuted, since the sugar forms
  are found by resolving a head in the prelude's scope, which no proof
  here speaks about (ASSUMPTIONS 111, 124).
- **Post-erasure code carries its erasures.** `Code ms` is indexed by
  the multiplicities of the values it produces, and the lists a node
  holds in step with that, a `values`' codes and a `let`'s ids, come
  with a proof that they sit at the many positions (ASSUMPTIONS 125);
  the interpreter returns the many values as a list beside an erased
  `Picked` reading it back against the index, and binds a `let` without
  a count check. What it cannot know statically, a closure's arity and
  a constructor's fields, is fitted once at the boundary. Because the
  index travels as a proof rather than as the shape of the values, a
  call and its callee hand back the same data and nothing converts
  between them along a call, which is what lets the interpreter reach a
  call in tail position by a tail call (ASSUMPTIONS 150).
- **Post-erasure code is indexed by its scope.** `Code ctx ms` names,
  beside its erasures, the frames of non-erased ids the code binds:
  one frame per function's parameters, per group, per `let` and per
  branch, innermost first. A variable carries the path to its frame
  and place (`Mem`, `At`), so the interpreter's environment is one list
  of values per frame and a lookup is total; a `let` extends the
  environment with the values picked from the same positions as its
  ids. A Const entry's value is embedded in the code with the entry
  that named it (section 34), so the top level binds no frames and run
  position is the empty context: a statement runs at compile time
  exactly when its context is empty, and a branch body, an `else` body
  included, always sits under a frame. The elaborator decides each
  variable's place when it emits it (ASSUMPTIONS 127); the invariant
  that every non-erased entry in scope has one is not yet a proof, so
  a miss there is an internal error at elaboration, no longer a value
  at runtime.
- **Code is built at the expectation.** Each case of the expression
  elaborator returns `Code ctx expect` (ASSUMPTIONS 129): a one-value
  case builds at its position and `single` identifies that shape with
  the expectation under `pos-of`'s `PosOf` proof, a call is projected
  onto the expectation whenever its returns lockstep with it, and the
  count of an expression's values is still reported once at its end.
- **Types travel with their terms.** `elab-term` returns the type it
  computed beside the term, `check-args` the types of the arguments,
  and an `is` entry keeps the type computed when its clause was
  elaborated (ASSUMPTIONS 126), so nothing reads a type off a term
  after the fact and there is no `infer`.
- **Lists walked together carry evidence.** Where the elaborator walks
  two lists in step, a telescope and the metas opened for it, a `let`'s
  binders and the results and values they bind, an expectation and the
  results checked against it, the second list comes with a `Lockstep`
  proof relating it to the first (ASSUMPTIONS 124), minted where the
  count was decided: `elab-expr` fits its results to the expectation
  after reporting a count error, so a consumer refutes the short list
  rather than filling in a placeholder.
- **The sources write `_` and `$` wherever the checker allows** (SUGAR.md
  6, DESIGN.md section 2; ASSUMPTIONS 116): an erased index is left to
  unification where a later argument or the expected telescope fixes it,
  and a last argument on one line opens with `$`.
- **`nat-cmp` is extern** (ASSUMPTIONS 90, 120, 123), so that the
  compiler's comparisons of characters, digits and tags are constant
  time under the FFI; `Cmp` itself is plain source, built by the FFI
  through its constructor, which since ASSUMPTIONS 151 the compile-time
  interpreter builds too, finding the constructors on the model's own
  return type rather than running the model.
- **The FFI's names are decided once.** An `extern` mark is looked up
  in the FFI's table where it is read and kept as an `Extern` or
  `ExtType` constructor (ASSUMPTIONS 128), the former indexed by its
  arity, so the interpreter's `apply-extern` and `ext-construct` and
  the emitter's runtime names dispatch on an enum rather than compare
  strings, and a model whose `many` parameters do not number the
  implementation's arity, or whose shape is not the one the
  implementation's view has, is refused at the mark, as the reference
  does; the arguments still reach an extern as the list the
  elaborator counted against its model. `apply-extern` is total
  (ASSUMPTIONS 151), so a claimed extern always runs.
- **Not modelled**: the `--no-extern` mode (the compiler's interpreter
  always runs the FFI's externs, and the output always uses them),
  the reference's warning for a phantom
  constructor with a `many` field (recorded but not printed), and
  macros, which the reference does not implement either. A string
  literal is not `is`-transparent to its characters as the reference's
  is (ASSUMPTIONS 60); `numeral-of` on one is refused as there.
