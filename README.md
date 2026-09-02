# special-lang

A prototype OCaml interpreter for the language recorded in DESIGN.md.
KERNEL.md and SUGAR.md are further design notes; SPEC-REVIEW.md lists
the spec's open points and ASSUMPTIONS.md the assumptions the
interpreter makes about them.

## Build and run

```sh
apt-get install -y ocaml ocaml-dune
dune build
dune exec bin/main.exe tests/list.sl tests/map.sl tests/coerce.sl
dune test
```

Files given on one command line share a scope, in order. A file is a
sequence of statements, optionally ending in an expression whose value
is printed.

## Layout

- `lib/reader.ml` — s-expressions with `$` (DESIGN.md section 2)
- `lib/term.ml` — the restricted type grammar (section 5), de Bruijn telescopes
- `lib/env.ml` — scope entries, the fact table, canonicalization, forced unification (sections 3, 18)
- `lib/value.ml`, `lib/eval.ml` — runtime values, post-erasure code, the evaluator
- `lib/special.ml`, `lib/prelude.ml` — the special-form registry (section 27) and built-ins
- `lib/elab.ml` — the elaborator: head dispatch, erasure, levels, match, statements
- `bin/main.ml` — command line driver
- `tests/` — DESIGN.md's worked examples and further tests
