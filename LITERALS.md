# Literals

Numerals, character literals and string literals, in one place. They
are sugar over the prelude, recorded as implementation choices in
ASSUMPTIONS.md 47-60, 102-106 and 154; DESIGN.md section 41 leaves
numeric literals open, and SUGAR.md 5 covers `unary` and `distinct`.

## Syntax

- A numeral is a digit-only atom, `0` or `42`, with no leading zero;
  it is never a name.
- A character literal is `#\c` for a printable ASCII `c`, `#\space`,
  `#\newline`, `#\tab` or `#\xHH`.
- A string literal is `"..."`, with the escapes `\n`, `\t`, `\"` and
  `\\`.

`Literal.classify` sorts an atom into these or a name; `Literal.spell`
is its inverse.

## Denotation

- A numeral is a `Nat`, the prelude's extern Peano enum, with an
  erased `Numeral b n` proof relating it to its spelling `b`, a `Bin`
  in bijective base 2 (`BZ`; `B1 b` is 2b+1; `B2 b` is 2b+2, least
  significant digit outermost), so each number has one spelling.
  `bin-to-nat` is extern over a structural model and returns the
  number with the proof.
- A character literal is a `Char`, the source newtype over `U8`, which
  is a newtype over a `Nat` below `u8-modulus`; the bound's proof is
  built by reflection on `lt-dec`. Any byte is a `Char`.
- A string literal is a `String`, the prelude's extern enum of `SNil`
  and `SCons` over `Char`, held by the FFI as a slice.

## Hoisting and interning

A literal is sugar for run-position statements over the prelude,
hoisted to just before the top-level form that first mentions it,
elaborated in the prelude's own scope so that shadowing cannot reach
them, and interned by spelling, one entry per program; the entry is
not in the scope list and an occurrence resolves through
`Env.literals` (`lit-lookup` in slc). The reference runs the source
`Literal.source` writes; slc's `intern` builds the same entries with
the FFI's payload as the value.

## What the checker sees

- A numeral is opaque: a call's result with no `is` rule, beside its
  erased `Numeral` proof. `3` is not `(Succ (Succ (Succ (Zero))))`.
  `(numeral-of lit)` yields a literal's proof by its spelling, so two
  spellings equated in a branch refute it; `unary` and `distinct`
  mint the one rule or refutation a `Succ` shape or a disjointness
  needs, through the prelude's `Numeral` lemmas.
- A character literal is transparent down to its opaque `Nat`: the
  hoisted `let` forwards `is (MkChar (MkU8 n p))`, `n` the code's
  numeral entry.
- A match or `let-match` refused for a branch left standing, when its
  scrutinee or the scrutinee's type holds a numeral or character
  literal, carries a note naming those literals, as written, with
  `unary`, `distinct` and `numeral-of`; a numeral that is a named
  character's code is left out, the character standing for it.
- A string literal is opaque: a `Const` `String` with no rule, in
  both compilers. `comptime-match` reads its value; a match inside a
  function walks the runtime slice. A rule exposing its characters
  would make every canonical form that mentions the literal expand
  to all of them.

## Runtime and printing

Under the FFI a `Nat` is a zarith integer, a `Char` its byte and a
`String` a slice of an OCaml string; under `--no-extern` the models
run instead, and a numeral around a million overflows the
interpreter's stack in unary. A value of the three types prints as
the literal it reads back from, through `Ffi_core.lit_char` and
`lit_string`, shared by the interpreter, extracted programs and slc's
output.

## Where the code is

`lib/literal.ml`, `Elab.hoist`, `Elab.elab_unary`, `Elab.elab_distinct`, `Elab.literal_notes`
and the `NumeralOf` form in `lib/elab.ml`; `classify`, `intern`,
`intern-string`, `record-literal`, `lit-lookup` and `noted-error` in `self/elab.sl`;
`lit_char` and `lit_string` in `lib/ffi_core.ml`; the prelude's `Nat`,
`Bin`, `Numeral`, `bin-to-nat`, `U8`, `Char`, `String` and the
`Numeral` lemmas.
