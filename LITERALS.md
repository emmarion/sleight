# Literals

How numerals, character literals and string literals are handled, in
one place. Everything here is gathered from ASSUMPTIONS.md 47-60,
102-106 and 154 and from the code they describe; it decides nothing
new, and where it states how the checker or the runtime behaves, the
tests named are the evidence. DESIGN.md section 41 still records
numeric literals as open, and section 26 sends sugar to SUGAR.md,
whose section 5 covers the two rewrite forms over numerals.

## Syntax (lib/reader.ml, lib/literal.ml, self/elab.sl's classify)

- A **numeral** is a digit-only atom: `0`, `42`. A leading zero is
  refused (`01`), and a numeral is never a name, so `Env.bind` refuses
  to bind one (ASSUMPTIONS 51, 55).
- A **character literal** is `#\c` for a printable ASCII `c`,
  `#\space`, `#\newline`, `#\tab`, or `#\xHH` (ASSUMPTIONS 52). The
  quote was left free for a future `Raw`.
- A **string literal** is `"..."`; the reader unescapes `\n`, `\t`,
  `\"` and `\\` (ASSUMPTIONS 60).

`Literal.classify` sorts an atom into these or `Name`; `Literal.spell`
is its inverse and is what a printed value reads back through.

## What each denotes (lib/prelude.sl)

- A numeral is a `Nat`, the prelude's extern Peano enum, related by
  the erased relation `Numeral : ((Bin) b) ((Nat) n) -> Type` to its
  spelling `b`, a `Bin` in bijective base 2 (`BZ`, `B1 b` = 2b+1,
  `B2 b` = 2b+2, least significant digit outermost), so each number
  has one spelling; `bin-to-nat` is extern over a structural model and
  returns the number with its proof (ASSUMPTIONS 50).
- A character literal is a `Char`, the source newtype over `U8`,
  itself a newtype over a `Nat` with an erased bound `(Lt n
  u8-modulus)`; any byte is a `Char` (ASSUMPTIONS 49). The proof of the
  bound is built by reflection, `lt-dec` decided and `comptime-match`ed
  (ASSUMPTIONS 52).
- A string literal is a `String`, the prelude's extern enum modelled
  as a cons list of `Char` (`SNil`, `SCons`), held by the FFI as a
  slice (ASSUMPTIONS 48).

## Hoisting and interning (Elab.hoist, self/elab.sl's intern)

A literal is sugar for run-position statements over the prelude,
hoisted to just before the top-level form that first mentions it and
run there (section 24 lets the top level call freely), elaborated in
the prelude's own scope so that shadowing `let` or `bin-to-nat` cannot
reach them; the minted entries are not in the scope list, and an
occurrence resolves by spelling through `Env.literals` (`lit-lookup`
in slc). Each distinct spelling is one entry per program
(ASSUMPTIONS 51, 52, 60). The reference runs the source
`Literal.source` writes, `(let (many _) (erased _) (bin-to-nat
<spelling>))` for a numeral, the reflection route for a character, the
characters consed up for a string; slc's `intern`, `intern-numeral`
and `intern-string` build the same entries directly, with the FFI's
payload as the value.

## What the checker sees

This is the part with content, and the one place the two compilers
have differed.

- A **numeral** is opaque: a call's result with no `is` rule, beside
  an erased `Numeral` proof to its spelling. `3` is not `(Succ (Succ
  (Succ (Zero))))` and `(Vec A 3)` is not `(Vec A (Succ ...))`
  (ASSUMPTIONS 51). `(numeral-of lit)` yields a literal's proof, by its
  spelling, so that inside a branch that has equated two literals each
  still fetches its own and the two spellings refute the branch
  (ASSUMPTIONS 53, `tests/numeral_of_branch.sl`). `unary` and
  `distinct` (SUGAR.md 5) mint the one rule or refutation a `Succ`
  shape or a disjointness needs, through the prelude's `Numeral`
  lemmas (ASSUMPTIONS 103-106), with a ceiling of 4096 steps the
  session chose.
- A **character literal** is transparent down to its opaque `Nat`: the
  hoisted `let` forwards `is (MkChar (MkU8 n p))`, so a match on a
  character sees its constructor and `n` is the code's numeral entry
  (ASSUMPTIONS 52, `tests/char.sl`).
- A **string literal** is opaque: a `Const` `String` with no rule.
  `comptime-match` reads its value (`tests/string_literal.sl`), and a
  match inside a function walks the runtime slice. Until d1a9a88 the
  reference forwarded the hoisted `SCons` chain as the literal's rule,
  so every canonical form mentioning the literal expanded to all of
  its characters and a chain of n `RCat`s over such literals cost
  n² times their length to elaborate (`self/header.sl` was 16 of
  the reference's 24 seconds on slc's sources); slc had always
  interned a literal as an opaque constant. The owner chose opaque for
  both. We believe no test told the two readings apart, `comptime-match`
  reading the value under either; a plain `match` refuted through a
  literal's characters would have.

## Runtime and printing

Under the FFI a `Nat` is a zarith integer, a `Char` its byte, a
`String` a slice of an OCaml string; stripped (`--no-extern`) the
models run instead, and a numeral around a million overflows the
interpreter's stack when computed in unary (ASSUMPTIONS 54). A value
of any of the three types prints as the literal it reads back from
(ASSUMPTIONS 154, the owner's decision): decimal, `#\c` or its escaped
spelling, a quoted string with the four escapes, through
`Ffi_core.lit_char` and `lit_string`, which the interpreter, an
extracted program and slc's output all share.

## Where the code is

`lib/literal.ml` (classify, key, spell, source, the `Bin` spellings
and the `BinSucc` witness), `Elab.hoist`, `Elab.elab_unary` and
`elab_distinct`, the `NumeralOf` form in `lib/elab.ml`; `classify`,
`literal-error`, `intern`, `intern-string`, `record-literal` and
`lit-lookup` in `self/elab.sl`; `lit_char` and `lit_string` in
`lib/ffi_core.ml`; the prelude's `Nat`, `Bin`, `Numeral`,
`bin-to-nat`, `U8`, `Char`, `String` and the `Numeral` lemmas.

## Open

DESIGN.md section 41's numeric literals; SUGAR.md 5's open items on
`unary`; whether `(numeral-of "...")` should mean anything, it being
an error today (ASSUMPTIONS 53).
