# Literals

Numerals, character literals and string literals are sugar over the
prelude: each stands for values the prelude's own types already
express, and an implementation must give a program with literals the
meaning it would have with those values written out. DESIGN.md
section 41 leaves numeric literals open; SUGAR.md 5 covers `unary` and
`distinct`; the prototype's choices are recorded in ASSUMPTIONS.md
47-60 and 154.

## Syntax

- A numeral is a digit-only atom with no leading zero, `0` or `42`.
  It is never a name: a binder spelled as a numeral is an error.
- A character literal is `#\c` for a printable ASCII `c`, `#\space`,
  `#\newline`, `#\tab` or `#\xHH`, `HH` two hexadecimal digits.
- A string literal is `"..."`, with the escapes `\n`, `\t`, `\"` and
  `\\`.

## Denotation

- A numeral denotes a `Nat`, the prelude's extern Peano enum, together
  with an erased proof `(Numeral b n)` relating it to its spelling `b`,
  a `Bin` in bijective base 2: `(BZ)` is zero, `(B1 b)` is 2b+1 and
  `(B2 b)` is 2b+2, least significant digit outermost, so each number
  has exactly one spelling. These are the two values
  `(bin-to-nat b)` returns.
- A character literal denotes a `Char`, the prelude's newtype over
  `U8`, itself a newtype over a `Nat` below `u8-modulus`, together
  with the erased proof of that bound. Any byte is a `Char`.
- A string literal denotes a `String`, the prelude's extern enum of
  `SNil` and `SCons` over `Char`: its characters consed up, in order.

## Interning

A literal is interned once per program by what it denotes: a numeral
by its number, a character by its code, a string by its characters,
so `#\a` and `#\x61` are one entry and every occurrence of `"ab"` is
one entry. The entries a literal stands for enter just before the
top-level form that first mentions it, as if by run-position
statements there, and refer to the prelude's own `Nat`, `Char`,
`String` and their constructors whatever names the program has since
shadowed. They are anonymous and outside the scope: nothing can name,
shadow or rebind them, and an occurrence of the literal resolves to
them by the literal itself.

## What the checker sees

- A numeral is opaque: a `Const` `Nat` with no `is` rule, beside its
  erased `Numeral` proof. `3` is not `(Succ (Succ (Succ (Zero))))`.
  `(numeral-of lit)` yields a literal's proof by its spelling, so two
  spellings equated in a branch refute it; `unary` and `distinct`
  mint the one rule or refutation a `Succ` shape or a disjointness
  needs, through the prelude's `Numeral` lemmas (SUGAR.md 5).
- A character literal is transparent down to its opaque `Nat`: its
  entry carries `is (MkChar (MkU8 n p))`, `n` the entry of its code's
  numeral and `p` the erased proof of its bound, so a character is
  its code to the checker and no separate relation on characters is
  needed.
- A string literal is opaque: a `Const` `String` with no rule.
  `comptime-match` reads its value; a match inside a function takes
  it apart at runtime. A rule exposing its characters would make
  every canonical form that mentions the literal expand to all of
  them.

## Printing

A value of type `Nat`, `Char` or `String` prints as the literal it
reads back from: a numeral in decimal; a character bare where the
reader's word syntax admits it, else `#\space`, `#\newline`, `#\tab`
or `#\xHH`; a string with the four escapes above. Reading a printed
value back yields a literal denoting the same value.

## Left to the implementation

How a `Nat`, `Char` or `String` is held at runtime, whether a
literal's entries are produced by elaborating the statements above or
minted directly to the same effect, and whether the bound in a
character's proof is decided or asserted, every byte being below
`u8-modulus`. Section 41's invariant applies: stripping the extern
implementations must leave every literal meaning the same value.
