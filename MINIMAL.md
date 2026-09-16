# The minimal language

A cut-down version of DESIGN.md's language, meant to be small enough that
its semantics can be written down as relations, themselves ADTs of the
full language. The cuts are the owner's decisions of one design session;
the wording, and every claim about what a cut takes with it, is that
session's reading and may be mistaken. DESIGN.md is unchanged by this
file: the full language stands, and this is a fragment of it.

## What is removed

1. **Erasure** (sections 6, 12, 20, 23): every multiplicity annotation,
   `erased`/`many` on telescope entries, `let` binders, matches,
   `def-fns` lines and `def-adts` constructors; phantom constructors;
   `union` and the `enum` token, every type now carrying a tag; the
   one-real-branch counting rules; `coerce`, `Coercible`, the
   `coercible-*` forms, `newtype` and `Newtype`; `tail` and `delegate`.
2. **`Matchable`** (sections 17, 19): `open-adt`, `open-absurd`,
   `matchable-of`, `newtype-of` and the opening invariant. A `match`
   instead requires its scrutinee's type to canonicalize to an
   application of a type constructor declared by a `def-adts`;
   constructor disjointness (section 18's failure mode 2) reads that
   declaration. A scrutinee whose type is headed by a variable, a
   first-class `TyCtor` parameter say, cannot be matched.
3. **`else`** branches, **`let-match`** and **`level-of`**, all
   expressible or unneeded without erasure.
4. **`Const`** (sections 4, 15, 34): the `Const`/`Dyn` state, stored
   values, run-position statements running during elaboration, the
   compile-time round trip of KERNEL.md, `comptime-match`,
   state-forwarding `let`, macros, and `Special` as a value. Special
   forms are reserved keywords, no longer renameable. Elaboration is a
   pure function from raw syntax to core terms; evaluation is a
   separate phase after it.
5. **The `_` sugar** of SUGAR.md, the `_` level, the `_` annotation
   and the inferred decrease annotation included: every call in a body
   writes `(predates p)` or `(subterm p)`, as DESIGN.md section 9 has it.
6. **`extern`** and the FFI; there is no prelude, a program declares
   its own `Nat`.
7. **Literals**: numerals, characters, strings.
8. **The `absurd` marks** on functions and branches. Ex falso is a match
   with no branches on a value of a type with no constructors, which the
   current interpreter already accepts (checked by running one);
   structural refutation of an unlisted constructor stays, as does the
   rule that every constructor is listed or refuted.
9. **Nested `def-adts`**: a `def-adts` is confined to the top level.
   `def-fns` and `def-lvl` may still nest inside a body, which the
   factory pattern of section 33 needs.

## What remains

The forms: `let`, `def-lvl`, `def-fns`, `def-adts`; the formers `Fn`,
`TyCtor`, `ValCtor` and `Type`; type- and value-constructor application,
saturated; function calls carrying `(predates p)` or `(subterm p)`;
`match` with its mandatory return annotation; `values`; `prove-subterm`,
`prove-predates` and the three transitivity axioms.

The rules: the restricted type grammar and canonicalize-then-compare
(section 5); the scope table and fact table with branch-forced
unification and its three contradictions (sections 3, 18); levels and
the lexicographic level/subterm decrease (sections 7 to 9); `Type :
Type` with no positivity restriction (section 10); multiple return
values (section 11); per-constructor index redeclaration (section 12);
user-written `is` entries in telescopes and `let` binders (section 14),
kept at the owner's word although their motivating case was erasure;
first-class types, type constructors, value constructors and functions
(section 17), kept likewise; the top level calling freely (section 24);
bottom-up inference (section 25).

## Consequences the session expects, not verified

- The minimal language appears to be the image of the stripping map
  section 23 describes: `Level`, `Predates` and `Subterm` values are
  unit-like at runtime, never inspected, and every type argument is
  ordinary runtime data. If so, section 23's invariant becomes a
  statement about a map from the full language into this one.
- A minimal program should become a full-language program by inserting
  `many` at every binder and `enum` on every `def-adts`, so the
  interpreter in `lib/` can run minimal programs today. Not yet tried.
- A `def-lvl` inside a body still mints a fresh atom at elaboration and
  needs no runtime counter, every level being unit at runtime.

## Decided about the semantics

- Evaluation and typing are relations, not functions.
- The metalanguage is the full language, not the minimal fragment.
- The relations follow an algorithm, the simplest one that can be
  written down, however slow: what will later be proved about them is
  expected to be erased, so readability and simplicity outrank
  everything else.
- The three transitivity axioms stay special forms.

- SPEC-REVIEW 7: a listed branch whose entry unification contradicts is
  an error, as the interpreter has it today.
- A positive `Fails` relation records why a program is refused, beside
  the relation that types it.
- `Term`, the type of types and `is` expressions, and `Val`, the type of
  runtime values, are separate ADTs.

## Where it stands

`mini/` holds the semantics as relations in the full language, with a
function deriving each relation, and `mini/README.md` records the shapes
that session chose and the syntax it gave the minimal language, all open
for the owner to confirm or change. `tests/mini_*.sl` run programs of the
minimal language through them.

## Open

- The surface syntax of the minimal language, chosen by the session that
  wrote `mini/` because the full language's telescopes and binders are
  told apart by their multiplicity tokens, which the minimal language
  lacks.
- The metatheory to state: determinism of elaboration, totality of
  unification, confluence of canonicalization, and every well-typed
  program evaluating, section 10's claim.
