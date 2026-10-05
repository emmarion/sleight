# Notable design choices

A list, compiled by a Claude session at the owner's request, of design
choices in this language that might be worth attention: as possibly novel,
as a combination that may not exist elsewhere, as a teaching example, or
just as an unusual call. Nothing here is a design decision: DESIGN.md,
UNIQUE.md, SUGAR.md and LITERALS.md are the record, and every entry below
is this session's paraphrase of them, which may be wrong. The novelty
judgments are guesses made without a literature search; the "compare"
pointers name prior art the session believes is nearby and has not
checked. DEMOS.md's last section lists further comparisons to make before
anything is called new.

## Core semantics and the type system

- **Termination by explicit levels, not by a measure inferred from
  structure** (§§7–9). Every function sits at a `Level`, minted by
  `def-lvl`; a call either goes to a strictly lower level, carrying a
  `Predates` proof, or stays at the same level, carrying exactly one
  `Subterm` proof on a marked argument, lexicographically. Possibly
  unusual in that the termination order is a first-class, user-minted
  object rather than something the checker reconstructs. Compare: sized
  types (Agda, MiniAgda), Coq's guardedness check, ACL2-style measures.
- **Levels are minted in program order, and "earlier" is the well-order**
  (§8). The mental model is a global counter bumped at each `def-lvl`;
  immutability and acyclicity make "minted before" well-defined. A level
  can be minted inside a function body at runtime, so the tower of levels
  can be as tall as an input (`tests/compose_list_dynamic.sl`). The
  session suspects a fixed measure could not express that tower; not
  checked against the sized-types literature.
- **Termination evidence as ordinary erased data** (§§8, 17). `Predates`
  and `Subterm` proofs are values: stored in fields, returned from
  functions, passed through lists (`tests/packed_list_predates.sl`), and
  combined by three transitivity axioms. Termination evidence handled
  something like a capability.
- **Higher-order functions via level factories** (§33). Because a callee
  must predate the caller's level, a `map` taking a function argument is
  produced by a factory that mints `map`'s level above the argument's.
  Level polymorphism falls out of multiple dependent returns rather than a
  dedicated quantifier. Possibly a good pedagogical example of the cost
  and shape of explicit levels.
- **The top level calls freely** (§24). Outside any function body, calls
  need no termination proofs, on the owner's argument that no leveled
  function can call into the top level. Recorded in DESIGN.md as an
  unverified claim.
- **`Type : Type` and no strict positivity, with soundness claimed to rest
  elsewhere** (§10). The owner's stated target is that termination comes
  entirely from the level/subterm order and that types cannot compute
  (§5), so the usual Girard-style and negative-occurrence paradoxes are
  meant to be blocked by other means. Explicitly an unverified claim; if
  it held, it would probably be the most publishable item here. A negative
  occurrence is used for real in `tests/recursion_through_pointer.sl`.
- **Restricted dependent types: no function calls in types** (§5). Types
  and `is` expressions are built only from variables, constructor
  applications and type formers, so type checking is "canonicalize, then
  compare for identity". Dependency without type-level computation;
  compare: indexed types in Dependent ML / ATS, GADTs, Liquid-style
  refinements.
- **Axiom K assumed** (§5), relevant to the dependent matching below.
- **The scope table is the AST** (§3). Every constructor application,
  anywhere, is itself an (often anonymous) scope entry with an `is` rule,
  so the fact table's reference graph is the whole term structure for the
  restricted grammar, and the rewrite engine canonicalizes through
  applications and named variables uniformly.
- **Types live in a scope-relative fact table, not on entries** (§§3, 18).
  An entry's type and `is` rule can be refined inside a match branch and
  revert after it; types are treated as being as hypothesis-sensitive as
  rewrite rules.
- **Match as forced unification** (§18). Entering a branch is licensed to
  *add* `is` facts wherever not already provably impossible, justified by
  the branch being gated by a real discriminant check. Exactly three ways
  to contradict (occurs check, constructor clash via an opened
  `Matchable`, and a variable equated with a telescope binder). Every
  fact ends with the scope that minted it.
- **`is` as an alternative to a type annotation** (§14), letting a binder
  be declared *equal* to an expression rather than of a type, including a
  `many` binder `is` an `erased` one — the language's mechanism for
  reifying an erased witness into a runtime value.
- **Value-constructor fields pinned by `is`** (§30): a stored field that
  is definitionally a compound expression of the indices, so it serves as
  runtime data and in types at once.
- **Per-constructor index redeclaration** (§12): an ADT's indices are not
  in scope across constructors; each constructor redeclares what it
  needs, GADT-style even for uniform parameters like `List`'s.
- **Multiple dependent return values without a sigma type** (§11). A
  function returns a telescope (later returns may depend on earlier
  ones), but there is no sigma former: several values are never one
  value, cannot nest, and are only eliminated by `let`. Expressions have
  a *size*, checked in exactly three places (§16).
- **Three distinct type formers** (§29): `Fn`, `TyCtor` and `ValCtor`,
  separated because their telescopes differ grammatically (levels,
  multiplicities, `subterm` marks, multi-return), not only semantically.
- **No currying** anywhere (§7), and applying a held, unapplied
  constructor is ordinary application.
- **Mandatory match motives as plain return telescopes** (§11), justified
  by the belief that the generalization cannot reliably be inferred from
  dependent branches.
- **Four match-branch kinds** (§12): present, absurd (automatic, `(absurd
  C)`), absurd by proof (produce a value of an empty type), and `else`,
  which is an error if it stands for no constructor.
- **`let-match`: a statement that destructures outward** (§16) when
  structural refutation leaves exactly one constructor possible, each
  candidate checked independently so hypothetical facts cannot leak
  between them.
- **Absurd functions compile to no code** (§37): a function marked
  `absurd` returns a value of an empty type instead of its declared
  result, and its pointer "may be null, or anything at all".
- **`open-absurd`** (§19): cashing in a contradiction that lives in the
  fact table (two constructors of one `Matchable` equated) rather than in
  a value.
- **Bottom-up inference, with explicit types only at definitions,
  function signatures and match annotations** (§25); `_` sugar solved by
  deliberately naive, left-to-right, boundary-delimited unification
  (SUGAR.md 6), with the naivety listed as constraints rather than left
  implicit.

## Erasure

- **Erasure on the binder, Idris 2 / QTT style, always written** (§§6,
  20). No default multiplicity anywhere; every binder declares `erased` or
  `many`, and an expression's erasure is fixed by its position. "Nothing
  is derived from usage."
- **Self-annotating ASCII keywords `erased`/`many`** (§§6, 28) instead of
  `0`/`ω`.
- **Enum vs union: erased discriminants** (§12). A union's tag is erased,
  so it has no runtime tag and can be matched non-erasedly only when at
  most one branch is "real"; the others must be refuted, absurd, or
  phantom. A possibly distinctive way of expressing "the type system
  already knows which constructor this is".
- **Phantom constructors** (§§12, 20): a constructor itself declared
  `erased`, which can never head a non-erased value; its branch under a
  `many` scrutinee is checked fully erased. The note on why the branch
  must still produce its declared values (`tests/phantom_false_bad.sl`) is
  a small soundness lesson in itself.
- **Erasure is conservative, stated as an invariant** (§23, UNIQUE §U14):
  strip every erasure mark and the program should compile and run
  identically. With uniqueness this becomes two ordered tiers (unique→many,
  then erased→many), with collapsed multiplicities kept as inert
  designators so every refutation survives. Intended, not verified.
- **Erasure is decided before code runs** (§20, §34), which is what makes
  the compile-time round trip well-ordered: no erasure demand ever flows
  backwards into code already checked, stripped and run.
- **Erased functions as proof producers** (§§20, 38): recursion over
  containers to build `Coercible` proofs is ordinary code, checked for
  termination, never run.

## Zero-cost coercion and representation

- **`coerce` with a heterogeneous, value-level `Coercible` proof** (§38).
  Coercion relates two *values*, not just two types, and proofs are built
  by `refl`/`sym`/`trans`, by wrapping into a declared newtype, and
  congruence through a constructor (`coercible-ctor`), whose type indices
  may differ between the sides. Compare: Haskell's `Coercible` and roles;
  this one appears to be more fine-grained and proof-carrying.
- **A mandatory, specified uniform representation** (§38): one word per
  value; tags only on enums with more than one non-phantom constructor;
  newtypes guaranteed to be their field. Representation as part of the
  language contract rather than an implementation choice, because
  coercion soundness depends on it.
- **Union newtypes** (§38, UNIQUE §U13): a union in which several
  constructors may each wrap one field, so `MaybeUninit` is one word
  either way, and reading `Init` out is a match whose `Uninit` branch must
  be refuted — `assume_init` "with evidence in place of `unsafe`".
- **`delegate` and the `Delegate` proof** (§§9, 38). A function whose
  post-erasure body is nothing but a pass-through call to an earlier
  function gets a proof that its pointer *is* the callee's, which can be
  turned into a `Coercible` between the two functions.
- **The worked `List (Meters)` → `List (Nat)` unwrap** (§40) as a
  candidate teaching example of a zero-cost, proved, container-level
  coercion.

## Tail calls and call marks

- **`tail` as a checked claim, not an optimization hint** (§9): a hard
  error if the compiler cannot honor it.
- **`notail`: a checked claim that a call is *not* a tail call** (§9),
  with the same hard error. The session has not seen this elsewhere;
  together with the warning on every unmarked same-level call
  (README, "same-level call ... is unmarked; mark it `notail`"), it makes
  every recursion that can grow the stack visible in the source.
- **Tail-ness judged on the post-erasure AST** (§§9, 23, 38): erased work,
  coercions, renaming `let`s and repackaging in the same order do not
  break a tail call, and under uniqueness `at` returns are dropped too, so
  a call returning only `at` results is a tail call from a function
  returning none (§U8).
- **Marks are errors in erased positions**, and ignored by the
  conservativity invariant.

## Kernel-style dynamism with static types

- **Special forms and macros are first-class values** (§§4, 9). Invoking
  something *as* a special form or macro requires its head to be
  constant-known and non-erased; holding one is ordinary data. The stated
  aim is Kernel (John Shutt's Lisp) dynamism while keeping clean static
  compilation. Possibly the most unusual framing in the design.
- **Two-tier head dispatch** (§4): type-driven application first (needing
  no constantness), then the `Const` `Special`/`Macro` tier.
- **One namespace in which everything, special forms included, can be
  renamed or shadowed** (§9), with a warning that names the built-in
  hidden (README).
- **`Special` is an ordinary ADT** (§9); the keyword registry is data.
- **`Const`/`Dyn` and state-forwarding `let`** (§§3, 9, 34): a `let` binder
  takes the entire state of its right-hand side's entry, which is how a
  renamed special form reaches into a function body.
- **Run-position statements run during elaboration** (§§16, 34): any
  statement outside a function body is elaborated, stripped, run, and its
  binders minted `Const`. Compile time and run time interleave statement
  by statement, a "dialogue" between kernel and interpreter (KERNEL.md).
- **"The checker never evaluates"** (§34): the checker computes only what
  the source spells out; branch selection on a value counts as evaluation
  and is handed to the interpreter. A crisp line between checking and
  evaluating that may be worth stating on its own.
- **`comptime-match`: proof by reflection as a statement** (§15): assert a
  `Const`'s constructor, have the compiler check it against the stored
  value, and get the fields (erased proofs included) as facts. The
  session's reading is that it plays the role of Coq-style proof by
  reflection; the correspondence is unverified.
- **Compile errors as a diagnostics channel** (§15): a failing
  `comptime-match` prints the actual value, so a wrapper enum's failure
  payload becomes the compile error with no dedicated mechanism.
- **Interpreter trust as a named soundness obligation** (KERNEL.md):
  because erased fields are stripped before the interpreter runs, a lying
  interpreter could forge an erased proof undetectably; recorded as a v2
  obligation (a small reference evaluator in the kernel).
- **Macro hygiene via entry references** (§35, v2 sketch): `Raw`
  variables as either names or scope-entry identities, in the tradition
  of syntactic closures as the design notes believe.
- **`hoist`** (§36, v2 sketch): running code "before" a level was minted,
  turning the factory pattern inline.

## First-class datatypes

- **`Matchable`: constructor disjointness as first-class data** (§§17,
  19). A type's ordered constructor list, tag and phantom markers are a
  value minted only by `def-adts`; nothing uses it until it is *opened*.
  This is what lets one match on a value whose type is described only by
  first-class type and value constructors.
- **Opening as an explicit act, with an invariant** (§19): at most one
  opened `Matchable` names a given constructor; two that would name one
  thing are unified or contradict, never ambiguous.
- **Types, type constructors, value constructors, `Matchable`s and proofs
  are all first class** (§17).

## Uniqueness, locations and in-place update (UNIQUE.md)

- **Uniqueness on the binder, not the type** (§U1): there is no unique
  type, only a third multiplicity `unique`, so it composes with erasure
  in one system.
- **Path-wise, order-free use checking** (§U2): on each path a `unique`
  binder has exactly one unique use or only degraded/erased ones; branches
  join by a max over unused < many < unique.
- **Four kinds of mention** (§U2a), including a *direct variable
  reference* that is not a use and may name an already-consumed binder,
  and the rule that every argument behaves as if bound to a fresh
  variable first.
- **Explicit degradation with `share`** (§U3), and erased mentions of
  consumed values allowed anywhere, so proofs may talk about destroyed
  data.
- **`def-unique` and `UniqueFn`** (§U6): closures that capture unique
  values, consumed at definition, callable once.
- **The at-database: locations separate from values** (§U8). Beside the
  fact table, a partition of entries by memory location; `at v` on a
  return promises the result occupies `v`'s word. Two equal values are
  `is`-equal but two blocks; a value can be `at` its argument without
  being `is` it (`tests/cell_at_not_is_bad.sl`). The session thinks this
  value/location split may be one of the more distinctive pieces.
- **Cells and placement in source** (§§U9–U10): a `unique` destructure
  hands back the constructor's cell; `cell-write` stores, and invoking a
  cell is a constructor application at that address, with `(at)` /
  full-`at` marks asserting stores can be skipped. Reuse is written and
  checked in source rather than found by a compiler pass. Compare: Koka's
  Perceus/FBIP, Lean 4's reuse, which do this automatically.
- **Tail call modulo cons written by hand and checked** (§U11):
  destination-passing `append` in constant stack, with `tail` still
  checked. Compare: OCaml's `[@tail_mod_cons]`.
- **`Slot` types that track what a cell holds by location** (§U10), with
  `SlotVacant` as `SlotHolds null`.
- **`Coercible` with sharing sides** (§U7), so a composed coercion cannot
  smuggle a shared value into a unique wrapper.
- **Proof-indexed, length-indexed arrays with extern primitives and
  source models** (§U13): `array-swap` returns an erased `ASet` relation
  between old and new array, which is meant to let in-place algorithms
  carry correctness relations over memory they overwrite
  (`tests/cell_rev_certified.sl`, `tests/cell_rotate_certified.sl`).
  DEMOS.md ranks this line as the one with the least prior art, on that
  session's reading.
- **`slot-eq` as a hint that may always answer "different"** (§U15,
  proposed): evidence only in the equal case, so a compiler that never
  compares stays sound.

## FFI, numbers and literals

- **Externs are models** (§41): every `extern` type or function has a
  source definition, and stripping all extern implementations must leave
  the program's values unchanged. The interpreter checks this on its own
  test suite (`--no-extern`).
- **`Nat` is Peano in the source, arbitrary precision in practice** (§41).
- **Bounded words as newtypes with erased bound proofs** (§41): `U8` and
  `U62` carry `Lt n modulus` proofs; `U62` arithmetic takes proofs that
  operands and results are in range, so the FFI can use a single machine
  operation with no overflow check. Moduli are proved to be powers of two
  by construction.
- **Literals are sugar over the prelude, interned and opaque** (LITERALS.md):
  a numeral is an opaque `Const` `Nat` beside an erased proof relating it
  to a bijective base-2 spelling, so `3` is *not* definitionally
  `(Succ (Succ (Succ (Zero))))`; `unary` and `distinct` mint the one rule
  or refutation needed, costing the spelling's depth rather than the
  number's size (SUGAR.md 5).
- **Printing round-trips through literals** (LITERALS.md).

## Syntax and surface

- **`$` as a paren-saving reader token** (§2), Haskell's `$` moved into
  the s-expression reader: it opens a form that closes at its enclosing
  form's `)`.
- **Type-before-name telescope entries** (§30): `(many (Nat) n)` so that
  source order tracks dependency order down to a single entry.
- **Explicit decrease annotations at call sites** (§§9, 32): `(subterm p)`
  sits immediately before the decreasing argument, identifying it by
  position, so nothing can shadow it; `(predates p)` follows the callee.
  Inferred when omitted (SUGAR.md 3).
- **`_` reserved**: `_` mints anonymous binders, and no other name may
  start with `_` (§U16), which leaves the `_`-prefixed spellings free for
  compiler messages.

## Tooling, aimed partly at LLM authors

DESIGN.md names "support LLMs writing code in the language" as a goal.

- **Indentation as a checked claim about paren nesting** (README,
  `lib/indent.ml`): run before parsing, so a file with a missing `)` still
  gets warnings that locate it.
- **Canonical term printing in errors** (README): atoms shown by the
  newest name still denoting them, else a fetch form, else a stable `_N`
  with a note saying where it was minted; shadowed built-ins shown as
  `_Fn` etc.
- **`(dump-context)`** stops elaboration and reports the goal, level,
  scope, facts and at-database.
- **`;! warn NAME MESSAGE`** pragmas that attach a warning to every
  non-erased use of a constructor, with checked suppress/restore regions.
- **Warnings that point at the fix**: unmarked same-level calls name the
  mark to add; a non-erased all-absurd `match` suggests an `absurd` mark.
- **Sandboxing flags** (`--confine-dir`, `--confine-output-bytes`,
  `--no-env`), embedded into extracted programs, and narrowable from
  inside the program (README).
- **An agent harness** (`agent/`) for running LLM sessions on tasks in the
  language.

## Implementation artefacts

- **Self-hosting** (`self/`): a compiler from the language to OCaml,
  written in the language, porting every check of the reference
  elaborator, with a fixed-point bootstrap.
- **Extraction that embeds compile-time values** (README): everything
  computed at elaboration, closures included and sharing kept, is
  emitted as data rather than recomputed.
- **The minimal language and its semantics as relations** (MINIMAL.md,
  `mini/`): a fragment whose elaboration, unification, canonicalization
  and evaluation are written as ADTs in the full language, with a
  positive `Fails` relation for refusals. MINIMAL.md expects the fragment
  to be the image of §23's stripping map; unverified.
- **Certified Manacher's algorithm** (`pal/`): longest palindrome with an
  erased `LongestPalindrome` correctness proof, also extracted to a fast
  standalone binary — perhaps a reasonable showcase that proofs cost
  nothing at runtime.

## Combinations that may be the real story

The session's guess at what is most likely to be new is not any single
item but some of these pairings:

- termination by explicit, first-class, runtime-mintable levels, together
  with `Type : Type` and no positivity check;
- QTT-style erasure, uniqueness and a value/location split in one
  binder-level multiplicity system, with in-place algorithms carrying
  erased correctness relations over overwritten memory;
- Kernel-style first-class special forms in a dependently typed,
  statically compiled, total language, with compile time interleaved
  statement by statement;
- every compiler optimization the programmer relies on (tail calls,
  reuse, coercion, delegation) written as a claim in the source that the
  checker must confirm, rather than performed silently.
