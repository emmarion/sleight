# Implementation decisions

Decisions the owner made in chat about how the implementations are
built, which DESIGN.md leaves out because it states the language and
not an implementation. Each was recorded by the session that carried it
out, in ASSUMPTIONS.md, and moved here; the wording is that session's,
not confirmed by the owner, and a paraphrase may say more or less than
the owner did. Each cites the ASSUMPTIONS.md item describing what was
built. An item that goes away leaves its number as a gap.

## The reference, extraction and messages

1. Interpretation is the checked path and extraction is opted into for
   speed: the interpreter raises on a reached absurd, while extracted
   code trusts the checker (ASSUMPTIONS 63).
2. A nested `def-adts`'s phantom constructors leave nothing in the
   post-erasure code, as an erased `def-fns` leaves nothing
   (ASSUMPTIONS 77).
3. Every message carries a file, a line and a column (ASSUMPTIONS 194).
4. A store into a block of a tagged unmarked datatype goes through the
   constructor's own pattern rather than `Obj.set_field`
   (ASSUMPTIONS 162).
5. Proof-indexed array get and set may use unsafe operations
   (ASSUMPTIONS 168).
6. An extern type's extraction goes through templates, and its view
   stays for held values; every hole of a template but a branch body is
   filled with a variable name (ASSUMPTIONS 133).

## The prelude

7. The FFI adder returns an `Add` proof, with a plain adder as a
   `delegate` over it; `double` is derived from it; `trim` is
   transparent; `str-append` gets a relation; and levels are used
   judiciously, with `_` (the section above ASSUMPTIONS 118).
8. `CEq` repeats its index rather than carrying an `Eq`, so matching it
   forces the two sides together the way `Refl` does (ASSUMPTIONS 107).
9. The prelude has no `char-to-nat` or `nat-to-char` (ASSUMPTIONS 107).
10. `Rope` has no length caching, for now (the section above
    ASSUMPTIONS 122).
11. `thunk` is an in-language helper that thunks a value, rather than an
    anonymous function form, at the cost of more verbose call sites
    (the section above ASSUMPTIONS 147).

## The driver and its requests

12. The requests use the general `Pair` rather than a two-field
    `EnvVar`, sorted listings, the `world` for the environment and the
    working directory, a single-level `MkDir`, deletion that reports
    `Unchanged` rather than failing on an absent path, `Change` as the
    answer of the three requests that ask for a state, and the `unix`
    dependency (ASSUMPTIONS 143, 144, 145).

## slc

13. slc ports every check of the reference ("make it not trusting")
    (ASSUMPTIONS 91).
14. slc's canonicalization terminates by a structural argument rather
    than by fuel (ASSUMPTIONS 93), and its invariant is carried as
    erased proofs, rather than as a stamped version with a runtime
    comparison, a fully verified map, or an eager-substitution design
    (ASSUMPTIONS 94).
15. slc's library layer: deciders return evidence, lookups return
    evidence, and lists carry specs; moving the libraries into the
    prelude is set aside (the section above ASSUMPTIONS 121).
16. Lists the elaborator walks together carry a `Lockstep` proof, and
    generated forms are built as `Syn` values (ASSUMPTIONS 124).
17. Post-erasure code is indexed by the erasures of the values it
    produces (ASSUMPTIONS 125).
18. The elaborator never reads a type off a term after the fact, in
    place of a depth-indexed `Term` (ASSUMPTIONS 126).
19. Post-erasure code is indexed by the frames it binds, and the
    interpreter's environment by the same frames; arity-indexed
    application is set aside as common-case special casing
    (ASSUMPTIONS 127).
20. An extern mark is decided into an enum where it is read, and the
    arity check at the mark is made in both compilers (ASSUMPTIONS 128).
21. Every case of the expression elaborator builds its code at the
    expectation (ASSUMPTIONS 129).
22. The compile-time interpreter's values live in a store with `Nat`
    addresses rather than `Bin` ones, weakening is a `coerce`, and the
    heap keeps no list of addresses (the section above ASSUMPTIONS 131).
23. Every use of `Bin` in slc is erased, and the conversion goes through
    `Half` (ASSUMPTIONS 136).
24. slc's compile-time evaluation does not grow the stack, or at least
    interpreting a tail call is a tail call; `tests/comptime_tail.sl`
    decreases an erased `Nat` tied to a binary counter
    (ASSUMPTIONS 150).
