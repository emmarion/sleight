# Examples worth reading first

An index of the tests that show DESIGN.md's features working together, for a
reader arriving cold. Written by a Claude session, not by the owner: each
entry says what its test does, and the test is the evidence, so a claim here
that the test does not make is a mistake in this file.

- `tests/io_lift.sl` — two `IO` programs at two levels embedded in a program
  at a third, at no runtime cost. An erased factory mints the program's
  level; `delegate` mints a `Coercible` between continuations whose types
  differ in level and result; `coercible-ctor` lifts it through each request
  with the erased level index differing on the two sides; the user's `coerce`
  erases to nothing, and the extracted OCaml holds only the original values.
  `tests/io_lift_runtime.sl` is the same embedding by rewrapping, one closure
  per request. Together they are the fullest exhibit of levels, erasure,
  `delegate` and `coerce` depending on each other.
- `tests/lt_subterm.sl` — `Lt a b` and `Subterm (Nat) a (Nat) b` each derive
  the other, as erased functions, so on `Nat` the subterm order is the strict
  order. Its `loop` returns `False` from `Subterm x x` by a self-call the
  proof licenses, so `Subterm` irreflexivity appears load-bearing for
  consistency in the way ASSUMPTIONS 69 describes for `Predates`; whether that
  deserves a stated invariant is open for the owner. `tests/lt_subterm_bad.sl`
  is the step `le-split` exists for.
- `tests/div.sl` and `tests/div_structural.sl` — division by repeated
  subtraction in two shapes: recursing on the subtraction's result under a
  `Subterm` proof the subtraction returns, and structural recursion on the
  dividend alone. The first is the pattern for well-founded recursion on any
  computed smaller `Nat`.
- `tests/gcd.sl` — Euclid's algorithm; the recursive call is justified by
  `lt-sub` applied to the remainder's bound, so it uses the interderivation.
- `tests/compose_list_dynamic.sl` — folding a list of functions into one
  function, each step minting a level at runtime above the one the recursive
  call returned, with the `Predates` proofs minted beside it. The tower of
  levels is as tall as the list and exists only when the program runs.
  `tests/compose_list.sl` is the defunctionalized form, the list kept as data
  under one interpreter, whose composed closure sits at one fixed level.
- `tests/runtime_level_bad.sl` — the same composition called from a function
  body is refused: a level minted inside the call cannot be proved to predate
  the caller's, so in this test the composed function is callable only from
  run position.
- `tests/stream.sl` — a stream with no coinductive type, its tail a function
  at a level minted after the producer's.
- `tests/gmap.sl` — a map generic over every type with `List`'s constructor
  shape, through first-class `TyCtor`, `ValCtor` and `Matchable` values; the
  shape is fixed by the signature.
- `tests/packed_bound.sl` and `tests/packed_list_predates.sl` — functions at
  different levels in one list, with the levels erased: either each package
  proves its level below a bound, or the consumer takes a proof that the list
  predates its level and `predates-subterm` walks it down to each function.
  `tests/packed_unbound_bad.sl` has neither, and
  `tests/packed_runtime_list_bad.sl` builds the list after the consumer's
  level was minted, where the list-level proof is refused.
- `tests/recursion_through_pointer.sl` — a function receiving itself inside a
  type with a negative occurrence and calling the pointer at its own level
  under a subterm decrease; `tests/ackermann.sl` for the lexicographic order
  across two subterm arguments.
- `tests/nub.sl` — recursion on a computed vector rather than a subterm: the
  filter returns an erased bound on the result's length, the recursion is on
  the erased length index, and `lt-sub` turns the bound into the `Subterm`
  proof, at no runtime cost.
- `tests/type_result_is.sl` and `tests/type_result_cases.sl` — a type
  computed by a call, made usable by an `is` return entry, and a closed
  existential whose erased type is fixed by matching a runtime witness beside
  a value of it. `tests/eq_transport.sl` transports along a user-defined
  equality by matching `Refl`, with no substitution principle.
- `tests/map.sl` — DESIGN.md section 33, level-polymorphic `map` through a
  factory that mints the level and proves the relation inside.
- `tests/coerce.sl` and `tests/delegate_coerce.sl` — section 40, unwrapping a
  list of newtypes by an erased recursive proof and a `coerce`, and a
  `delegate` whose argument and result pass through coercions.
- `tests/char_ops.sl` — the prelude's `char-cmp`, a comparison of `Char`s
  that is `nat-cmp` on their codes. A `Char` is its `U8` and a `U8` its
  `Nat` at runtime, so the arguments coerce down through both newtypes
  (`coercible-wrap` reversed with `coercible-sym`, the two steps chained),
  the call to `nat-cmp` is marked `delegate`, and the `Coercible` carrying
  the result back up to `Cmp (Char) CharLt a b` is built by an erased match
  on the three outcomes, so nothing but the marked call is left to run. The
  test fetches with `coercible-of` the proof the mark minted that `char-cmp`
  and `nat-cmp` are one function, coerces `char-cmp` to the `Nat` signature,
  and runs it both on characters and on numerals.
- `tests/vec_map.sl` and `tests/binder_clash.sl` — dependent motives checked
  under each branch's forced facts, and a branch refuted because a
  constructor's index mentions its own `Fn` binder (ASSUMPTIONS 73).
- `tests/absurd.sl`, `tests/absurd_proof.sl`, `tests/transparent_union.sl` —
  absurd functions and branches, and a union whose other constructor is
  refuted by proof so the type is represented as its one field.
- `tests/else_enum.sl`, `tests/else_phantom.sl`, `tests/absurd_implicit.sl` — an
  `else` dispatching on a tag, one standing only for a phantom constructor
  and so counting as no real branch, and refuted constructors left unlisted.
  `tests/phantom_false_bad.sl` is why a phantom branch still owes its value:
  omitted, it would prove `False`.
- `tests/comptime.sl` and `tests/comptime_transparent.sl` — `comptime-match`
  verifying a `Const` and binding its fields `Const`, proof by reflection.
- `tests/first_class.sl` and `tests/shadow_false_capture.sl` — matching
  through first-class type and value constructors and a `Matchable`, and a
  function keeping the empty `False` it was defined against after the name is
  shadowed by an inhabited one.
- `tests/main_reverse.sl`, `tests/io_echo.sl`, `tests/thunk_list.sl` — the
  three ways a final value is run by the driver, and `tests/tail_values.sl`
  for a checked tail call over multiple returns.
- `tests/numeral_distinct.sl`, `tests/numeral_succ.sl`,
  `tests/numeral_lemmas.sl` — reasoning about literals through the prelude's
  `Numeral` relation rather than about their opaque `Nat`s. `distinct`
  refutes a branch that has equated two literals, at a cost set by their
  spellings' depth rather than their difference; `unary` rewrites a literal
  to successor form, walking only as far as the floor it is given, which is
  what lets one index a `Vec`. The third writes out what both expand to, so
  the sugar can be read against the calls it stands for.
