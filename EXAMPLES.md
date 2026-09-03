# Examples worth reading first

An index of the tests that show DESIGN.md's features working together, for a
reader arriving cold. Written by a Claude session, not by the owner: each
entry says what its test does, and the test is the evidence, so a claim here
that the test does not make is a mistake in this file.

- `tests/io_lift.sl` — two `IO` programs at two levels embedded in a program
  at a third, at no runtime cost. An erased factory births the program's
  level; `delegate` births a `Coercible` between continuations whose types
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
  function, each step birthing a level at runtime above the one the recursive
  call returned, with the `Predates` proofs born beside it. The tower of
  levels is as tall as the list and exists only when the program runs.
  `tests/compose_list.sl` is the defunctionalized form, the list kept as data
  under one interpreter, whose composed closure sits at one fixed level.
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
  factory that births the level and proves the relation inside.
- `tests/coerce.sl` and `tests/delegate_coerce.sl` — section 40, unwrapping a
  list of newtypes by an erased recursive proof and a `coerce`, and a
  `delegate` whose argument and result pass through coercions.
- `tests/vec_map.sl` and `tests/binder_clash.sl` — dependent motives checked
  under each branch's forced facts, and a branch refuted because a
  constructor's index mentions its own `Fn` binder (ASSUMPTIONS 73).
- `tests/absurd.sl`, `tests/absurd_proof.sl`, `tests/transparent_union.sl` —
  absurd functions and branches, and a union whose other constructor is
  refuted by proof so the type is represented as its one field.
- `tests/comptime.sl` and `tests/comptime_transparent.sl` — `comptime-match`
  verifying a `Const` and binding its fields `Const`, proof by reflection.
- `tests/first_class.sl` and `tests/shadow_false_capture.sl` — matching
  through first-class type and value constructors and a `Matchable`, and a
  function keeping the empty `False` it was defined against after the name is
  shadowed by an inhabited one.
- `tests/main_reverse.sl`, `tests/io_echo.sl`, `tests/thunk_list.sl` — the
  three ways a final value is run by the driver, and `tests/tail_values.sl`
  for a checked tail call over multiple returns.
