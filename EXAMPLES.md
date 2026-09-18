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
- `tests/comptime_tail.sl` — a loop run at elaboration whose measure is
  erased. A non-erased binary counter drives the dispatch, while the
  `subterm` decrease is taken on an erased `Nat` tied to that counter by the
  prelude's `Numeral`, stepped by `numeral-succ` and cashed in through the
  `Eq` it returns — DESIGN.md section 12's subterm recursion through an
  erased argument — so the iterations build no unary `Nat` and cost the same
  with the extern `Nat` as without it. `tests/extern_tail.sl` is a loop of
  the same shape run by the extracted program rather than at elaboration.
- `tests/first_class.sl` and `tests/shadow_false_capture.sl` — matching
  through first-class type and value constructors and a `Matchable`, opened
  first, and a function keeping the empty `False` it was defined against
  after the name is shadowed by an inhabited one.
- `tests/open_absurd.sl`, `tests/open_adt_unify.sl`, `tests/open_tyctor.sl` —
  opening a `Matchable` (DESIGN.md section 19): a
  contradiction between two constructors held as a fact until the
  `Matchable` listing both is opened, cashed in by `open-absurd` or refuting
  the branch when the open comes first; two `Matchable`s sharing a
  constructor unified by opening both, which equates their type
  constructors; and a first-class type constructor that unifies with `Nat`
  until its `Matchable` is opened and its constructors' signatures tell the
  two apart. `tests/unopened_matchable_bad.sl` and
  `tests/open_adt_branch_bad.sl` show a match finding nothing unopened and an
  open ending with its branch, and `tests/open_adt_let.sl` an open inside a
  `let`'s right-hand side serving the matches after it.
- `tests/main_reverse.sl`, `tests/io_echo.sl`, `tests/thunk_list.sl` — the
  three ways a final value is run by the driver, and `tests/tail_values.sl`
  for a checked tail call over multiple returns.
- `tests/io_step.sl` — iterating without recursing. Every `IO` request but
  `Exit` carries a continuation, so a loop hands its next request to the
  driver instead of calling itself: `Step` performs nothing and loops
  silently, and `WriteOut` loops on output alone. The continuation is a
  closure at the IO level, which comes after the looping function's own,
  so no function in the program can call it and the unbounded iteration
  stays the driver's.
- `tests/numeral_distinct.sl`, `tests/numeral_succ.sl`,
  `tests/numeral_lemmas.sl` — reasoning about literals through the prelude's
  `Numeral` relation rather than about their opaque `Nat`s. `distinct`
  refutes a branch that has equated two literals, at a cost set by their
  spellings' depth rather than their difference; `unary` rewrites a literal
  to successor form, walking only as far as the floor it is given, which is
  what lets one index a `Vec`. The third writes out what both expand to, so
  the sugar can be read against the calls it stands for.
- `tests/bare_call.sl`, `tests/bare_lex.sl` — calls with no decrease
  annotation (SUGAR.md 3): the first has a `Predates` proof and a `Subterm`
  proof inferred beside a written `_`; the second is `tests/ackermann.sl`
  with nothing written, the inferred position being the first `subterm`
  argument that differs from its counterpart. `tests/bare_lex_bad.sl` shows
  there is no search: a first argument that grows is refused although the
  second decreases.
- `tests/wild_ctor.sl`, `tests/wild_call.sl` and `tests/wild_is.sl` — `_`
  for an erased argument (SUGAR.md 6): a constructor's type argument solved
  from the field after it, from the telescope a body returns into through
  `values`, and from a match's annotation; a call's type argument solved
  from a later argument or from the results' expected telescope; an
  `is`-entry's value taken by `_`, and a `_` inside a pinned field solved
  through the value expected. `tests/wild_fn_binder.sl` solves one under a
  `Fn` binder, `tests/wild_erased_many.sl` puts one at a `many` parameter
  in an erased position, `tests/wild_match_ann.sl` writes a match's `_`
  annotation at an argument position, and `tests/wild_let.sl` lets typed
  `let` binders solve the right-hand side. `tests/wild_open.sl` has a
  constructor's `_` solved by the argument after it in the enclosing call,
  and `tests/wild_partial_ann.sl` a match annotation and a let binder type
  with `_`s inside them, `tests/wild_bare_hole.sl` a bare `_` entry,
  `tests/wild_later_arg.sl` a `_` at a `many` parameter of an erased call
  solved by the proof argument after it, `tests/wild_is_alias.sl` an
  `is` return instantiated with an alias-typed argument and fed to a `_`
  solved through an `is` field, with `tests/wild_is_alias_bad.sl` showing
  the canonical type printed for such a value, and `tests/wild_special_bad.sl`
  a special form refusing an open `_`. The refusals: `tests/wild_nested_bad.sl`
  (`(len _ (Nil _))`, the inner `)` first), `tests/wild_ambiguous_bad.sl`,
  `tests/wild_many_bad.sl`, `tests/wild_mismatch_bad.sl`,
  `tests/wild_match_ann_bad.sl` and `tests/wild_type_bad.sl`.
- `tests/longest_palindrome.sl` — a naive search for the longest palindromic
  window of a `List (Nat)`, returning beside the length an erased proof of
  the spec `tests/palindrome_relations.sl` states (the owner's relations;
  the test runs against a copy of the file the owner supplied). Deciders
  return evidence either way, as the prelude's `lt-dec` does: `take-dec`
  a `Take` or a length bound, `pal-dec` a `Palindrome` or a `NotPalindrome`
  by peeling both ends with `unsnoc`, `has-dec` the fused
  `HasPalindromeOfLength` or `NoPalindromeOfLengthF`. The search walks the
  candidate length down from the input's, carrying `NoLargerPalindromeF`
  as its invariant, and erased lemmas bridge the fused relations to the
  spec: `Windows` is total and `Take` functional, a window found is an
  `Exists` over the windows, and a slide finding none is an `All`. Nothing
  but the decisions' tags and the input's length survives erasure.
- `tests/manacher.sl` — the same answer in linear time, with the same proof.
  Manacher's algorithm with lists alone: a zipper for the left end of the
  current palindrome, a suffix for its right end, and a suffix of the
  radius list (`Back`, whose entries carry erased certificates) for the
  mirror centre, each moving monotonically or by the amount just compared.
  The mirror step is an erased lemma (`mirror-agree`) that peels the deepest
  element of two reversed prefixes at once; the certificates are read back
  forwards (`FwdB`) to refute every longer window, and the found-window
  evidence is built by walking the zipper back. `tests/palindrome_bridge.sl`
  holds what the two searches share: a `Take` decider and the bridge from
  the fused relations to the spec. On this session's measurement the
  extracted program handles four hundred thousand elements in well under a
  second; the reading of it as linear is the session's, not verified.
