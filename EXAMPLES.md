# Examples worth reading first

An index of the tests that show [DESIGN.md](DESIGN.md)'s features working together, for a
reader arriving cold. Written by a Claude session, not by the owner: each
entry says what its test does, and the test is the evidence, so a claim here
that the test does not make is a mistake in this file.

- [`tests/io_lift.sl`](tests/io_lift.sl) — two `Program`s at two levels embedded in a program
  at a third, at no runtime cost. An erased factory mints the program's
  level; `delegate` mints a `Delegate`, read as a `Coercible` between
  continuations whose types differ in level and result; `coercible-ctor` lifts
  it through each step with the erased level index differing on the two
  sides; the user's `coerce` erases to nothing, and the extracted OCaml holds
  only the original values.
  [`tests/io_lift_runtime.sl`](tests/io_lift_runtime.sl) is the same embedding by rewrapping, one closure
  per step. Together they are the fullest exhibit of levels, erasure,
  `delegate` and `coerce` depending on each other.
- [`tests/lt_subterm.sl`](tests/lt_subterm.sl) — `Lt a b` and `Subterm (Nat) a (Nat) b` each derive
  the other, as erased functions, so on `Nat` the subterm order is the strict
  order. Its `loop` returns `False` from `Subterm x x` by a self-call the
  proof licenses, so `Subterm` irreflexivity appears load-bearing for
  consistency in the way [ASSUMPTIONS 69](ASSUMPTIONS.md) describes for `Predates`; whether that
  deserves a stated invariant is open for the owner. [`tests/lt_subterm_bad.sl`](tests/lt_subterm_bad.sl)
  is the step `le-split` exists for.
- [`tests/div.sl`](tests/div.sl) and [`tests/div_structural.sl`](tests/div_structural.sl) — division by repeated
  subtraction in two shapes: recursing on the subtraction's result under a
  `Subterm` proof the subtraction returns, and structural recursion on the
  dividend alone. The first is the pattern for well-founded recursion on any
  computed smaller `Nat`.
- [`tests/gcd.sl`](tests/gcd.sl) — Euclid's algorithm; the recursive call is justified by
  `lt-sub` applied to the remainder's bound, so it uses the interderivation.
- [`tests/compose_list_dynamic.sl`](tests/compose_list_dynamic.sl) — folding a list of functions into one
  function, each step minting a level at runtime above the one the recursive
  call returned, with the `Predates` proofs minted beside it. The tower of
  levels is as tall as the list and exists only when the program runs.
  [`tests/compose_list.sl`](tests/compose_list.sl) is the defunctionalized form, the list kept as data
  under one interpreter, whose composed closure sits at one fixed level.
- [`tests/runtime_level_bad.sl`](tests/runtime_level_bad.sl) — the same composition called from a function
  body is refused: a level minted inside the call cannot be proved to predate
  the caller's, so in this test the composed function is callable only from
  run position.
- [`tests/stream.sl`](tests/stream.sl) — a stream with no coinductive type, its tail a function
  at a level minted after the producer's.
- [`tests/gmap.sl`](tests/gmap.sl) — a map generic over every type with `List`'s constructor
  shape, through first-class `TyCtor`, `ValCtor` and `Matchable` values; the
  shape is fixed by the signature.
- [`tests/packed_bound.sl`](tests/packed_bound.sl) and [`tests/packed_list_predates.sl`](tests/packed_list_predates.sl) — functions at
  different levels in one list, with the levels erased: either each package
  proves its level below a bound, or the consumer takes a proof that the list
  predates its level and `predates-subterm` walks it down to each function.
  [`tests/packed_unbound_bad.sl`](tests/packed_unbound_bad.sl) has neither, and
  [`tests/packed_runtime_list_bad.sl`](tests/packed_runtime_list_bad.sl) builds the list after the consumer's
  level was minted, where the list-level proof is refused.
- [`tests/recursion_through_pointer.sl`](tests/recursion_through_pointer.sl) — a function receiving itself inside a
  type with a negative occurrence and calling the pointer at its own level
  under a subterm decrease; [`tests/ackermann.sl`](tests/ackermann.sl) for the lexicographic order
  across two subterm arguments.
- [`tests/nub.sl`](tests/nub.sl) — recursion on a computed vector rather than a subterm: the
  filter returns an erased bound on the result's length, the recursion is on
  the erased length index, and `lt-sub` turns the bound into the `Subterm`
  proof, at no runtime cost.
- [`tests/type_result_is.sl`](tests/type_result_is.sl) and [`tests/type_result_cases.sl`](tests/type_result_cases.sl) — a type
  computed by a call, made usable by an `is` return entry, and a closed
  existential whose erased type is fixed by matching a runtime witness beside
  a value of it. [`tests/eq_transport.sl`](tests/eq_transport.sl) transports along a user-defined
  equality by matching `Refl`, with no substitution principle.
- [`tests/map.sl`](tests/map.sl) — [DESIGN.md](DESIGN.md) section 57, level-polymorphic `map` through a
  factory that mints the level and proves the relation inside.
- [`tests/coerce.sl`](tests/coerce.sl) and [`tests/delegate_coerce.sl`](tests/delegate_coerce.sl) — section 60, unwrapping a
  list of newtypes by an erased recursive proof and a `coerce`, and a
  `delegate` whose argument and result pass through coercions.
- [`tests/char_ops.sl`](tests/char_ops.sl) — the prelude's `char-cmp`, a comparison of `Char`s
  that is `u62-cmp` on their codes. A `Char` is its `U8` and a `U8` its
  `Nat` at runtime, so the arguments coerce down through both newtypes
  (`coercible-wrap` reversed with `coercible-sym`, the two steps chained),
  the call to `u62-cmp` is marked `delegate`, and the `Coercible` carrying
  the result back up to `Cmp (Char) CharLt a b` is built by an erased match
  on the three outcomes, so nothing but the marked call is left to run. The
  test fetches with `delegate-of` the proof the mark minted that `char-cmp`
  and `u62-cmp` are one function, reads the `Coercible` off it with
  `coercible-of`, coerces `char-cmp` to the `Nat` signature, and runs it
  both on characters and on `Nat`s with their bound proofs.
- [`tests/cell_rev_inplace.sl`](tests/cell_rev_inplace.sl), [`tests/cell_rotate.sl`](tests/cell_rotate.sl) and
  [`tests/cell_map_retype.sl`](tests/cell_map_retype.sl) — algorithms that reuse the cells their unique
  destructures hand back ([DESIGN.md](DESIGN.md) sections 23, 37), beside [`tests/cell_append.sl`](tests/cell_append.sl)'s
  tail call modulo cons. The first is pointer reversal, one store per node
  under an `(at)` that skips the head slot; the second rotates a tree by
  reinvoking both the outer node's cell and its left child's; the third maps
  `(ULst (Nat))` to `(ULst (Tag))`, a cell being tied to its value
  constructor but not to the type constructor's arguments, with `Tag` a
  newtype so the elements need no wrapper either.
  [`tests/cell_retype_ctor_bad.sl`](tests/cell_retype_ctor_bad.sl) is the step a cell does not take, a block
  rewritten as a different constructor's of the same non-erased arity.
- [`tests/cell_rev_certified.sl`](tests/cell_rev_certified.sl) and [`tests/cell_rotate_certified.sl`](tests/cell_rotate_certified.sl) — the
  same two algorithms carrying a relation about their result: reversal's
  `RevOnto` and rotation's `FlatOnto`, both in difference-list form, which is
  what lets rotation's derivation be rebuilt from its argument's with no
  lemma about appending. Each relation's indices name cells the algorithm
  overwrites, which an erased mention may do after the binder is consumed
  (section 15), and every entry of both proofs is declared erased (section 14).
  [`tests/cell_at_not_is_bad.sl`](tests/cell_at_not_is_bad.sl) is the step that separates them: the result
  is `at` its argument and not `is` it, so a relation proved of the argument
  beforehand is refused where one about the result is wanted. It is the
  converse of [`tests/at_is_independent_bad.sl`](tests/at_is_independent_bad.sl).
- [`tests/unique_typestate.sl`](tests/unique_typestate.sl) — a handle whose erased index records its
  protocol state and whose operations consume it, so the index fixes the
  order and uniqueness stops a spent handle being reused. Each transition
  reinvokes the handle's own cell, and `do-open`, which changes nothing but
  the index, is a full-at invocation returning `at` its argument.
  [`tests/unique_typestate_bad.sl`](tests/unique_typestate_bad.sl) skips a step; [`tests/unique_double_bad.sl`](tests/unique_double_bad.sl)
  is the other half.
- [`tests/placed_thread.sl`](tests/placed_thread.sl) — a value passed through a function that knows
  only its slot ([DESIGN.md](DESIGN.md) section 66). `go` places its parameter `n` and
  hands the `Placed` value to `bump`, whose signature names only an erased
  `(Slot) s`; `bump` unplaces it, updates it in place through its cell and
  places it again, using `placed-slot` to keep the index `s`; and `go`
  unplaces the result and uses `placed-slot` once more to return it `at n`.
  [`tests/placed_slot_missing_bad.sl`](tests/placed_slot_missing_bad.sl) leaves out that last step.
- [`tests/subterm_call_result_bad.sl`](tests/subterm_call_result_bad.sl) — a field is a subterm of what it was
  destructured from and a call's result is not ([DESIGN.md](DESIGN.md) section 28), so a
  recursive occurrence reached by calling a stored function does not drive
  recursion the way [`tests/recursion_through_pointer.sl`](tests/recursion_through_pointer.sl)'s stored function
  does when the decreasing argument is a field.
- [`tests/vec_map.sl`](tests/vec_map.sl) and [`tests/binder_clash.sl`](tests/binder_clash.sl) — dependent motives checked
  under each branch's forced facts, and a branch refuted because a
  constructor's index mentions its own `Fn` binder ([ASSUMPTIONS 73](ASSUMPTIONS.md)).
- [`tests/absurd.sl`](tests/absurd.sl), [`tests/absurd_proof.sl`](tests/absurd_proof.sl), [`tests/transparent_union.sl`](tests/transparent_union.sl) —
  absurd functions and branches, and a union whose other constructor is
  refuted by proof so the type is represented as its one field.
- [`tests/refute.sl`](tests/refute.sl), [`tests/refute_noprelude.sl`](tests/refute_noprelude.sl) — absurd bodies ending in a
  match annotated `_` whose branches are all absurd, in a value whose type no
  constructor can head, or in `(open-absurd m _)`, with a `let-match` before
  the final value; `tests/refute_*_bad.sl` are what is refused.
- [`tests/else_enum.sl`](tests/else_enum.sl), [`tests/else_phantom.sl`](tests/else_phantom.sl), [`tests/absurd_implicit.sl`](tests/absurd_implicit.sl) — an
  `else` dispatching on a tag, one standing only for a phantom constructor
  and so counting as no real branch, and refuted constructors left unlisted.
  [`tests/phantom_false_bad.sl`](tests/phantom_false_bad.sl) is why a phantom branch still owes its value:
  omitted, it would prove `False`.
- [`tests/comptime.sl`](tests/comptime.sl) and [`tests/comptime_transparent.sl`](tests/comptime_transparent.sl) — `comptime-match`
  verifying a `Settled` and binding its fields `Settled`, proof by reflection.
- [`tests/comptime_tail.sl`](tests/comptime_tail.sl) — a loop run at elaboration whose measure is
  erased. A non-erased binary counter drives the dispatch, while the
  `subterm` decrease is taken on an erased `Nat` tied to that counter by the
  prelude's `Numeral`, stepped by `numeral-succ` and cashed in through the
  `Eq` it returns — [DESIGN.md](DESIGN.md) section 21's subterm recursion through an
  erased argument — so the iterations build no unary `Nat` and cost the same
  with the extern `Nat` as without it. [`tests/extern_tail.sl`](tests/extern_tail.sl) is a loop of
  the same shape run by the extracted program rather than at elaboration.
- [`tests/first_class.sl`](tests/first_class.sl) and [`tests/shadow_false_capture.sl`](tests/shadow_false_capture.sl) — matching
  through first-class type and value constructors and a `Matchable`, opened
  first, and a function keeping the empty `False` it was defined against
  after the name is shadowed by an inhabited one.
- [`tests/open_absurd.sl`](tests/open_absurd.sl), [`tests/open_adt_unify.sl`](tests/open_adt_unify.sl), [`tests/open_tyctor.sl`](tests/open_tyctor.sl) —
  opening a `Matchable` ([DESIGN.md](DESIGN.md) section 8): a
  contradiction between two constructors held as a fact until the
  `Matchable` listing both is opened, cashed in by `open-absurd` or refuting
  the branch when the open comes first; two `Matchable`s sharing a
  constructor unified by opening both, which equates their type
  constructors; and a first-class type constructor that unifies with `Nat`
  until its `Matchable` is opened and its constructors' signatures tell the
  two apart. [`tests/unopened_matchable_bad.sl`](tests/unopened_matchable_bad.sl) and
  [`tests/open_adt_branch_bad.sl`](tests/open_adt_branch_bad.sl) show a match finding nothing unopened and an
  open ending with its branch, and [`tests/open_adt_let.sl`](tests/open_adt_let.sl) an open inside a
  `let`'s right-hand side serving the matches after it.
- [`tests/main_reverse.sl`](tests/main_reverse.sl), [`tests/io_echo.sl`](tests/io_echo.sl), [`tests/thunk_list.sl`](tests/thunk_list.sl) — the
  three ways a final value is run by the driver, and [`tests/tail_values.sl`](tests/tail_values.sl)
  for a checked tail call over multiple returns.
- [`tests/io_step.sl`](tests/io_step.sl) — iterating without recursing. A loop hands its next
  step to the driver as a `Continue` instead of calling itself: one loop's
  continuation performs nothing, and another's writes and nothing else. The
  continuation is a `def-unique` closure at the program's level, which comes
  after the looping function's own, so no function in the program can call
  it and the unbounded iteration stays the driver's; the step it is stored
  in consumes it, so each step wraps a fresh one.
- [`tests/io_unique_state.sl`](tests/io_unique_state.sl) — a continuation owning a unique value across
  steps: a counter captured at unique by each step's continuation, updated
  in place through its cell as lines arrive, and read off at the end.
  [`tests/io_continuation_twice_bad.sl`](tests/io_continuation_twice_bad.sl) and [`tests/io_shared_final_bad.sl`](tests/io_shared_final_bad.sl)
  show a continuation refused twice and a shared `Program` refused as a
  program.
- [`tests/world_twice_bad.sl`](tests/world_twice_bad.sl), [`tests/world_shared_bad.sl`](tests/world_shared_bad.sl),
  [`tests/world_kept_bad.sl`](tests/world_kept_bad.sl), [`tests/world_unboxed_bad.sl`](tests/world_unboxed_bad.sl) — the world
  refused for a second request, once shared, kept by a continuation for a
  later step, and taken out of a box that is not a newtype and so is no
  longer `at` the world it came from. [`tests/world_erased.sl`](tests/world_erased.sl) shows a
  `world-do` in an erased position performing nothing.
- [`tests/prove_literal_lt.sl`](tests/prove_literal_lt.sl), [`tests/numeral_succ.sl`](tests/numeral_succ.sl),
  [`tests/numeral_lemmas.sl`](tests/numeral_lemmas.sl) — reasoning about literals through the prelude's
  `Numeral` relation rather than about their opaque `Nat`s.
  `prove-literal-lt` gives an `Lt` between two numerals, which with
  `lt-asym` refutes a branch that has equated them; `unary` rewrites a literal
  to successor form, walking only as far as the floor it is given, which is
  what lets one index a `Vec`. The third writes out what both expand to, so
  the sugar can be read against the calls it stands for.
- [`tests/bare_call.sl`](tests/bare_call.sl), [`tests/bare_lex.sl`](tests/bare_lex.sl) — calls with no decrease
  annotation ([DESIGN.md](DESIGN.md) section 48): the first has a `Predates` proof and a `Subterm`
  proof inferred beside a written `_`; the second is [`tests/ackermann.sl`](tests/ackermann.sl)
  with nothing written, the inferred position being the first `subterm`
  argument that differs from its counterpart. [`tests/bare_lex_bad.sl`](tests/bare_lex_bad.sl) shows
  there is no search: a first argument that grows is refused although the
  second decreases.
- [`tests/wild_ctor.sl`](tests/wild_ctor.sl), [`tests/wild_call.sl`](tests/wild_call.sl) and [`tests/wild_is.sl`](tests/wild_is.sl) — `_`
  for an erased argument ([DESIGN.md](DESIGN.md) section 50): a constructor's type argument solved
  from the field after it, from the telescope a body returns into through
  `values`, and from a match's annotation; a call's type argument solved
  from a later argument or from the results' expected telescope; an
  `is`-entry's value taken by `_`, and a `_` inside a pinned field solved
  through the value expected. [`tests/wild_fn_binder.sl`](tests/wild_fn_binder.sl) solves one under a
  `Fn` binder, [`tests/wild_erased_many.sl`](tests/wild_erased_many.sl) puts one at a `many` parameter
  in an erased position, [`tests/wild_match_ann.sl`](tests/wild_match_ann.sl) writes a match's `_`
  annotation at an argument position, and [`tests/wild_let.sl`](tests/wild_let.sl) lets typed
  `let` binders solve the right-hand side. [`tests/wild_open.sl`](tests/wild_open.sl) has a
  constructor's `_` solved by the argument after it in the enclosing call,
  and [`tests/wild_partial_ann.sl`](tests/wild_partial_ann.sl) a match annotation and a let binder type
  with `_`s inside them, [`tests/wild_bare_hole.sl`](tests/wild_bare_hole.sl) a bare `_` entry,
  [`tests/wild_later_arg.sl`](tests/wild_later_arg.sl) a `_` at a `many` parameter of an erased call
  solved by the proof argument after it, [`tests/wild_is_alias.sl`](tests/wild_is_alias.sl) an
  `is` return instantiated with an alias-typed argument and fed to a `_`
  solved through an `is` field, with [`tests/wild_is_alias_bad.sl`](tests/wild_is_alias_bad.sl) showing
  the canonical type printed for such a value, and [`tests/wild_special_bad.sl`](tests/wild_special_bad.sl)
  a special form refusing an open `_`. The refusals: [`tests/wild_nested_bad.sl`](tests/wild_nested_bad.sl)
  (`(len _ (Nil _))`, the inner `)` first), [`tests/wild_ambiguous_bad.sl`](tests/wild_ambiguous_bad.sl),
  [`tests/wild_many_bad.sl`](tests/wild_many_bad.sl), [`tests/wild_mismatch_bad.sl`](tests/wild_mismatch_bad.sl),
  [`tests/wild_match_ann_bad.sl`](tests/wild_match_ann_bad.sl) and [`tests/wild_type_bad.sl`](tests/wild_type_bad.sl).
- [`tests/dump_context.sl`](tests/dump_context.sl) — `(dump-context)` in the `Cons` branch of
  [DESIGN.md](DESIGN.md) section 61's `append-into`, after the tail call: the report shows the
  goal `(many (List A) r at cell)`, the scrutinee's forced rule, the cell
  consumed by the write and the fresh one consumed by the call, the live
  written cell, and the at-database's classes. [`tests/dump_context_top.sl`](tests/dump_context_top.sl)
  is the same form as a top-level statement over `Settled` values, a `unary`
  rule and a shared unique; [`tests/dump_context_focus.sl`](tests/dump_context_focus.sl) names what to
  report and has a `_` still open in the goal; [`tests/dump_context_type.sl`](tests/dump_context_type.sl)
  and [`tests/dump_context_stmt.sl`](tests/dump_context_stmt.sl) put it in a type and in an erased body;
  [`tests/dump_context_empty.sl`](tests/dump_context_empty.sl) is the form alone in a file, where the
  prelude's entries are listed; [`tests/dump_context_erased_fns.sl`](tests/dump_context_erased_fns.sl) follows
  a run-position `def-fns` whose erased function and `Delegate` proof are
  listed `Settled`.
- [`tests/macro_read_file.sl`](tests/macro_read_file.sl) — a macro that splices in the text of
  [`tests/macro_read_file_data.sl`](tests/macro_read_file_data.sl) as a string literal. Its path arrives as a
  literal, so as a handle, whose type the macro checks with `settled-eq`
  before reading its value; it reads with `read-file` at its own call's
  position and interns the text. The same test shows the refusals of a path
  outside the directory, of `NoPos` and of a position that names no source.
  [`tests/macro_symbol_eq.sl`](tests/macro_symbol_eq.sl) compares names and gensyms with `symbol-eq`.
- [`tests/tactic_lt_lemma.sl`](tests/tactic_lt_lemma.sl) — a proof tactic written as a macro, `lt-lemma`
  from [`std/tactics.sl`](std/tactics.sl). It takes a lemma's whole signature and reads the `Lt`,
  `Le`, `Add` and `Double` hypotheses and the goal from it as syntax, each side
  as a base term under some number of `Succ`s. Each hypothesis is an edge
  between two bases, or two for an `(Add a b c)`, one from `a` and one from `b`
  to `c`, carrying its proof as an `Lt` between the two sides, a non-strict one
  as an `Lt` to the `Succ` of its upper side; the tactic searches for
  a path between the goal's bases, joins its edges with `lt-le-trans`, moves
  `Succ`s across a proof with `LtS` and with `lt-pred` from [`std/nat.sl`](std/nat.sl), and
  weakens the result to the goal with `lt-succ-left` and `lt-weaken`. It then
  emits the `def-fns` with that proof as its body, which is checked like any
  other definition. The test covers chains, a `Succ` added to or peeled off
  both sides, unevenly too, and a chain whose links differ in their `Succ`s.
  [`tests/tactic_ne_false_lemma.sl`](tests/tactic_ne_false_lemma.sl) covers the other two goals and the other two
  hypotheses: an `(Ne a b)` goal is proved by a chain either way, wrapped in
  `NeLt` or `NeGt`, and a `(False)` goal by a chain from an edge back to its
  own start whose `Succ`s make it an `(Lt x x)`, closed by `lt-irrefl`;
  `(Add a b c)` and `(Double a b)` hypotheses step through `add-le-left`,
  `add-le-right` and `double-le`. [`tests/tactic_false_lemma_bad.sl`](tests/tactic_false_lemma_bad.sl) is a cycle
  of non-strict steps, and [`tests/tactic_ne_lemma_bad.sl`](tests/tactic_ne_lemma_bad.sl) an `Ne` the
  hypotheses allow to fail.
  [`tests/tactic_le_lemma.sl`](tests/tactic_le_lemma.sl) covers `Le`: each way of joining a strict and a
  non-strict step, `(Le a a)` from no hypotheses, a weakened `Lt` and `Le`
  under `Succ`s; [`tests/tactic_le_lemma_bad.sl`](tests/tactic_le_lemma_bad.sl) is two `Le` steps offered for
  an `Lt` goal. It checks the `Lt` and `Succ` heads against the prelude's
  through `resolve` and `settled-eq`, so the `aliased` lemma's `S` passes,
  and it emits the names it uses as handles, so the `hygienic` lemmas, whose
  parameters shadow them, still check. [`tests/tactic_lt_lemma_bad.sl`](tests/tactic_lt_lemma_bad.sl) is a
  goal the hypotheses do not imply; [`tests/tactic_lt_lemma_head_bad.sl`](tests/tactic_lt_lemma_head_bad.sl) is a
  goal whose head is none of the four; [`tests/tactic_lt_lemma_gensym.sl`](tests/tactic_lt_lemma_gensym.sl) has another
  macro write the call with every variable a gensym, which the search
  matches through the prelude's `symbol-eq`.
