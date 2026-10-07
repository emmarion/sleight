# Candidate demos

Programs worth writing that nothing in `tests/` writes yet, proposed by a
Claude session after probing the language rather than by the owner. Nothing
here is implemented and nothing here is a design decision: each entry is a
guess about what would typecheck and what it would be worth, and the guesses
may be wrong. Where an entry states what the language *does*, it names the
test that is the evidence; everything else is this session's expectation.
EXAMPLES.md indexes what is built; this file is the list of what is not.

The entries are grouped by what each would exhibit, since the value of a
demo here is mostly in which claim it supports.

## What the tests already establish

The baseline the entries below are measured against:

- An algorithm can reuse the cell a `unique` destructure hands back, in
  constant space and with no allocation: `tests/cell_append.sl` (tail call
  modulo cons), `tests/cell_rev_inplace.sl`, `tests/cell_rotate.sl`,
  `tests/cell_map_retype.sl`.
- Such an algorithm can carry a relation about its result whose indices name
  cells it overwrites, every entry of the relation declared erased:
  `tests/cell_rev_certified.sl`, `tests/cell_rotate_certified.sl`.
- A result is `at` its argument without being `is` it, so a relation proved
  of the argument beforehand does not transfer to the result:
  `tests/cell_at_not_is_bad.sl`, and its converse
  `tests/at_is_independent_bad.sl`.
- Termination evidence is ordinary erased data, derivable and storable:
  `tests/lt_subterm.sl`, `tests/nub.sl`, `tests/packed_bound.sl`,
  `tests/packed_list_predates.sl`.
- Levels can be minted while a program runs:
  `tests/compose_list_dynamic.sl`.
- A datatype may have a negative occurrence, and recursion through it is
  bounded by a `subterm` argument beside it:
  `tests/recursion_through_pointer.sl`.

Two limits this session measured, which several entries below run into:

- A field is a subterm of what it was destructured from; the result of a
  call is not (`tests/subterm_call_result_bad.sl`). So a recursive
  occurrence reached by *calling* a stored function needs an independent
  decreasing argument.
- A cell is tied to the value constructor it was allocated or destructured
  at; only the type constructor's arguments may change
  (`tests/cell_retype_ctor_bad.sl`, `tests/cell_map_retype.sl`).

## 1. Erased proofs over reused memory

On this session's reading this is the line with the least prior art, so the
entries here are ranked highest. Each is a step up in size from
`tests/cell_rotate_certified.sl`, which proves one rotation.

**1a. In-place sorting with a permutation and a sortedness certificate.**
A quicksort or heapsort over the prelude's `Array`, returning the sorted
array `at` its argument beside evidence that it is a permutation of the
input and is ordered. The reason this session would rank the permutation
half above the sortedness half: `array-swap` already returns a `SetNth`
relating the array before and after, so a run of swaps might compose into a
permutation witness out of the calls' own return values, rather than needing
a multiset argument beside them. Whether they compose that way is the thing
to find out; if they do, that is a better story than proving a permutation
lemma. Expected cost: high, and the friction is expected to be the `Nth`
evidence a runtime index needs, of the kind TOOLING-WISHLIST 8, 20 and 28
record, rather than the proof.

**1b. Union-find with path compression.** `find` rewrites parent pointers
while leaving the partition it denotes unchanged, which is the same
separation `tests/cell_at_not_is_bad.sl` pins down, so this session expects
the language's own distinction to be doing the work rather than being
illustrated. `find`'s termination would want an erased rank or depth measure
about the structure *before* compression, which UNIQUE.md U2 permits as an
erased mention of a consumed binder. Expected cost: high. Unknown: whether
the measure can be stated over a structure the same call is mutating, which
is 1d's question in a harder setting.

**1c. In-place red-black or AVL insert.** The scaling question
`tests/cell_rotate_certified.sl` leaves open: one rotation takes a four-line
derivation, and an insert recurses, maintains an invariant and rebalances.
Whether the derivation grows with the operation or stays flat is the
empirical claim worth measuring; this session has no prediction. A cheaper
warm-up with the same shape: **in-place merge of two sorted lists**, reusing
the cells of both, with a `Merged xs ys r` certificate, which would be the
first demo whose relation names two destroyed structures rather than one.

**1d. A termination measure computed over the structure being mutated.**
Every existing demo uses in-place reuse or termination-by-erased-proof, none
uses both in one recursion. A candidate is an in-place sort whose measure is
an inversion count that each swap lowers. This session cannot tell from the
rules whether a measure may refer to a structure mid-mutation; both answers
seem worth having, and a refusal would be a sharper statement of what `at`
and `is` being separate costs than any accepted program would be.

## 2. Datatypes without positivity

**2a. Higher-order abstract syntax.** A `Term` whose abstraction holds a
function from `Term` to `Term` — roughly `(many Lam : (many (Fn L (many
(Term) x) -> (many (Term) y)) body) -> (Term))` — with an evaluator
beside it. DESIGN.md section 10 removes the
positivity requirement, and `tests/recursion_through_pointer.sl` is a
negative occurrence used for real, so this session expects the
*representation* to be accepted. The evaluator is the open part and is
expected to meet `tests/subterm_call_result_bad.sl` head on: substitution
under `Lam` applies the stored function, and the result of that call is no
subterm of anything, so an evaluator would need a separate erased measure —
a size or depth index on `Term` — to recurse on.

This session would try this one first, for cost rather than for rank: it is
small, and either outcome says something. Accepted, it is a short statement
about what removing positivity buys. Refused, it is a precise statement of
what it does not buy, which is at least as useful to write down.

## 3. Levels

**3a. An interpreter tower whose depth is read at runtime.**
`tests/compose_list_dynamic.sl` already mints a level tower as tall as its
input; this would be the same machinery with `mini/`'s interpreter in place
of composition, interpreting itself *n* deep for an *n* the program reads.
What it would exhibit is narrower than "a tower exists": the well-order the
termination argument rests on is built while the program runs, which this
session believes a fixed measure cannot express, though that belief is worth
checking against the sized-types literature before it is claimed.

**3b. Dispatch over a registry assembled at runtime.**
`tests/packed_list_predates.sl` walks one `Predates` about a list down to
each function's level. Scaled up — a scheduler over functions at unknown
erased levels, gathered while running — it would read as termination
evidence being handed about like a capability. Expected cost: low to medium,
since the test already has the hard part.

## 4. Cross-cutting

**4a. A zero-cost abstraction boundary, proved.** `tests/coerce.sl` unwraps
a list of newtypes for nothing. The scaled form is an interface whose
abstract and concrete types are proved identical, so that crossing the
boundary emits no code at all. This session confirmed while writing
`tests/cell_rotate_certified.sl` that a certified and an uncertified
rotation extract to the same body once generated names are normalised, which
is the same kind of evidence and could be presented together.

**4b. Validate once at elaboration, never at runtime.** A reader that
returns a value beside a well-formedness certificate, so that code after it
destructures the certificate rather than re-checking; with
`comptime-match`, the checking happens while the program is elaborated.
`tests/comptime_tail.sl` shows a compile-time loop of real size already
works. Expected cost: medium.

**4c. Connect `mini/` and `self/`.** `mini/` writes the semantics down as
relations and `self/` implements them; proving one pass of the compiler
against the relations, in the language, would be the largest claim available
here. Almost certainly too big as stated, but a thin slice — the erasure
pass over the minimal fragment — might not be. Listed for completeness, not
proposed.

## Order this session would try them in

2a first, being small and informative either way; then 1b, where the
language's own distinction between location and value looks load-bearing
rather than decorative; then 1a, which is the one a reader is most likely to
ask for by name. 1c's warm-up (in-place merge) is the cheapest way to learn
whether 1c is worth starting.

## Obstacles expected to apply to all of them

TOOLING-WISHLIST 14 and 31 both record that the checker was not the
obstacle and that the rounds went to arithmetic, positional arguments and
parens. Every entry above is heavy in indices and erased evidence fields, so
this session expects the cost to land in the same place. That expectation is
itself worth measuring: if it holds across demos of this size, it is a
finding about the design rather than an inconvenience.

## Comparisons worth checking before any of this is called novel

Pointers this session did not verify, listed so that a later session checks
rather than repeats them: Koka's Perceus reuse analysis and FBIP, and Lean
4's reuse, for cell reuse done by a compiler instead of in source; OCaml's
`[@tail_mod_cons]` for `tests/cell_append.sl`'s shape; Agda's sized types and
MiniAgda for erased measures; Dafny, Why3, VST and CFML for verified
in-place sorting and for union-find with path compression; Mezzo, Granule and
Clean for uniqueness; ATS for linear types with proofs. Whether any of them
state a correctness relation over memory the program has overwritten, and at
what cost, is the question that decides how much of section 1 is new.
