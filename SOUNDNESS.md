# `Type : Type` and no positivity: why they appear sound here

A reader who knows Girard's and Curry's paradoxes will expect §10 of
DESIGN.md, `Type : Type` with no positivity requirement, to make this
language unsound. This note argues that it does not. Claude sessions
wrote it. `lean/` checks the argument by machine for a fragment of the
language (part 10); for the rest it is a sketch. Section numbers are
DESIGN.md's.

## In short

The claim is relative: **whatever soundness the rest of the language
has, §10 does not take away.** The language also has mutual recursion,
recursion through function pointers stored in data, and first-class
types. None of these appears to reopen the paradoxes, for four reasons:

1. **Types never compute.** A type contains no call (§9) and the checker
   never evaluates (§29), so a paradox has no way to make checking loop.
2. **Termination does not come from types.** Every call must go down in
   §17's order: the callee's level, then the `subterm`-marked arguments.
   Levels are ordered by when they are minted, and `Subterm` is strict
   subtree on finite values. Neither looks at a type, so neither cares
   whether `Type` contains itself or whether a datatype occurs
   negatively in its own constructors.
3. **A stored function is a leaf.** The result of calling a function
   held in data is never a subterm of that data. Calling the function
   needs the same level or subterm evidence as any other call. A Curry
   knot fails at exactly that call: `tests/paradox_*.sl` compile the
   standard knots, and the checker refuses each at the self-application.
4. **The number of `subterm` parameters is bounded by the program
   text.** Telescopes are syntax, never built at run time, so the
   lexicographic order has a fixed length and is well-founded.

Parts 1 to 7 turn this into an argument. Outside `lean/`'s fragment it
rests on lemmas about the rest of the language that are not proved: that
the facts the checker records hold of the values, that uniqueness and
cells implement immutable values, that the FFI matches its models, and
so on. A stratified, strictly positive version of the language would
need every one of those too. A bug in any of them is a bug, but it is
not a cost of §10.

## 1. What is claimed

The claim has four parts, about any program the checker accepts:

- **(C) Checking terminates.** Elaboration of every form ends, apart from
  a crash of the host (§31).
- **(T) Totality.** In the *full semantics* of part 3 below, in which erased
  code runs too, every function activation returns, apart from a crash.
- **(S) Safety.** No reachable state of the full semantics reads a word
  as a field of a constructor that did not build it, enters a refuted
  branch, or runs the body of an `absurd` function.
- **(E) Erasure.** The run the implementations perform, with erased
  positions stripped, follows a run of the full semantics, so (S)
  carries over to it.

From these, consistency in the sense §10 needs would follow: no reachable
state, erased or not, holds a value of a type whose opened `Matchable`
lists no constructors (§25), so
no `(False)` token can justify a refutation that the run then relies on.

The argument claims nothing about logical consistency in the
Curry-Howard sense for types read as propositions independently of
runs. It is the run-time reading that the language relies on: an erased
proof is never checked again, so what matters is that it would have
evaluated to a value had it run.

## 2. Why the two features usually break a system, and why that seems not to apply here

In a dependently typed language, `Type : Type` (Girard's paradox, in
Hurkens' short form) and a negative occurrence in a datatype (Curry's
paradox: `MkBad : (Bad -> False) -> Bad`) each yield a term of an empty
type that does not terminate. That does damage in two ways:

1. **The checker loops.** Where checking compares types up to evaluation,
   a non-terminating term inside a type makes checking diverge.
2. **A proof of `False` is accepted.** Where termination of recursion is
   derived from the types, from a guard condition, strict positivity or
   a logical relation indexed by the universe hierarchy, the paradox is
   a well-typed term that the termination argument wrongly covers, and
   its type is then trusted.

As far as this session can tell, neither mechanism exists here, for
reasons 1 and 2 of the summary above: type equality is canonicalization
by `is` rules followed by identity (§7, §9), and termination rests on
§17's order, which mentions no type.

A further difference from systems such as Coq: there, for a constructor
like `Lim : (nat -> Ord) -> Ord`, the result `f n` of a stored function
counts as a structural subterm of `Lim f`, and that infinitary subterm
relation is what strict positivity protects. Here `prove-subterm` treats
a type former as opaque (§18) and an `is` term cannot contain a call
(§9), so the result of a stored function is never a subterm of anything.

## 3. The full semantics

The argument works in an eager semantics of the unerased program:

- Every position runs, erased ones included; a `Level`, a proof and a
  type are ordinary values. Each `def-lvl` that runs mints a new level,
  and levels are ordered by minting time, a well-order of type ω.
- Values are finite trees, and are immutable: a `unique` binder, a cell
  and an in-place update are read as an implementation of fresh
  immutable values. That reading is OPEN.md 2's first step and OPEN.md
  3, which this note assumes rather than proves.
- An at-function's call and an at-match run (§39, §40); a `coerce` is
  replaced by the value its proof names.

This is roughly the program OPEN.md 2's second step describes.

## 4. Three invariants

In every reachable state of the full semantics, for the facts in force
at the code being run:

- **(I1) Facts are true.** Every `is` fact and type fact in force holds
  of the values the entries are bound to, reading a term of §9's grammar
  as the tree it builds.
- **(I2) `Subterm` is true.** For every `(Subterm A a B b)` token in
  scope, the value of `a` is a strict subtree of the value of `b`.
- **(I3) `Predates` is true.** For every `(Predates A x L)` token in
  scope, every level occurring in the value of `x`, or `x` itself if it
  is a level, was minted strictly before the level `L` denotes.

**Preservation of (I2) and (I3)** appears to follow form by form:

- `prove-subterm a b`: canonical `a` is a strict subtree of canonical `b`
  (§18), and by (I1) canonical terms denote the values, so the values
  are strict subtrees too.
- `subterm-trans`, `predates-trans`: transitivity.
- `predates-subterm`: a level in a subtree of `x` is a level in `x`.
- `prove-predates x L`: by the *lexical-order lemma* below.
- Any other token, returned by an erased function or taken from a field,
  was produced by a finished evaluation, and by induction on that
  evaluation it came from the forms above.

**Lexical-order lemma.** If `x` is introduced before an entry `L` made
by `def-lvl` (or forwarding from one, §19), then in every run the step
that binds `x` finishes before the step that mints `L`. The reason
offered: in a body, statements run in order; parameters are bound before
the body runs; a nested function's body runs after its definition, so
its own entries come after every `def-lvl` of the enclosing body that
precedes the definition and cannot see any that follow it; and the top
level runs in order. A value bound at that step contains only levels
already minted, so (I3) holds of the new token. The lemma does use that
`L` is a mint: §18 refuses `prove-predates x L` for a parameter `L`,
since a parameter's level may have been minted after anything at all.
`tests/paradox_curry_bad.sl` and `tests/predates_*` exercise this check.

**Preservation of (I1)** is the load-bearing lemma that this note does
*not* prove; `lean/` proves it for its fragment (part 10). It needs the
forcing rules of §7 to be valid for equality of value trees: constructor
and type-constructor application injective, the disjointness of §8 true
of distinct constructors, and the occurs check true of finite trees.
With values as syntax trees these seem plausible and seem not to depend
on §10, because none of them asks what a type means, only how it is
spelled. The parts most in need of checking are the `Matchable`
invariant of §8, the unification of unopened first-class type
constructors (§8), and slots (OPEN.md 3). Also assumed: the FFI agrees
with its models (§42); `comptime-match` reads correct values (§29,
OPEN.md 4), as do `settled-eq`, `resolve` and `settled-value` (§64,
§65); and the axioms `gensym-unique`, `placed-slot` and `placed-eq`
(§65, §66) and the literal facts of §45 are true.

## 5. Totality (T)

Give each activation of a function, of `def-fns` or `def-unique`,
erased ones included, the measure

  μ = (λ, s₁, …, s_k)

where λ is the minting index of the activation's level, s₁ … s_n are the
values of its `subterm`-marked parameters in order, and the positions
from n+1 to k hold ⊤, a value above every tree. k is the largest number
of `subterm`-marked parameters of any function in the program text, which
is finite once macros have expanded (§62).

Order measures lexicographically: λ by minting order, then each sᵢ by
strict subtree with ⊤ on top. Each component is well-founded and there
are k + 1 of them, so the order is.

The bound k is essential. A call may decrease its argument at index i
and pass anything after i, so with no bound on the number of `subterm`
parameters this chain would go down at every step and never end, each
call decreasing a later index than the one before:

  (1), (0, 1), (0, 0, 1), (0, 0, 0, 1), …

k exists because a function's telescope is syntax, written once in the
source or in a macro's output, and the number of its `subterm` marks is
read off that text. Nothing at run time builds a telescope: `Fn` is a
type former (§9, §11), and a type is never computed by a call (§9).
`Type : Type` lets a type be passed around as a value, but every `Fn`
type it can hold was written in the finite program text, so the bound
holds whatever types are passed.

Every call goes down in it:

- **A lower-level call** carries `(predates p)`, `p` a
  `(Predates (Level) l L)` relating the callee's level to the current
  one (§19). By (I3) the callee's λ is smaller.
- **A same-level call** has the callee's level identical to the current
  one after canonicalization, so by (I1) the same instance. The
  `subterm` arguments before index i are identical to the enclosing
  ones, by (I1) equal, and the argument at i carries `(subterm p)` with
  `p` relating it to the enclosing argument at i, so by (I2) it is a
  strict subtree. Positions after i may be anything, which lexicographic
  order allows.

This covers a call through any first-class function value, whatever
type it was stored at, because the measure reads only the callee's
level and arguments. So there is no infinite chain of activations. Code
between calls is finite: there is no loop form, `let` does not recurse
(§3), and every other construct is structural in the source. Each
activation therefore makes finitely many calls, each of which finishes,
by well-founded induction on μ. The top level is not a function and
runs straight through (§20). Macro expansion is bounded (§62), and the
driver's loop over a `Program` (§42) is outside the claim, each step
being a total call.

## 6. Checking terminates (C)

Canonicalization rewrites atoms by rules that the occurs check keeps
acyclic (§7), so unfolding ends; unification is first-order with an
occurs check and no β or η (§7 item 3), so it ends. Run-position forms
run total code by (T). `_` metas are solved by unification alone (§50).
None of this looks at whether `Type` contains itself.

## 7. Safety and erasure (S, E)

(S) is a syntactic progress-and-preservation argument, which `lean/`
carries out for its fragment with no stratification (part 10). The
dependent part is that a refuted branch and the
one-real-branch rule (§21) are only as good as the facts in force,
which is (I1), and that no value has an empty type, which holds of
trees built by constructors.

(E) is where §10 meets §17. The stripped run skips every erased
computation and uses its declared result as if it had produced one. By
(T), each skipped computation would have finished in the full
semantics, with results satisfying (I1) to (I3). So each state the
stripped run reaches corresponds to a reachable state of the full
semantics, where (S) holds. Without (T) this step fails: a
non-terminating erased proof of `False` would be skipped and its claim
used, which is the usual way `Type : Type` turns into unsafety. Here
the paradoxes seem to be refused at the call that would loop, as part 8
below records.

## 8. The paradoxes, compiled

Each of these is refused by both compilers. The messages are the
checker's.

- `tests/paradox_curry_bad.sl`: Curry's paradox over a negative type
  whose stored function carries its level as a field. `omega` cannot call
  the stored function: `l` was not in scope when `omega`'s level was
  minted, so no `Predates` relates them.
- `tests/paradox_knot_bad.sl`: the same paradox through a factory. The
  factory itself is accepted: given a `Bad` from before its fresh level,
  it does build a function that calls the stored one. Tying the knot
  needs a caller that calls the factory's result, whose level was
  minted after the caller's, and that call is refused.
- `tests/paradox_same_level_bad.sl`: a negative type whose stored
  function is at the caller's own level. The self-application is a
  same-level call and decreases no `subterm` argument.
  `tests/recursion_through_pointer.sl` shows that the same shape with a
  decreasing argument is accepted and runs.
- `tests/paradox_univ_subterm_bad.sl`: `(Univ)` is its own type but not
  its own strict subterm, so `Type : Type` gives the subterm order no
  cycle.

The Lean runner refuses the same four (`lean/examples/`). Run with
`--unchecked`, its evaluator stops the three knots at the decrease
check rather than looping. These cover the obvious shapes, not every
possible one.

## 9. What the argument leans on

If any of the following changed, the argument above would need
revisiting:

- a call, or any evaluation, inside a type or in canonicalization (§9,
  §29);
- `prove-predates` accepting an `L` that is not a mint (§18), or a
  `Predates` that can be reflexive, or a `Subterm` that can be non-strict
  (OPEN.md 5 asks whether to state these as invariants; the argument
  uses both);
- `prove-subterm` looking inside a type former, or any form that makes
  the result of a call a subterm;
- recursion by any route other than a call under §19's evidence, such as
  a recursive `let` or a loop form;
- a way to build a telescope at run time, or any other way for the
  number of `subterm` parameters a call can meet to be unbounded
  (part 5);
- a construct that runs at the top level without being total.

## 10. What `lean/` checks

`lean/` defines a full semantics like part 3's for MINIMAL.md's
fragment and the additions `lean/README.md` lists, and proves in Lean 4,
on Lean's three standard axioms:

- (T): `eval` is defined by well-founded recursion on part 5's measure,
  with levels as counter values and value sizes in place of strict
  subtree, and `checked_runs` shows a checked program never fails the
  decrease check.
- (S): `checked_runs`, through `VTy`, which types values by recursion on
  the value, not the type. `no_false` is part 1's consistency.
- (E): `eval_sound`, through the stripped run `RunS` and `Real`.
- (I1) is `Sat`, in `EnvOK`; (I2) and (I3) are how `VTy` reads
  `Subterm` and `Predates`; the lexical-order lemma is `Chrono`. Part
  5's bound k rests on `Tm.isTele`: a telescope is written out, never a
  variable.
- (C) only in part: `checkProg` is total, but the reader, the elaborator
  and `Infer.lean` are outside the proof.

Outside the fragment, so argued above at most: `unique`, cells, `at`,
slots, at-functions and at-matches, macros, and the FFI's
implementations of extern functions (`lean/` runs their models).
