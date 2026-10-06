# Surface sugar

DESIGN.md records the core language. This file records sugar: forms that
would elaborate away into constructs DESIGN.md already defines, carrying
no meaning of their own. Everything here is provisional. Examples using
sugar live here; DESIGN.md's examples use none.

## 1. `_` as a `def-fns` level

Writing `_` where a `def-fns` block's level goes (§7, §27) would do two
things: insert a `def-lvl` immediately above the block, minting an
anonymous level, and define the block's functions at it.

## 2. `_` in a match's return annotation

Where a `match` is the result expression of a function body or of a match
branch body (§16), the telescope it must produce is already fixed by that
body. `_` in place of the annotation (§11) would reuse it. With §6 the
telescope a position expects reaches an argument too, so a match there may
write `_` as well, provided the expectation holds no `_` still to infer.

## 3. `_` in a call's decrease annotation, and no annotation at all

`(predates _)` reads the callee's level (`level-of`, §27) and the level
of the body being elaborated into, and builds the `Predates` proof
relating them. `(subterm _)` attempts the `Subterm` proof for the
argument it precedes. Both naive — no search, so both fail wherever a
proof needs §8's transitivity axioms, comes from a parameter or a call,
or is carried in data; such a call writes its proof out, as DESIGN.md
§9 has it.

A call inside a function body may also carry no annotation at all. The
elaborator then supplies one: `(predates _)` when the callee's level and
the current level do not canonicalize equal, otherwise `(subterm _)`
before the first `subterm`-marked argument that does not canonicalize
equal to its counterpart among the enclosing function's `subterm`
arguments (DESIGN.md §3, §9). As far as this note can tell that is the
only position at which `(subterm _)` could succeed — a canonically
equal argument is no strict subterm of its counterpart, and §9 wants
equality at every earlier position — so a bare call should be accepted
exactly when some `_` annotation would be. The proof is built and
checked as before; only its spelling is gone. A same-level call whose
`subterm` arguments all canonicalize equal to their counterparts is an
error. At the top level a bare call is what §24 already has.

## 4. Worked example: `map` with sugar

The same program as DESIGN.md §33, which is written without any, the
calls with no annotation (§3).

```scheme
(def-fns _ $ (many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) ->
              (many (List B) ys))
          mapped))
  (def-fns _ $ (many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) ->
      (many (List B) ys))
    (match many xs _
      ((Nil a) (Nil B))
      ((Cons a hd tl)
        (Cons B (f hd) $ map A B f tl))))
  (values (level-of map) map))
```

```scheme
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))

(let ((erased ML) (many map-nat)) (map-factory (level-of inc)))

(let ((many xs)) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(map-nat (Nat) (Nat) inc xs)
```

## 5. `unary` and `distinct`

Both reason about a numeral through the prelude's `Numeral` relation
rather than about its opaque `Nat`, and both elaborate away into
ordinary calls on prelude lemmas — the elaborator writes down terms it
already knows how to spell, and the checker does the rest. Neither
carries meaning of its own.

`(unary a b)`, with `b` below `a`, would mint one rule,
`a is (Succ ... b)` under as many successors as separate them: the
one-step proofs from `numeral-succ`, each given the `BinSucc` witness
that one spelling steps to the next, folded together by `eq-cong-succ`
and `eq-trans` and carried out by a single `let-match`. `(unary a)` is
the same with `(Zero)` as the floor, reached through `numeral-zero`. The
literals walked over are not mentioned by the rule and stay opaque, so
`(unary 5 3)` says `5 is (Succ (Succ 3))` and nothing about `4`; a
literal a million above its floor still costs one rule. What the rewrite
buys is a literal usable where a `Succ` shape is wanted — peeling a
`Vec`, or, with each literal down to zero given its own `unary`, standing
as a `Vec`'s length.

`(distinct a b)` would yield a `(False)` in a context that has already
equated the two literals, by a vacuous match on `numeral-inj`'s `Eq`
between their spellings: a `Nat` has one bijective base-2 spelling, so
two spellings for one `Nat` conflict through `Bin`'s `Matchable`. Its
cost is the spellings' depth rather than the difference between the
numbers, which is what it has over walking there with `unary`. Outside
such a context it is an error, having nothing to discharge.

## 6. `_` for an erased argument

**Where `_` may stand, today.** As an erased argument of any application
(§4's tier 1, including a Cell invocation, §U9). Also as an argument of
`coercible-wrap`, as the `Sharing` argument of the `coercible-*` forms
(§U7), and in place of any type. Each `_` is a fresh unification
variable, a *meta*. Nowhere else.

**Expectation.** Some positions expect a telescope, each entry a type or
an `is` term, which helps solve the metas inside them. These positions
are a function body (its returns), a match branch (its annotation), a
`let` whose binders all carry a type or `is` clause, and an argument
(its parameter, given the arguments before it). The expectation passes
down through `values`, `tail`, `notail` and `delegate`, and never passes
up.

**Boundaries.** A meta may never reach the fact table. So every form
that records a fact is a *boundary*, and any meta still unsolved at a
boundary is an error. The boundaries are a call's `)`, a `let` binding,
a scrutinee, a match annotation, a body's results, a special form's
operands, run position, and each telescope entry as it is bound. A
constructor application is not a boundary, and *as implemented* neither
is a Cell invocation: its metas may stay open for the surrounding form
to solve. So a `_` in a signature is fine when its own entry solves it.

**Solving.** By unification only, with no search and no computation.
Boundaries settle inside out. Everything within one boundary is solved
together. A boundary nested inside it closes first, using only what is
known at that point. A match's annotation is settled before its
branches, so no meta crosses into a branch.

After that, §3's decrease annotation is inferred.

Open, for the owner (the implementation's choices are the session's):

1. Whether a `_` should be accepted at an entry of a `values` or at the
   scrutinee of a `let-match` — positions with an expectation but no
   application of their own to solve at.
2. Whether §27 should list the sugar (ASSUMPTIONS 105).
3. A bare `_` as a whole annotation or binder type is a hole of type
   `Type`; as the expression of an `is` entry it would be a value of
   unknown type and is not given a meaning.

## 7. Refuting in an absurd body

In the body of an `absurd` function or of an absurd-by-proof branch
(DESIGN.md §12, §37), after its statements, the final expression may
*refute* the facts in force instead of producing a value of an empty
type. Those statements may include a `let-match`, as in
`(absurd (Zero) (let-match erased le (LtS x y l1)) l1)`. A refutation
produces no value and binds nothing. It is one of:

- a `match` annotated `_`. It is erased and refutes when every
  constructor is refuted. Each of its branches is `(absurd C)` or absurd
  by proof, whose body refutes in turn, and it has no `else`.
- `(open-absurd e _)`, which refutes when the open contradicts
  (DESIGN.md §19).
- any other expression `e`, elaborated as an erased value and accepted
  when `(match erased e _)`, with no branches, would refute. So `(False)`
  works as before, and so does `(Lt a (Zero))`. Naive like §6: one match
  deep, no search.

## 8. `let-match` with branches

`(let-match m s (C f...) branch ...)` takes §12's four branch kinds,
written as in a `match`, and `(C f...)` binds outward as before. With
more than one real branch, the pattern included, it elaborates to
`(match m s A ((C f...) rest...) branch ...)`, with `A` the containing
expression's annotation and `rest...` what follows. With one, it stays a
statement and its absurd branches just refute. Coverage replaces
"exactly one survives."

More than one real branch requires a function body, `match` branch
body, or `cell-match` body (UNIQUE.md §U10). A `let` right-hand side,
run position, and absurd bodies (§7) are not allowed. Absurd branches
are allowed anywhere.

## 9. Fetch forms in a type

`(level-of f)`, `(matchable-of T)`, `(delegate-of g)` and
`(numeral-of n)` may be written in a type or an `is` expression, where
each elaborates to the entry it yields as an expression, a variable
reference, which is DESIGN.md §5's first production. It is read where it
is written, against the facts in force there. A `def-fns` block's own
names are in scope in its bodies but not in its signatures, so a
signature cannot name the block's level through one of them. Whether
`coercible-of` joins them is deferred: it mints a fresh proof at each
use rather than fetching one.
