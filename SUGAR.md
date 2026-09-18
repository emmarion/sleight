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
(def-fns _ $ many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) ->
              (many (List B) ys))
          mapped)
  (def-fns _ $ many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) ->
      (many (List B) ys)
    (match many xs _
      ((Nil a) (Nil B))
      ((Cons a hd tl)
        (Cons B (f hd) $ map A B f tl))))
  (values (level-of map) map))
```

```scheme
(def-fns _ $ many inc : (many (Nat) n) -> (many (Nat) m)
  (Succ n))

(let (erased ML) (many map-nat) (map-factory (level-of inc)))

(let (many xs) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

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

Note (owner, via a later session): the `_` implementation is more powerful
than this section says, and the section needs updating from the
implementation itself; until then read it as a lower bound.

The owner's proposal, recorded by the session that implemented it: the
decisions are the owner's, the wording and the reading of the gaps the
session's, and `tests/wild_*.sl` are the evidence for what the
implementation does.

An argument to a type constructor, a value constructor or a function may
be written `_` (type formers perhaps later). Elaboration stays naive and
left to right, and an expression's type is fully settled once the
elaborator leaves it.

- **Expectation.** An expression may be elaborated with an expected type
  and/or an expected `is` (terminology open: holes, wildcards, metas),
  built from the usual type and `is` grammar (DESIGN.md §5) except that,
  in place of a variable, a meta — a unification variable — may stand,
  with no user-facing syntax for it. §2's `_` annotation reuses the
  expectation, and is an error if the expectation still holds a meta.
  Function and match returns set the expectation initially, and so does a
  `let` whose binders all carry a type or an `is` clause (added by the
  owner after the first implementation); a function still spells out its
  whole type.
- **Solving.** Each `_` mints a fresh meta, unified at once with what is
  known and eagerly from then on. A `_` is solved by the time the nearest
  *boundary* around it closes; one still open there is an error, and so
  is a `_` at an argument that is not erased where it stands (in
  actuality, not by the parameter's mark: in an erased context a `_` may
  stand at a parameter the function declared `many`).
- **Boundaries** (the owner's second round): the invariant is that no
  entry's type or `is` rule in the fact table mentions an unsolved meta;
  metas live only in terms in flight. A form whose whole content is §5's
  grammar — a type or value constructor application, a type former — is
  pure and no boundary: its `_`s may stay open past its own `)`. Every
  form that records a fact is one: a function call's `)` for its
  arguments, a `let`'s right-hand side, a `match`'s scrutinee and its
  annotation, a function body's results, the arguments of the special
  forms, and run position. A match's annotation may itself hold `_`s
  (`(((List _) r))`, `((_ r))`, or `_` for all of it) and must fully
  unify with the expected telescope right there, before any branch; a
  `let` binder's type may too, solved by the right-hand side at the
  let's `)`. Whether a meta may be solved inside a match branch and
  escape it is deliberately left out.
- **Then the decrease annotation.** Only after this is §3's `predates` or
  `subterm` proof inferred where none is written.

**Naive by design.** The constraints, spelled out, since they decide what
is refused:

- Arguments are read once, left to right: what a later argument would
  settle is not known while an earlier one is elaborated, and an
  expression's own arguments are never revisited.
- A `_` is solved at the nearest boundary's `)` and not later: no
  constraint is carried past a boundary to be solved by what follows,
  and there is no search or backtracking. Within the boundary, what can
  solve a `_` is the expectation the position hands down and the
  arguments before and after it, in the same application or an
  enclosing pure one.
- The expectation flows downward only, from the enclosing position into
  an expression, never up from an expression into its context, and
  never out of a boundary.
- A `_` is never solved by computation: the unifier compares canonical
  terms and binds metas, nothing more (DESIGN.md §5's grammar has no
  function calls to run anyway).

As implemented (ASSUMPTIONS 115): the expectation is the telescope a body
returns into, a match's annotation, or — the owner's addition — the
binders of a `let` when every one of them carries a type or an `is`
clause; it is handed down through `values`, `tail`, `delegate` and every
argument position, where it is the parameter's signature instantiated with
the arguments before it. An application with a `_` first unifies its
result, over metas for all its parameters, with the expectation; each
written argument is then checked against its parameter and bound to its
meta; at the `)` a mismatch with the expectation is reported before an
unsolved `_` is. So `(Cons _ hd tl)` is solved by `hd`, `(Nil _)` by the
telescope it is returned into, the parameter it is passed at or the typed
binder it is bound to, `(list-length _ xs)` by `xs`, `(Cons _ (Nil _) rest)`
by `rest`, and `(f _ (Nil _) xs)` by `xs`, the inner `Nil` being pure.
Refused, by the constraints above: `(f _ (Nil _))`, nothing in the call
fixing the element type by the call's `)`; `(let (many xs) (Nil _))`, the
untyped binder handing nothing down; `(List _)` in a signature, since a
signature is spelled out in full; and a match annotation with a `_` where
nothing is expected of the match.

Open, for the owner (the implementation's choices are the session's):

1. Whether a `_` should be accepted at an entry of a `values` or at the
   scrutinee of a `let-match` — positions with an expectation but no
   application of their own to solve at.
2. Whether §27 should list the sugar (ASSUMPTIONS 105).
3. A bare `_` as a whole annotation or binder type is a hole of type
   `Type`; as the expression of an `is` entry it would be a value of
   unknown type and is not given a meaning.
