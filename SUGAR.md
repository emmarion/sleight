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
body. `_` in place of the annotation (§11) would reuse it.

## 3. `_` in a call's decrease annotation

`(predates _)` would read the callee's level (`level-of`, §27) and the
level of the body being elaborated into, and build the `Predates` proof
relating them. `(subterm _)` would attempt the `Subterm` proof for the
argument it precedes. Both naive — no search, so both would fail wherever
a proof needs §8's transitivity axioms.

## 4. Worked example: `map` with sugar

The same program as DESIGN.md §33, which is written without any.

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
        (Cons B (f (predates _) hd) $ map A B f (subterm _) tl))))
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
