# Classical principles and levels

This directory was written by Claude sessions at the owner's request. It
holds experiments, not decisions: nothing here is part of the language,
and no principle here is proposed as an axiom. The checker shows only
what the files say. A file in `fail/` shows that one attack stops where
it says, not that the principle it attacks is consistent. Every other
claim in this file is the sessions' reading and may be wrong.

## Checking

```sh
classical/check.sh
```

This prints `classical: PASS` when every file in `pass/` checks and every
file in `fail/` stops with the error that `fail/expected.txt` lists for
it. Each file is checked after [`defs.sl`](defs.sl), which defines `Or`,
`IsProp`, `Ex`, `Even`, and `Odd`.

## Notation

`¬_N A` is `(Fn N (erased A a) -> (erased (False) f))`. Each principle is
an erased hypothesis at a level `K`, and each instance of it is given
*certificates*:

- an `IsProp` proof at level `M`;
- a decider at level `D`, whose refutations are at level `E`;
- an at-most-one proof at level `A`;
- a double-negation proof at level `O`.

Its conclusion contains negations at levels `N` and `W`. Every
refutation here returns a function at a fresh level whose result is
`(False)`, as [`tests/anticlassical.sl`](../tests/anticlassical.sl)
does. In every one, the attacker picks the levels.

Excluded middle for propositions takes `M`, `N`, a proof that `M`
predates `N`, `P`, and `(IsProp M P)`, and returns
`(Or P (Fn N (erased P p) -> (erased (False) f)))`. The other principles
are stated in the files that attack them.

## Results

| Principle | Refuted when | No refutation found when |
|---|---|---|
| Excluded middle, propositions | `M` above `N` | `M` at or below `N` |
| LPO | `E` above `N`; or `D` above `K` | `E` below `N` and `D` below `K`; or `E` = `N` |
| WLPO | `W` below `N` | `N` below `W`, even with `D` above `K`; or `W` = `N` |
| LLPO | `A` and `E` above `N`; or `A` above `N` and `D` above `K` | `A` below `N` |
| Markov's principle | `E` and `O` above `N`; or `O` above `K`, at any other levels; or `D` above `K` and `O` above `N` | `E` below `N` with `D` and `O` below `K`; or `O` = `N` |
| Weak excluded middle, all types, no decider | `W` below `N` | `N` below `W`; or `W` = `N` |

Excluded middle for propositions is also refuted with `M` below `N`
when a hypothesis that any two `¬_N X` are equal is added
([`prop-lem-negations-props.sl`](pass/prop-lem-negations-props.sl)).
That hypothesis is a fragment of function extensionality.

## How the refutations work

Every refutation found uses one of three constructions.

1. **Packing.** A datatype with no positivity restriction stores a
   level-`N` refutation of itself, as `Bad` does in
   `tests/anticlassical.sl`. A certificate above `N` can call what is
   stored, so it can refute the datatype, and the principle's level-`N`
   negation can be packed back into it.
2. **Self-passing.** A certificate at a level above `K` may call the
   hypothesis and pass itself as the argument. A function may be named
   as a value in its own body; passing it is not a call.
3. **A low double negation.** For any `A` and `W` below `N`,
   `¬_W ¬_N A` is refutable in the base language
   ([`low-double-negation.sl`](pass/low-double-negation.sl)): a function
   `n` at level `N` whose body is `(k n)` refutes `A`, and `(k n)` is
   then `(False)`.

## Consequences that check

- **Lowering.** With excluded middle for propositions, a refutation of
  a proposition at any level gives one at every level above `M`
  ([`prop-lem-lowers-negations.sl`](pass/prop-lem-lowers-negations.sl)).
- **Deciding equations.** It decides `(Eq (Nat) u v)` for any `u` and
  `v` ([`prop-lem-decides-eq.sl`](pass/prop-lem-decides-eq.sl)), and it
  gives an erased `Bool` oracle with a proof relating its answer to the
  proposition ([`prop-lem-bool-oracle.sl`](pass/prop-lem-bool-oracle.sl)).
- Without any hypothesis, two opened `Matchable`s that name one type
  force the functions captured in their constructors' types to be equal
  ([`matchable-fn-eq.sl`](pass/matchable-fn-eq.sl)). A function defined
  at a parameter level can call a function at a lower level
  ([`lift-to-param-level.sl`](pass/lift-to-param-level.sl)).

## Why no refutation was found where none was

This is an informal reading, not a proof.

- **Excluded middle for propositions, `M` at or below `N`.** A
  refutation seems to need a proposition `P`, a map from `¬_N P` to `P`,
  and a map from `P` to `(False)`.
  - A level-`N` negation cannot be called below `N`, so the first map
    has to store it in the value it builds.
  - Showing that `P` is a proposition at level `M` then means equating
    two level-`N` functions at a level that cannot call them.
  - The ways found to equate functions all pin a function to a term
    that exists before `P` is defined: forcing through indices, Axiom K,
    `placed-eq`, and `Matchable` unification. A fresh negation is not
    such a term.
  - A refutation at `M` gives a negation at `N` without the hypothesis
    ([`lift-to-param-level.sl`](pass/lift-to-param-level.sl)).
  - Inside an `IsProp` proof, the hypothesis helps only where its
    negative answer can be refuted, and refuting it needs the fact being
    decided (the `prop-lem-*` files in `fail/`).
- **The omniscience principles.** Below `N`, a refutation or
  at-most-one proof can take a value of `Q` apart only structurally. It
  cannot call the level-`N` functions packing would store in it.
- **Weak excluded middle and WLPO, `N` below `W`.** Refuting a second
  disjunct `k` at level `W` needs a level-`N` refutation to pass to
  `k`. Building that refutation from `k` would need a call to `k` from
  level `N`, which is below `W`.

## Observations about the checker

These are for the owner to judge. None looks unsound to the sessions
that found them.

- In [`prop-lem-type-eq-cycle.sl`](fail/prop-lem-type-eq-cycle.sl),
  forcing accepts `X := (Fn N (erased (Pin) q) -> (erased (False) f))`
  for a type `X` bound before the local type `Pin`, whose field has
  type `X`. The occurs check does not look into `Pin`. The equation can
  only be refuted, since `Pin` did not exist when `X` was bound.
- In [`prop-lem-matchable-pin.sl`](fail/prop-lem-matchable-pin.sl), two
  unified `Matchable`s are not equal as values, although §8 says that
  two that can be unified "become one". This looks like incompleteness,
  not unsoundness.

## Open questions

- Whether excluded middle for propositions, with `M` at or below `N`, is
  consistent with the language. No model or proof was attempted.
- The same for each "no refutation found" row of the table.
