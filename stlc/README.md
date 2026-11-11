# Strong normalization of the simply typed λ-calculus

This directory was written by a Claude session at the owner's request. A
claim in this file that the checked proof does not make is a mistake in
this file. [NOTICE.md](NOTICE.md) credits the proofs it follows.

## Checking

```sh
stlc/check.sh
```

This checks two units, each with its own goal, and prints
`--goal proved: PASS` twice. It runs the reference implementation;
`SLEIGHT=_build/release/slc stlc/check.sh` runs slc instead.

## The statements

Both statements share [`types.sl`](types.sl), the simple types (`Ty`: a
base type and arrows), and rely on `NatLe` from `std/nat.sl`.

### Bounded reductions, over intrinsically typed terms

[`ispec.sl`](ispec.sl) is meant to be the easier one to check. A
`(Term g a)` is a term of type `a` in context `g` by construction: a
variable is a membership proof `(Mem g a)`, so the spec has no `Nat`
indices and no separate typing judgment. `(Insert b g h)` says `h` is
`g` with `b` inserted at some position. `Hole` names the variable at
that position, and `VarShift` maps every other variable of `g` to its
counterpart in `h`. Over these, `Weaken` and `Subst` are the usual
single-variable weakening and substitution, and their indices say they
preserve types. `OneStep` is full β-reduction, `Reduction g a k t u` a
sequence of `k` steps from `t` to `u`. The goal `BoundedReductions` asks
for every `(Term g a) t` a number `n` and a function proving `k ≤ n` for
every reduction sequence of length `k` from `t`. The function must
produce a first-order `NatLe` proof for every sequence.

### A structural decrease, over Curry-style terms

[`curry.sl`](curry.sl) defines Curry-style λ-terms with de Bruijn
indices (`Term`), shifting (`Shift`, through the index-insertion
relation `Skip`), substitution (`Sub`), one-step full β-reduction
(`Step`) and typing (`Typed`). [`spec.sl`](spec.sl) sets the goal
`StronglyNormalizing`:

- some predicate `P` on terms
- holds of every typed term (`typed`),
- and, whenever `P t` holds by a derivation `d` and `t` steps to `u`,
  holds of `u` by a derivation that is a strict `Subterm` of `d` (`step`).

So an infinite reduction sequence from a typed term would give an
infinitely descending chain of strict subterms, which is what this
statement relies on being impossible. `P` is existential, so the spec does
not fix any definition of strong normalization of its own. The proof
picks `Sn` in `reducts.sl`: a term is `Sn` when the list of all its
one-step reducts is all `Sn`, which is accessibility made finitely
branching.

A function-valued accessibility predicate, `(Acc t)` holding a function
from each step `t → u` to `(Acc u)`, would not do here. A closure at a
fresh level can call the function that builds it, so such a value can be
built for a relation that loops.

The proof is constructive and every lemma is an `erased` function
checked for termination by Sleight's levels and `subterm` arguments.

## The proof

- [`skip.sl`](skip.sl), [`ctx.sl`](ctx.sl), [`subst.sl`](subst.sl):
  arithmetic on `Skip`, context insertion, and the de Bruijn lemmas:
  existence and determinism of shifting and substitution, and their
  commutations (`shift-shift`, `shift-sub`, `shift-sub-lo`, `sub-shift`,
  `sub-sub`).
- [`jm.sl`](jm.sl), part 1: typed terms are in `SN`, an inductive
  characterization of strongly normalizing terms indexed by context and
  type, with neutral terms (`SNe`) and strong head reduction (`SNRed`).
  The main block proves closure under substitution (`sub-sn`, `sub-ne`,
  `sub-red`) and under application (`app-sn`), by lexicographic recursion
  on the type of the substituted variable and then on the derivation.
  The call from `sub-ne` to `app-sn` at a smaller type is where the
  first component decreases. `typed-sn` follows.
- [`reducts.sl`](reducts.sl): the list of a term's one-step reducts, its
  soundness and completeness, `Sn`, and `sn-step`.
- [`steps.sl`](steps.sl): reduction commuting with shifting and
  substitution, neutral terms, and how a step from a weak head redex
  relates to its contractum (`head-step`).
- [`proof.sl`](proof.sl), part 2: `Sn` is closed under abstraction,
  application of a neutral term, and weak head expansion. Each is proved
  by a walk over the reduct list, recursing lexicographically. Then `SN`
  implies `Sn`. [`qed.sl`](qed.sl) proves `StronglyNormalizing`.
- [`ibridge.sl`](ibridge.sl): erasure from intrinsic to Curry-style
  terms, which is typed and carries weakening, substitution and steps
  across, and a height on `Sn` derivations that drops along every step.
  [`curry-names.sl`](curry-names.sl) keeps the Curry-style constructor
  names reachable before `ispec.sl` reuses them, which is what the four
  shadowing warnings of the second unit are about. [`iqed.sl`](iqed.sl)
  proves `BoundedReductions`, with the height of the erasure's `Sn`
  derivation as the bound.

## Strength

The README at the repository root puts Sleight's strength at about IΣ₂.
The usual Tait/Girard reducibility proof quantifies over predicates on
terms, which that strength appears not to allow. The proof here uses only
induction on types and on finite derivations, which is why it was chosen.
This is a reading of why it fits, not a proof that the other does not.
