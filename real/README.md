# Constructive Cauchy reals

`defs.sl` defines the constructive Cauchy reals of the Rocq Prover's
standard library (NOTICE.md), restated in Sleight. Load it after
`std/macro.sl`, `std/nat.sl` and `std/list.sl`.

## Integers and rationals

- `Z` has Rocq's shape: `Z0`, `(Zpos p)` for p+1 and `(Zneg p)` for
  −(p+1), over `Nat`.
- `(ZView z p q)` says z = p − q for the canonical pair, and `ZAdd`,
  `ZMul`, `ZLt` and `ZLe` are stated through it.
- `(Qmake n d)` is the rational n/(d+1), not reduced. `QLt`, `QLe`,
  `QPlus`, `QMult`, `QOpp`, `QMinus`, `QAbs`, `QInv` and `QPower` are
  relations whose last index is the term Rocq's function returns.
  `QRed` states `Qred` by its result: the same value in lowest terms,
  with a positive denominator.

## Reals

Sleight cannot prove that two calls of one function on one argument
return the same value, and a type cannot contain a call, so a sequence
is a relation rather than a function:

- `(MkSpec E env R scale)`: `R` is a relation over an index n : `Z` and a
  term q : `Q`, taking an erased parameter `env` of type `E`, and `scale`
  is Rocq's `scale` field. `(SeqAt s n q)` says q is term n of `s`.
- `(CReal M s)`: a function at level `M` giving, for each n, a term with
  its `SeqAt`, a proof that `s` relates each n to at most one term, and
  `QCauchySeq` and `QBound` as in Rocq, stated over `SeqAt`.

`CRealLt`, `CRealLe`, `CRealEq` and `CRealAppart` take the relations, so
they apply to sums and products as well as to `CReal`s. `CRealPlus`,
`CRealOpp`, `CRealMinus` and `CRealMult` relate two relations (one for
`CRealOpp`) to the relation of Rocq's sum, opposite, difference or
product, whose terms and scale follow Rocq's definitions.
