# F4. `coercible-of` fetches the newest anonymous proof, shadowing the delegate proof

Status: fixed in `fa5747a` (`lib/elab.ml` `Sp.CoercibleOf`, `self/elab.sl`
`ExCoercibleOf`); test `tests/coercible_of_shadowed.sl`. Severity:
rejects a valid program. Pre-existing at `8091d86`; the uniqueness sides
made it bite.

## The rule

DESIGN.md section 38 item 6: `def-fns` mints the proof
`(Coercible (Fn ...) g (Fn ...) f)` anonymously for a `delegate`-bodied
`g`, and `coercible-of` fetches it from ambient scope by naming `g`.
UNIQUE.md U6 extends this to `def-unique`, and U7 gives that proof the
sides `(Unique)` to `(Shared)`.

## The defect

The search took the newest anonymous scope entry whose type is a
`Coercible` with `g` in the source-value slot. Every proof-minting form
binds its result anonymously too, so any later proof about `g`, a
`coercible-refl`, a `coercible-sym`, shadowed the delegate proof. Before
the sides existed the shadowing proof was still a true proof and
`(coerce g p)` produced `g` itself, so nothing was observable. With U7's
sides a `refl` proof is `(Shared)` to `(Shared)`, so the `coerce` used `g`
at many and was refused.

## Reproducer

```scheme
; expect: 1
(def-fns _ $ many id : (many (Nat) x) -> (many (Nat) r) x)
(def-unique _ $ unique d : (many (Nat) x) -> (many (Nat) r) (delegate (id x)))
(let (erased junk) (coercible-refl (Shared) d))
(let (erased p) (coercible-of d))
(let (many f) (coerce d p))
(f (Succ (Zero)))
```

Before the fix: "unique value d needs an explicit share".

## The fix

Search oldest-first. The delegate proof is minted by the very `def-fns`
that binds `g`, before any user code can name `g`, so no anonymous
`Coercible` about `g` can be older than it; oldest-first is exact.

## Caveats

Soundness-neutral: the wrong proof was always a true one. "Oldest wins" is
exact but implicit. The more robust alternative is a flag on the minted
entry, and section 38 item 6 carries its own TBD about whether the fetch
should find only an opened proof; either would make it explicit.
