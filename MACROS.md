# Macros: proposals

Proposals for macros (DESIGN.md sections 62 to 65) that are not yet in
DESIGN.md. Each moves to DESIGN.md, in wording the owner confirms, once
it is adopted.

## 1. `settled-ty-apply`

**The gap.** Inside a macro, a handle's indices are static: after
`(let-match many a (RawSettled p m A x c))`, `A` is an erased variable
of the macro body, and `(MkPair A A v v)` checks at `(Pair A A)`. But
no form yields a handle of type `(Settled (MErased) Type (Pair A A))`,
so such a value cannot be passed to `mint-settled`, and a macro cannot
mint at a type that no `Settled` entry names. The `mint-settled` family
mints opaque entries, so it cannot help either.

**The form.** `(settled-ty-apply mw c a1 ... an)` is a special form,
not a `def-prim`: its arity is that of the type constructor's
telescope, as `coercible-ctor`'s arguments follow its constructor's.
It applies a type constructor to handles and mints the application,
with the application visible in the type of the handle it returns.

It is checked as a call is, with one handle per entry of the
constructor's telescope, in order: `mw` at `unique`, and `c` and each
`ai` at `many`, so `_` cannot stand for a handle. The type of `c` must
canonicalize to `(Settled (MErased) F t)`, where `F` canonicalizes to a
`TyCtor` former `(TyCtor (B1 b1) ... (Bn bn) -> Type)`. The type of each
`ai` must canonicalize to `(Settled (MErased) Ai ti)`, where `Ai` is
identical to `Bi` instantiated with `t1` to `t(i-1)`. These are read
against the facts in force where the form is written, branch-forced
ones included, so a `JMRefl` from `settled-eq` can refine an index that
an application then relies on. The results are
`(unique (MacroWorld) mw2 at mw)` and
`(many (Settled (MErased) Type (t t1 ... tn)) h)`.

Every handle's `Mult` is `MErased`. A handle at another `Mult` is made
`MErased` first by `settled-erase`; a type constructor's own handle,
from `settled-of erased` or `resolve`, is `MErased` already, since a
type constructor enters scope erased, and so is a handle from
`settled-type`.

Where it runs, it mints a fresh anonymous `Settled` entry, erased,
whose minted type is `Type` and whose `is` rule is the application of
the entries that `c` and the `ai` denote; `h` reads its minted `is`.
Like an entry that `mint-settled-erased` mints, it is outside every
scope and has no introduction order. Unlike one, it is not opaque, so
`settled-eq` and a splice of `h` see the application. In an erased
position the form is checked and mints nothing.

**Example.** Given an `MMany` handle `c` to a value `v` of a user's
type `A`, with `pair-h` bound at the top level to
`(settled-of erased Pair)`:

```scheme
(let ((many th)) (settled-type _ _ _ c))
(let ((unique mw1) (many ph)) (settled-ty-apply mw pair-h th th))
(let ((unique mw2) (many h)) (mint-settled mw1 _ ph (MkPair A A v v)))
```

**Decided by the owner.**

- The name `settled-ty-apply`, and `settled-val-apply` for the value
  constructor variant.
- No `here` argument: every error is static.
- `F` must be a `TyCtor` former canonically. A macro cannot apply a
  type constructor it was handed as an argument unless it first learns
  the signature, for example by `settled-eq` against a reference
  handle. This limitation is accepted for now.
- An erased position is allowed, and the form only checks there.
- Every handle, the result included, is held at `many` and indexed at
  `(MErased)`.
- The static check reads the facts in force where the form is
  written, branch-forced ones included.
- `t` is not otherwise restricted: requiring a handle to it already
  confines it to what a `Settled` entry denotes.
- Both compilers implement it, `lib/elab.ml` and slc in `self/`. The
  Lean development in `lean/` is not touched.

**Why it appears sound (a sketch, not a proof).** Only built-in forms
create handles, so a handle denotes its index (DESIGN.md section 64),
and the term minted at runtime is the term checked statically, under
that denotation. A branch-forced fact used by the check was justified
by the run that reached the form. An implementation may also re-check
the application against the run-position facts where it mints, as a
guard.

**On adoption.** A paragraph at the end of DESIGN.md section 65, the
form added to section 54's expressions and to section 42's macro
bullet, and OPEN.md 35, which asks for this, deleted.

## 2. `settled-val-apply`

The value constructor variant is deferred: the owner expects it to
carry nuance beyond the type constructor case. Open: the multiplicity
of its result, how the value is built when it runs, and what it
requires of the handles to non-erased fields.
