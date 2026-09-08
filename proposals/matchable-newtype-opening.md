# Proposal: opening a `Matchable` or `Newtype`

Status: a proposal discussed with the owner, not yet adopted into
DESIGN.md. Section 1 is the proposal itself; section 2 is rationale and
implications, and is not normative.

## 1. The proposal

**Ambient scope no longer suffices.** A `Matchable` or a `Newtype` does
nothing by being in scope; nothing consults it until it is **opened**.

**Two forms**, each naming one object, taken at `erased` multiplicity and
read for its type, not its value:

- **Non-contradicting open** — a *statement*: binds no source name,
  produces no values, mints facts, and records the opened *entry*. Its
  extent is the rest of the containing expression, and it is discarded
  exactly when the entries minted alongside it are — a match branch
  discards both, a `let` right-hand side retains both. Requires the
  assertion below to **hold**.
- **Contradicting open** — an *expression*, its size and multiplicities
  given by a declared return telescope, or by `_`, which reuses the
  enclosing function body's or match branch's telescope and is an error
  elsewhere (sugar, as for a match annotation). Records and mints
  nothing. Requires the assertion below to **fail**.

**The assertion**, on opening `M`:

1. `M`'s listed constructors are pairwise distinct after
   canonicalization; and
2. for every already-open `M'` that shares a canonical constructor with
   `M`, **or** heads a canonically equal type constructor, `M` unifies
   with `M'` — recursively through the enum/union tag, the
   constructor-list length, the per-constructor multiplicity markers,
   the constructors, and the type constructors, hence their signatures.

**The open record holds an entry reference.** Two opens that unify
**merge**; the record keeps a non-erased entry where one is available.
(A `Newtype` is always erased, §38, so this bites for `Matchable`s only.)

**Requires a prior open:** §18's constructor-disjointness rule; `match`;
`comptime-match`; §12's and §37's emptiness check; `matchable-of` and
`newtype-of`, which search only opened ones; and `coercible-wrap`, which
requires an opened `Newtype` for `C`.

**A match at a non-erased position with a non-erased scrutinee** requires
the opened `Matchable` for its scrutinee's type to be a non-erased entry.

**Not gated:** §18's occurs check and its signature-based refutation.

`def-adts`, and the FFI's equivalent (§41), auto-open what they mint.

## 2. Rationale and non-obvious implications

**It finishes §19's reification.** §19 reified the constructor list as
first-class data but left the judgment ambient and always-on. Opening
makes no-confusion a named hypothesis; the contradicting open is its
elimination rule, made explicit.

**The behavioural delta is narrower than it looks.** Signatures already
refute most constructor pairs — `Nil`/`Cons`, `Zero`/`Succ` differ in
arity. The `Matchable` is load-bearing only for pairs whose signatures
unify (`True`/`False`, same-shaped enum constructors). Both cost and
benefit are confined there, and §18's edit is one word.

**Facts can now be held before they explode.** Equating `True` with
`False` while nothing is open succeeds by minting `True is False`;
opening later cashes it in. That latency is what makes the contradicting
open a coherent primitive rather than a bolt-on.

**Unopened means opaque, upward too.** Since two type constructors are
told apart by their `Matchable`s, an unopened first-class `TyCtor`
becomes indistinguishable from any other — apparently a gain for
abstraction. It also answers SPEC-REVIEW 6 by a general rule: opaque
built-ins have no `Matchable`, are never opened, so are neither
matchable nor empty.

**Ambiguity of content becomes impossible.** Two opened `Matchable`s
either unify or contradict, so §19's ambiguity error and SPEC-REVIEW 25
go. Unification equates terms, not entries, so a preference over entries
survives — but only over erasure, which is the one axis a non-erased
match can actually fail on.

**The visible-vs-`Dyn` tier leaves the design entirely.** Because
`def-adts` is the sole minting site and two opened `Matchable`s for one
type describe the same `T`, they hold the same value; which the merge
keeps looks like it can only affect code quality. So `Known` vs `Held` —
whether the compiled match reads a `Matchable` at runtime — becomes a
pure code-generation specialization applied to whatever the merge kept,
not a rule the language states. It also means the existing
non-erased-match check is relocated to the open record rather than newly
invented.

**Nothing needs a source name, so `let`-style shadowing never arises** —
which is what dissolved the original scoping worry.

**Scope: not pruning is soundness-neutral, pruning is not.** Extra
disjointness is true (minting monopoly) and can only refute more — it
changes which programs are accepted, never whether an accepted one is
correct. Retracting facts while the entries recorded under them survive
leaves those entries claiming types nothing justifies. ASSUMPTIONS 29
already records that facts leak past a `let` right-hand side today,
excused by the leaked facts being unconditionally true; an open's qualify
on the same ground, with one clause added — a lying first-class
`Matchable` leaks only inside code already dead, its parameter being
uninhabited.

**A half-pruning trap.** Disjointness is consulted today by scanning the
scope list, which a `let` restore prunes, while `add_rule` writes to the
fact map, which it does not. An open reached through the scope list would
prune its disjointness at the right-hand side's end while retaining any
`T is T'` it minted — the one combination that breaks. Both halves must
share a fate.

**A lying first-class `Matchable` self-refutes.** Where the true one is
open, opening one that misstates the tag or a phantom marker *is* a
contradiction, so the non-contradicting form refuses it and the body must
be written as the contradicting one — correctly, since such a parameter
is uninhabited. The false marker never reaches §12's erasure exemption.

**Opening is a fact-minting site, not just an assertion.**
Cross-`Matchable` unification can mint `T is T'` and `Ci is Ci'` into
enclosing entries. §18's soundness argument for forcing is about runtime
gating and does not cover this; the justification here is §12's
one-constructor-one-type discipline plus §19's minting monopoly, making
these facts unconditional within their scope rather than
hypothesis-gated. §18 would need to carry both.

**`Newtype` gains uniformity rather than a fix.** ASSUMPTIONS 45 notes it
has no ambiguity case, and gating doesn't change its provenance-based
trust. What it buys is that `coercible-wrap`'s dependency becomes visible
at a site the programmer wrote, and that the two objects keep parallel
rules.

**Not yet settled:** whether `coercible-of`'s ambient fetch gets the same
treatment; whether a `Newtype` has a contradicting form at all, and
whether an opened `Newtype` for `C` alongside a `Matchable` marking `C`
phantom is itself a contradiction; the contradicting open's clause in
§23's erasure invariant; §16's definition of a statement, phrased in
names, which would need to admit one that emits only facts and to reckon
with names being pruned at a right-hand side while facts are not; and
whether the contradicting open with `_` as a whole function body makes
§37's `absurd` marker redundant for the `Matchable`-contradiction route.

## 3. Implementation notes

Not normative. Implemented in `lib/` and `self/` by a session at the
owner's request; the owner settled the following in chat, and
ASSUMPTIONS.md 114-116 record the session's reading of the rest.

- The two forms are `(open-adt e)`, the statement, and
  `(open-absurd e ann)`, the expression, `e` any erased expression
  naming a `Matchable` or `Newtype` entry and `ann` a return telescope
  or `_`. One form opens both objects, so the keyword names the
  minting site rather than either kind.
- A `Newtype` is recorded only: `open-adt` merges it with an opened one
  naming the same constructor and asserts nothing else, and
  `open-absurd` refuses a `Newtype`, its contradicting form being among
  the points section 2 leaves unsettled.
- `let-match` requires the opened `Matchable`, as `match` does;
  `coercible-of` keeps its ambient fetch for now (a TBD for DESIGN.md
  section 38).
- `coercible-ctor` drops its phantom check and so consults no
  `Matchable`; the reading behind that is ASSUMPTIONS 116.
- DESIGN.md is not yet edited.
