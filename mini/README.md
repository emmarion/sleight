# mini/: the minimal language's semantics as relations

`mini/` writes down the semantics of the minimal language of MINIMAL.md in
the full language: each judgment is an ADT whose constructors are its
rules, and beside each relation stands a function that derives it by
structural recursion, or answers "stuck" on a shape the rules have no
derivation for (evaluation alone still burns fuel). Everything here is one session's proposal
made autonomously at the owner's request; the decisions in MINIMAL.md are
the owner's, the shapes below are the session's and open to revision. A
claim in this file that the tests do not make is a mistake in this file.

## Files, bottom up

- `base.sl` — booleans, decided equality on `Nat` and `Bool` with
  inequality evidence, list indexing with evidence.
- `term.sl` — `Term`, DESIGN.md section 5's grammar with de Bruijn
  telescopes, and three relations with their functions: `Subst`
  (instantiating binders), `Abstract` (turning entries into binders) and
  `Assignable` (section 18's occurs check and third contradiction).
- `canon.sl` — `Rule` and `Canon`: a term's canonical form under the
  rules in force, structurally (sections 5, 18).
- `ctx.sl` — the context: entries with a kind (`KDecl` for constructors
  and type constructors, rigid; `KLevel` for `def-lvl`'s entries), names,
  declared ADTs, rules, the ambient level and subterm arguments (section 3);
  then, for the functions only, what it means for terms, rules, names and
  ADTs to mention only the context's entries, and for one context to have
  grown from another.
- `unify.sl` — `Unify`: section 18's forced unification as a walk over
  equations, in `Force` mode minting rules and in `Check` mode comparing
  for identity, with the three contradictions as its `UFail` rules.
- `core.sl` — `Core`, what programs elaborate to; `Val` and `Env`.
- `eval.sl` — `Eval`: big-step evaluation.
- `elab.sl` — `ElabProgram`, `ElabExpr`, `ElabStmt`, `ElabTerm` and their
  helpers, each judgment total with an `Ok` or `Err` outcome; `Fails` is
  the `Err` outcome of a program.
- `elabfn.sl` — the deriving functions for `elab.sl`.
- `preserve.sl` — groundwork for the open preservation argument below:
  canonicalization is a function of the rules, and `ElabTerm` forms only
  what `TypeOfTerm` types. Not needed by the elaborator.
- `tests/mini_*.sl` — what runs, under `dune test`.

## Shapes chosen here, for the owner to confirm or change

- **Structural recursion, with the invariants it needs carried beside the
  data.** Only `eval` burns fuel. Canonicalization recurses on a rank
  bound then the term, the ranks ordering the rules so that following one
  strictly lowers the bound (`canon.sl`); unification walks the two terms
  of an equation and, when it mints a rule, restarts on a count of the
  rule-free entries that the mint lowers (`unify.sl`); elaboration
  recurses on the raw syntax alone, every function carrying the
  context's well-formedness (`WF` in `elabfn.sl`: the ranking, ids below
  the next one, everything scoped, declared constructors' types being
  value-constructor formers, every ruled entry non-rigid) and returning
  it for the context it produces. Results are ADTs holding the derived
  data and the erased derivation, or a `Stuck` constructor, which the
  functions reach only on a malformed shape, with one exception: the
  type of a closed term (`type-of-term` in `unify.sl`), which `UAssign`
  and `MintTele`'s `is` entries need, has no derivation for a `Bound`
  outside its binder or an application whose head's canonical type is
  not a former, and the carried invariants do not exclude those inputs.
  One session found a program that reached it while `ETValCtor`
  accepted any type as a `ValCtor` former's return and `UAssign` related
  a variable to a term with no check on their types
  (`tests/mini_untyped_rule.sl`). The owner then restored ASSUMPTIONS 80
  (the return canonicalizes to an application of a type constructor not
  among the former's own binders), which refuses that program, and had
  `UAssign` equate the variable's type with the term's next, as `UAlias`
  already did, so that every rule unification mints relates terms whose
  types it has unified; `Refine` then forces one equation, the type
  equation following from it. Whether any program still reaches the
  stuck is open: the session's reading is that showing it needs the
  invariant that every application head in play has a former's type,
  carried through the elaborator and unification, which is not attempted.
  Two relations changed for this, both flagged for the owner: `Subst`
  gained `SubBeyond` (a `Bound` past the end of the substitution stays,
  making substitution total), and `Unify`'s twin left/right rules for a
  variable against a non-variable were merged through `Sided`.
- **`Univ` is a term.** Section 10 makes the universe a nullary type
  constructor with `Type` an entry rewriting to it; here `Univ` is a
  constructor of `Term`, `Type` an entry whose rule is `Univ`, and
  `Type : Type` the rule `TotUniv`.
- **Built-ins.** Entries 0 to 3 are `Level`, `Predates`, `Subterm` and
  `Type`; the first three are `KDecl` with no declared ADT, so they are
  neither matchable nor empty (section 19's decision carried over).
- **Substitution without arithmetic.** A substitution is a list indexed
  by `Bound`, a `None` standing for a binder passed on the way in, so
  going under a telescope entry is prepending a `None` and nothing is
  ever shifted; abstraction is the same list over entry ids.
- **Ids never reused**, with one exception. The context's `next` survives
  leaving a scope; everything else is restored (`Leave`), or only the
  names are (`Hide`, for a let's right-hand side, section 16). The
  exception is the entries a telescope is elaborated with (`ElabTele`),
  which are abstracted into binders and dropped with their ids, `ElabTerm`
  being pure.
- **Levels and proofs are `CToken`**, unit at runtime; `def-lvl` mints a
  fresh entry of kind `KLevel`, and `prove-predates x L` checks `x`'s id
  is below `L`'s, section 8's counter taken literally.
- **Surface syntax of the minimal language.** With no multiplicities to
  mark them, telescopes and binders are grouped in lists, which the full
  language does not do: `(Fn L (params) (rets))`, `(TyCtor (params))`,
  `(ValCtor (params) ret)` (the return an application of a type
  constructor other than the former's own binders, ASSUMPTIONS 80), `(def-fns L (f (params) (rets) items...)...)`,
  `(def-adts (T (params) (C (fields) ret)...)...)`,
  `(let (binders) items...)`, `(match s (rets) ((C fields...) items...)...)`;
  an entry is `(T x)`, `(subterm T x)` or `(e is x)`; a binder `x`, `(T x)`
  or `(e is x)`. Keywords are turned into `RKey` by the reader, so they
  are reserved and never names.
- **Malformed syntax has no derivation.** `Fails` records why a
  well-formed program is refused; a shape the rules do not recognize
  derives nothing, and the functions answer "stuck" on it. A branch
  pattern with the wrong number of field names counts as such a shape.
- **The axioms** (section 8) read both proofs' canonical types through
  `PredatesShape` and `SubtermShape`, compare the shared parts with
  `Same`, and mint the conclusion; the three ways they fail are one
  `AxiomBad` relation.
- **Refutation and coverage** (section 12, MINIMAL.md): a listed branch
  whose forced unification contradicts is `RRefutedBranch`; an unlisted
  constructor must be refuted with anonymous fields, else
  `RMissingBranch`.
- **The decrease check** (section 9) reads the callee's `Fn` level and
  telescope; `(subterm p)` before the i-th argument needs that argument's
  entry marked, every earlier marked argument the same as the enclosing
  function's, and the proof's small side that argument and big side the
  j-th enclosing subterm argument; `(predates p)` needs a proof from the
  callee's level to the current one.

## Open

- A reader from text to `Raw` is not written; tests build `Raw` by hand.
- The metatheory MINIMAL.md anticipates (determinism of elaboration,
  totality of unification, confluence of canonicalization, evaluation of
  every well-typed program) is stated nowhere yet.
