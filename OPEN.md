# Open questions

Questions about the language that DESIGN.md does not answer, each
stated as a question. Nothing here is a decision. Section references
are to DESIGN.md.

## Soundness and invariants, unverified

1. Consistency: whether the language is sound with `Type : Type` and
   no positivity restriction (§10), termination being carried by the
   level and subterm order (§17) and types never computing (§9). No
   soundness argument has been written.
2. Erasure conservativity: whether every program that compiles still
   compiles and runs to the same values after collapsing `unique` to
   `many` (a `UniqueFn` to an `Fn`, every cell operation to an
   allocation, `share` and `slot-of` to the identity, `at` entries to
   ordinary entries, at-functions and at-matches to functions and
   matches whose bodies run), and again after collapsing `erased` to
   `many` with `Level` and the proof types given some non-erased
   representation and each `coerce` replaced by the value its proof
   names. The collapsed multiplicities would stay as inert designators
   that §7's unification still compares. Neither tier is verified.
3. Slot equality: what the soundness claim for slots (§35) must be,
   and whether it holds; in particular for a user type indexed by
   `(Slot)`, where a forcing merges two slots in an unrefuted branch.
4. Facts from stored values: a `comptime-match` trusts the evaluator
   (§29). Whether a reference evaluator inside the checker should
   arbitrate fact-bearing runs, so that a wrong evaluation cannot mint
   a `(False)` token through an erased field, is open.
5. Whether `Subterm` irreflexivity and the strict mint order of
   `Predates` deserve stated invariants, both appearing to be
   load-bearing for consistency.
6. Whether a `comptime-match`'s or a `let-match`'s `is`-declared
   fields and forced index unification are one mechanism.

## Design directions not taken up

7. A unified lexicographic-decrease proof: one proof structure
   reifying §17's whole order as a nested disjunction, so that a call
   need not name the decreasing argument when which argument decreases
   is known only through an erased computation.
8. Macros: `Macro` and `Raw` (§19) are unimplemented. Open are macro
   termination beyond a global expansion limit, and hygiene, perhaps by
   `Raw` carrying entry references beside names, with an out-of-scope
   reference being an error rather than merged into the current scope.
9. Compile-time evaluation inside a body: a `comptime` form, and a
   `hoist` form `(hoist L body)` whose mints count as happening just
   before `L`'s, so that the factory pattern of §57 could be written
   inline. Where such a body would run, and what the fact table would
   need at each `def-lvl`, are undecided.
10. A rewriting engine without the atom requirement: rules from
    expression to expression rather than from atom to expression (§7),
    and what that would do to §7's third failure mode, the occurs check
    and the table's self-consistency.
11. Whether the outer declaration syntax `name : signature` should put
    the name last as telescope entries do (§3), and whether `let`
    should put its binders last.
12. Whether a union newtype none of whose non-phantom constructors
    holds a non-erased field should be allowed (§21).
13. Whether `_` should be accepted as an entry of a `values` or as the
    scrutinee of a `let-match` (§50).
14. A source-level declaration of extern types and functions, in place
    of the prototype's fixed table (§42), and what guarantees an
    implementation's agreement with its model beyond the requirement
    stated there.
15. Whether an unrefined `else` should refine the scrutinee to exclude
    the listed constructors.

## `at`, slots and cells

16. Whether a `Coercible` may be minted from two variables in one slot
    (`at-coercible`), and under what restriction; as last proposed it
    is potentially unsound and is not implemented.
17. Whether a runtime comparison of two slots answering with evidence
    in the equal case (`slot-eq`) should exist, a compiler being free
    to always answer that they differ.
18. Relaxing §21's one-real-branch rule for an at-match (§40), which
    dispatches at no runtime.
19. Allowing the function in an `(at (f ...))` call to be erased, as a
    `Coercible` proof is.
20. What becomes of `coerce`, `Coercible`, the `coercible-*` forms and
    `Delegate` once the `at` system can express what they express; and
    whether a `Cell` for an extern type's constructor should exist
    outside an extern function's body (§43).
21. Whether `tail`, `notail` or `delegate` on a skipped at-function
    call (§39) should be the error it is or be ignored.
22. Whether a `cell-match` annotation written in the `at` form should
    make a `cell-match` skip its runtime as an at-match does.
23. Whether a shadowing sugar should replace same-name rebinding,
    `(let ((unique x)) (f x))` being the idiom.
24. The names of the forms above and of `vacant-slot`, `slot-self`,
    `at-fn-of` and `open-at-fn`.
