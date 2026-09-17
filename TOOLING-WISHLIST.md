# Tooling wishlist for writing .sl by hand (or by LLM)

Observations from one session rewriting `mini/` without fuel: each item is a
point where the session lost time or guessed, with what would have helped.
Nothing here is a design decision; it is a log of friction, in the order met.

1. **Paren-depth locator.** Every unbalanced file was diagnosed with an ad hoc
   script printing the nesting depth at each `(many f :` line. A checker
   error like `line N: syntax error: missing )` names the end of the file; a
   per-form report ("form starting at line N opened 3 more than it closed")
   would have found each of the five imbalances met so far at once.

2. **Error locations inside a form.** Type errors report the line of the
   enclosing `def-fns` (e.g. `expected 3 arguments, got 2` on a 20-line
   function). The offending sub-expression, or at least its line, would cut
   most of the guesswork.

3. **Shadowing report.** `Canonical` exists in both `mini/canon.sl` (two
   arguments) and `mini/elab.sl` (three); after loading both, the first is
   unreachable by name and a use of it fails with an arity error far from
   the cause. A warning on redefinition, or a way to qualify names, would
   have caught this immediately.

4. **`let-match` on GADT-refined evidence.** `let-match` insists on a
   single-constructor type, so evidence types with two constructors (one
   of them ruled out by the index) still force a nested `match`, which is
   what makes these functions 20 levels deep. Accepting a `let-match` when
   the index leaves one constructor possible would flatten most of
   `elabfn.sl`.

5. **`else` does not refine.** After `(else ...)` the scrutinee is not known
   to differ from the listed constructors, so an empty erased match there is
   refused; the workaround is enumerating the remaining constructors by hand
   (14 keys in `axiom-check`). A refined `else` would remove that noise.

6. **Arithmetic on `Lt`.** `Lt n (Succ (Succ n))` from `lt-succ` needs
   `lt-weaken`, `le-trans` needs its middle term spelled, and every one of
   these was a compile-fix round. A small solver for `Lt`/`Succ` goals over
   the prelude lemmas, even one that only chains `lt-succ`/`lt-weaken`/
   `le-trans`, would remove a class of errors.

7. **Wrapper boilerplate.** Facts about the entries of a context are stated
   over a `(MkCtx n s e r a l sa)` record, so every wrapper (`Sc`, `ScL`,
   `Has`, `Grew`, `Cov`, ...) carries seven erased fields and every use is
   `(MkSc _ _ _ _ _ _ _ t p)`. Record projections usable inside types, or a
   way to define a wrapper by "the `e` field of `ctx`", would remove most of
   the underscores in `mini/ctx.sl` and `mini/elabfn.sl`.

8. **Positional evidence lists.** Constructors with 20 to 40 erased fields
   (`EXCall`, `EBCons`, `MkWF`) are called positionally; a misordered pair
   surfaces as a type mismatch with no hint of which position. Named
   fields, or an error naming the position, would help.

9. **Subterm bookkeeping.** Mutual recursion needs every function of a group
   to align the same number of `subterm` positions, with `is`-typed
   constants (`(POuter (PInner))`, `(Nil (Raw))`) as fillers. A way to
   declare "this call is a sub-call of that one" (or an implicit phase
   position) would remove the filler arguments.

10. **Whole-file compile per fix.** Each fix recompiles the whole prefix of
    files; an incremental mode that keeps the earlier files' environment
    would make the edit loop several times faster.

11. **Duplicate constructor names across files.** `CRNil` (a helper in the
    new `elabfn.sl`) silently shadowed `CRNil` of `CheckRets` in
    `mini/elab.sl`, and `ALOk` shadowed `AfterList`'s; `AOk` is already
    defined by both `mini/unify.sl` and `mini/elab.sl`. The symptom is an
    arity error at the use site. A one-line `uniq -d` over constructor
    names found all of them at once; the checker could do the same.

12. **Branch misalignment reads as a type error.** When a branch closes one
    paren too few, the next branch lands in the enclosing `match`, and the
    error is `BTrue is not a constructor of SameDec` or `Ref is not a
    constructor of ExprArgsDec`, far from the missing paren. An editor
    that shows the enclosing `match` of each branch (or the checker naming
    the branch's scrutinee and line) would turn each of these into a
    one-line fix; a formatter that re-indents by nesting would make the
    imbalance visible before compiling.

13. **No branching on erased data, so keys are enumerated.** An erased
    proof of `AxiomKey k` cannot be matched with three real branches, and
    `else` does not refine `k`, so the three axiom keys are dispatched by
    matching `k` itself and the other fourteen keys each get an empty
    erased match. Either a refined `else` (item 5) or an erased match that
    only refines (no runtime branch) would remove that.

14. **The good news, for calibration.** Once the parens balanced, the
    whole 2700-line elaborator type-checked with the subterm discipline
    (three lexicographic positions across a group of sixteen mutually
    recursive functions, `is`-typed constants as phases) accepted on the
    first try; the checker's GADT refinement through erased single-branch
    matches and omitted impossible branches behaved exactly as guessed.
    The cost was almost entirely in bookkeeping, not in the type system.

15. **Stack depth in `slc`'s compile-time interpreter.** Three of the
    `mini/` end-to-end programs overflow the OCaml stack inside `slc`
    under the default 8MB limit (before and after this change), while the
    reference interpreter runs them; `ulimit -s unlimited` is enough. A
    heap-allocated continuation, or at least a message naming the limit,
    would keep `self/bootstrap.sh` honest on programs that evaluate
    deeply at compile time.
