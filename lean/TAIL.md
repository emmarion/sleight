# Tail calls as a theorem: a proposal

A proposal for the Lean development in `lean/`, not adopted. Nothing
here is decided; the open questions at the end are the owner's to
answer.

## Where things stand

DESIGN.md section 19 judges tail position "on the post-erasure code,
where erased positions, types, coercions and placings are gone and
every `let` that only renames has been resolved away". The reference
checks the `tail`, `notail` and `delegate` marks that way, after
elaboration (`check_marks` and `normalize` in `lib/elab.ml`).

Here the reader checks them while elaborating, against a syntactic
reading of the rest of the body (`returnsBinders`, `renamesOf`), so an
alias can mislead it: in a body
`(let ((many y)) (tail (id x))) (v y)`, with `v` an alias of `values`,
the reference accepts the `tail` and this runner refuses it
(`lean/HANDOFF.md` item 13). The marks never reach the core, so no
theorem says anything about them.

Every run the theorems describe is big-step (`eval`, `RunS`, `RunM`).
A big-step run has no stack, so, as far as a session can tell, "this
call reuses its caller's frame" cannot be stated about any of them as
they are.

## The proposal, in stages

1. **Marks in the core.** A `tail`, `notail` or `delegate` mark becomes
   a `.chk (.mark …)` just before the call, as uniqueness marks are
   carried now. The existing proofs would ignore it, which is expected
   to keep the churn small.
2. **Post-erasure code as a type.** An `ECode` (let, call, match,
   values) and a function from the core to it that drops erased
   statements, types, coercions and placings, resolves renaming `let`s
   and drops `at` returns, with a proof that running `ECode` agrees
   with `RunS`. Tail position is then defined on `ECode` by section
   19's rules, and a checked function computes it, in place of the
   reader's syntactic analysis. This alone would remove the alias
   divergence above and make the marks checked rather than trusted.
3. **A small-step machine for `ECode`** with an explicit stack of
   frames, and a proof that it agrees with the big-step run. This is
   what makes stack depth observable.
4. **The tail theorem.** At a call that passed the `tail` check, the
   machine enters the callee with the caller's own continuation: no
   frame is pushed. A possible corollary: a run made only of tail calls
   uses bounded stack. `delegate` could get a sharper statement: the
   caller's frame is replaced by the callee's, with its arguments
   passed straight through.

## Cost, as a session estimates it

Stage 1 is small. Stage 2 is a moderate change to the reader plus a
proof of agreement with `RunS`. Stages 3 and 4 are expected to be of
the order of the existing machine proofs (`MachineRun.lean`,
`MachineAsm.lean`). Stages 1 and 2 are useful without 3 and 4.

## Open questions

- What the theorem should promise: that no frame is pushed at a marked
  call (local), or that stack depth stays bounded across a run
  (global).
- Which run carries the stack: `ECode` beside `RunS`, or a small-step
  form of the heap machine `RunM`, which would put the guarantee on the
  low-level machine itself, at more cost.
- Which lets are folded away: section 19's rule only, or also the
  reference's further folding of lets that bind constants nothing
  mentions (its ASSUMPTIONS 164 and 189). Any difference would show as
  a tail verdict that differs from the reference's.
