# Working agreement for this project

This is a from-scratch prototype OCaml implementation of a programming
language design belonging to the repo owner. Ground rules below were set
by the owner and apply to every session.

1. **Hedge permanent claims.** Anything committed to git — code comments,
   commit messages, docs, design notes — must hedge any claim that doesn't
   come directly from the owner. This subfield (type theory / advanced
   OCaml type-system features) is one where Claude can get confidently
   wrong, and unhedged claims compound when read by future Claude sessions.
   Confident prose is fine in chat with the owner if it helps move things
   along, but even there, defaulting to the same hedging habit is safest.

2. **Compile a claim rather than arguing it, when reasonable.** Prefer
   `dune build` / running the type checker as the arbiter over prose
   argument about whether something type-checks or behaves a given way.

3. **This OCaml install may exceed what's in Claude's training weights**
   for existential types, GADTs, etc. — e.g. a `let` or plain function can
   open an existential type *and* get proper GADT branch refutation of the
   other variants at the same time. Don't assume training-data intuitions
   about OCaml's type-system limits are current; check by compiling (rule 2).

4. **Minimal comments.** Do not add comments unless the owner gives
   explicit permission for that instance. The one standing exception: brief
   notes explaining GADT type variables, especially where a variable's
   binding site is far from its use — those are welcome without asking.

5. **Keep code succinct.** Optimize for a small overall codebase. Use
   descriptive names, but aggressively DRY — abstract away repetition
   rather than duplicating variants of similar code.

6. **Don't optimize for performance.** Correctness first, then
   readability. It's fine — expected — for edge cases to drive the core
   design/reasoning rather than being bolted on after. Forcing code to
   primarily reflect the "common case" tends to produce duplicated,
   verbose, more error-prone code; avoid that shape.

7. **Design first, implementation second.** Prioritize the quality of the
   resulting language design over ease/difficulty of implementing it.

8. **This is a feature-showcase prototype, not a product.** No goals
   around ergonomics or performance. Soundness/correctness is essential
   and non-negotiable.

9. **Think like a mathematician.** Reach for abstraction and generality
   as primary tools, not just as cleanup after the fact.
