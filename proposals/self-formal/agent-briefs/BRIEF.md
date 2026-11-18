# Shared brief for the overnight exploration (read fully)

You are one of several agents exploring, overnight, the options for a
project the owner of this repository (emmarion/sleight, at
/home/user/sleight) wants: **formalize Sleight in Sleight, then have a
compiler (slc in self/, or a new one) proved to agree with that
formalization, with as little fuel as possible.** The owner is asleep.
When they wake, they want concrete proposals, trade-offs, decisions they
must make, and the context for each decision. Nothing is being decided
tonight; everything you write is a proposal.

## Ground rules (from CLAUDE.md, which you must read and follow)

- Read CLAUDE.md in full first. Then read ALL of DESIGN.md (3156 lines,
  72 sections) — every section, in chunks, not a summary (rule 19).
  This is non-negotiable: a previous session kept making false claims
  about what DESIGN.md says.
- Hedge every claim that isn't the owner's (rule 1). Distinguish
  explicitly, in what you write, between:
  (a) what DESIGN.md says — cite the section and quote the words;
  (b) what the code does — cite file:line;
  (c) what the owner has decided — ONLY the items listed under "Owner
      decisions" below;
  (d) your own reading, inference or proposal — say so.
- Compile a claim rather than arguing it when reasonable (rule 2, 3).
  `dune build` builds the reference; `_build/default/bin/main.exe f.sl`
  (or `dune exec bin/main.exe -- f.sl`) runs a Sleight file with the
  prelude. MANUAL.md has flags (`--goal`, `--no-prelude`, ...).
- ASSUMPTIONS.md records sessions' choices, NOT owner decisions (rule
  14). Never cite it as the owner's view. Do not treat lean/ as a
  blueprint (the owner strongly discourages relying on it); you may
  mention it as a cautionary data point only.
- Do NOT edit DESIGN.md, ASSUMPTIONS.md, DECISIONS.md, OPEN.md or any
  existing file. Write ONLY your own output file(s) under
  /home/user/sleight/proposals/self-formal/ (create it if missing).
  Prototype code goes under /home/user/sleight/proposals/self-formal/proto/<your-topic>/.
  Do NOT git commit or push; the coordinating session commits.
- Minimal comments in any code (rule 4); succinct code (rule 5).
- Oxford commas in prose (rule 22).
- A proposal states the design, succinctly, not how it came about.

## Owner decisions / statements (from a handoff written by an earlier session; these are that session's paraphrases)

1. No `no_false`-style consistency theorem is expected (diagonalization).
   Wanted instead: "we parameterized the semantics of the language, and
   this, or the syntax of the language, or both, and our compiler is
   proven to be in agreement with those."
2. A fuel-free self-interpreter may be possible because the top level is
   not a function; it is the continuation the driver loops over — the
   prelude's `Program` with `Continue` and `Exit` (DESIGN.md §27, §42).
   Whether that makes sense for the interpreter was left to analysis.
3. It should be a theorem that every program's source code is either
   accepted or rejected as an error.
4. On compile-time termination: the owner was in "general agreement"
   (not agreement to exact statements) with: (i) the compiler can only
   diverge if the spec's own run of some compile-time code diverges;
   (ii) under a hypothesis H that every accepted compile-time form's
   spec run halts, `compile` is a total function to accepted-or-rejected.
5. Don't rely much on the Lean proof in lean/; its handling of slots and
   mutation might be worth rewriting.
6. The owner suspects the spec's run should be a mutating heap machine
   from the start. The owner's concern about running with erased
   positions removed ("stripped mode") goes away if the heap is mutable.
   (A session read these together as "the spec's run is a mutating heap
   machine on code with erased positions removed"; NOT confirmed.)
7. The owner voiced concern about: not modelling a heap machine; a pure
   order-free run; running in stripped mode (covered by 6). The owner
   also asked whether DESIGN.md spells out evaluation order.
8. DESIGN.md §21 makes a missing branch an error ("A constructor with no
   branch must either be refuted or be covered by the `else`.").

Also: the owner's goals include "minimize fuel use", and "process:
analysis and proposals first; later, agents do the work".

## Proposals from the earlier session (NOT approved; may be wrong; treat as one input, not a blueprint)

A. Evaluation order: statements in written order, then the final form;
   within one form, sub-expressions left to right, head first. Note §15's
   argument-hoisting rule ("Every argument to a constructor, a function
   or a cell behaves as if it were first bound to an anonymous variable
   ... placed just before the statement or final form that contains the
   call") already fixes some order — check exactly how much.
B. Addresses: abstract names, no order or arithmetic; allocation takes
   any never-used address; a block keeps its address; a word is an
   address or an immediate; machine can read/write a block and compare
   two words. Open: what word a function value is; whether the spec runs
   extern models or FFI implementations.
C. Explicit-stack evaluator with a total single step, looped by the
   `Program` driver, state carrying an erased proof tying it to the spec
   run; theorem targets (accepted ⇒ typing derivation; rejected ⇒
   positive `Fails` derivation; compile-time values match spec run;
   output run matches spec run); "never both accepted and rejected";
   spec starts at source text vs core; OCaml output: prove down to a
   modelled OCaml subset printed by a decision-free printer, vs trust
   emission; route: retrofit slc / certified kernel behind slc's front
   end / new compiler; macro-expansion fuel; spikes on mini/ first.

## Cautions

The previous agent was repeatedly caught making false assumptions. So:
before writing any claim, ask "where exactly does this come from?" If
it's DESIGN.md, quote it. If you can't find it, say "DESIGN.md does not
say". If it's about OCaml or Sleight type-checking, compile it. If it is
about what slc or mini/ does, read the code and cite lines. Prefer
"I could not determine" to a guess. Flag rough edges and contradictions
you find in DESIGN.md as questions for the owner, not as resolved.

## Output format for your file

Markdown. Start with a 2–4 line header saying it was written by an agent
overnight, is a proposal, and nothing in it is approved. Then:
1. Summary (≤ 15 lines).
2. Findings: facts established, each with its source (§/file:line/compiled test).
3. Options: for each question, 2–4 concrete options, each with a short
   design statement, pros, cons, risks, and rough cost.
4. Decisions for the owner: numbered, each a crisp question with the
   recommended answer (if any) and why, and what depends on it.
5. Rough edges / contradictions / gaps found in DESIGN.md (quoted).
6. Unverified claims: list anything you assert but could not check.
