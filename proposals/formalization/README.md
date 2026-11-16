# Formalizing Sleight in Sleight: proposals

A Claude session wrote everything under this directory overnight, at
the owner's request, as material for decisions. Nothing here is
approved. DESIGN.md, DECISIONS.md, OPEN.md, ASSUMPTIONS.md, and BUGS.md
are unchanged. A claim in these files that a quoted line of DESIGN.md,
a listed command, or a checked spike does not bear out is a mistake in
these files.

## Where to start

`00-decisions.md` is the one file to read first: twelve decisions,
each with what bears on it, the options, and a recommendation.

| File | What it holds |
|---|---|
| `00-decisions.md` | The decisions, D1 to D12 |
| `01-theorems.md` | What can be proved and how it would be stated; the theorems T1 to T7 |
| `02-spec-run.md` | The specification's run: a heap machine, evaluation order, addresses, externs |
| `03-spec-static.md` | The static specification, from source text to a verdict |
| `04-fuel.md` | Fuel: what has to give, and the designs that avoid it |
| `05-compiler-route.md` | Retrofit slc or write a new compiler; where the output proof stops |
| `06-design-gaps.md` | Nineteen places where DESIGN.md is silent or gives a choice |
| `07-prior-art.md` | What comparable projects did |
| `08-spikes.md` | The prototypes: what each shows and how to run it |
| `09-plan.md` | A staged plan |

## How the claims were checked

- Sub-agents did the research and built most of the prototypes. Their
  reports are under `evidence/` as they wrote them, each claim tagged
  as a quotation, a command that was run, code that was read, an
  inference, or an unknown. The numbered files are this session's
  summaries of them. A report is an agent's word, not the owner's, and
  not DESIGN.md's.
- Reviewer agents, briefed to look for false assumptions, read
  DESIGN.md in full and check the numbered files against it, against
  the handoff, and by re-running commands. "Review status" below says
  how far each file has got.
- The prototypes are under `spikes/`. `spikes/check.sh` re-runs all of
  them with both implementations:

  ```sh
  dune build && self/release.sh
  proposals/formalization/spikes/check.sh
  ```

## Words used throughout

- **The handoff**: the previous session's summary that the owner
  pasted. It is second-hand; these files quote it and say so.
- **The reference**: the OCaml implementation in `lib/` and `bin/`.
  **slc**: the compiler written in Sleight, in `self/`.
- **Accepted, rejected, verdict**: these files' words. DESIGN.md does
  not define a program's being accepted (06, G10).

## Review status

| File | Status |
|---|---|
| `01-theorems.md` | One round: 13 errors found, all fixed; the fixes not yet re-checked |
| `07-prior-art.md` | One round: 9 errors found, all fixed; the fixes not yet re-checked |
| The other numbered files | Not yet reviewed |
