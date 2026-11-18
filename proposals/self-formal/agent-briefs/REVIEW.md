# Round-8 review brief

You are a fresh, independent adversarial reviewer. The files under review
have already been through several review passes, recorded in sections at
their ends ("Review notes", "Second" to "Fifth review notes", "Round 6
review notes", "Round 7 review notes", and "Coordinator notes" and "Round
7 coordinator notes"). Per-file error counts per round fell roughly 9–27,
8–22, 6–13, 4–9, 3–9, then 3–14 in round 6 and 4–13 in round 7, which
also added new results: more errors very likely remain, and they cluster
in text written or rewritten most recently. Your job is to find what all
earlier reviewers missed, AND errors introduced by later edits (edits
create new mistakes, break sentences, leave a body contradicting its notes
or a coordinator note, or leave a note claiming a fix the body doesn't
reflect). Check every change that the round-7 notes and coordinator notes
list first, then the rest.

Before anything: read the original brief
proposals/self-formal/agent-briefs/BRIEF.md
(its "Owner decisions" list is the ONLY source of owner attributions, and
those are an earlier session's paraphrases), then CLAUDE.md, then ALL of
/home/user/sleight/DESIGN.md, every section, in chunks. No skimming. Read
SOUNDNESS.md too if your files cite it.

For every claim, ask "where exactly does this come from?":
- DESIGN.md claims: find and quote the text; check section numbers; for
  "DESIGN.md does not say X", grep DESIGN.md to confirm.
- Code claims (file:line): open the lines.
- Accept/refuse/output/timing claims: re-run them. Reference:
  `_build/default/bin/main.exe`. slc: `_build/release/slc`, built from the
  same compiler sources as `origin/main`. MANUAL.md has the flags. Mind
  argument order with `--extract`/`--build` (an earlier run nearly
  overwrote a source file). Prioritise claims never re-run and claims
  changed in the latest passes. Background jobs may load the machine:
  before re-running a timing claim, check `uptime`, and if the one-minute
  load average is above 1.5, do not re-run timings; say they were not
  re-run.
- Logic/type-theory claims: check the reasoning step by step; flag
  overclaims and underclaims.
- Owner attributions; ASSUMPTIONS.md as owner views; proposals presented
  as decided; questions DESIGN.md already answers.
- Internal consistency, and cross-references to other files (open them).
- Prose: two-way sentences, vague nouns, Oxford commas, present tense.

Error clusters seen so far: inferences built on correct test results;
hedges drifting stronger or weaker during edits; false "DESIGN.md does not
say X"; untested claims presented as tested; condensations losing a
condition; general "cannot" or "only" claims drawn from one refusal test;
counts of implementations or modes that are off; run-to-run counts given
as fixed.

FIX each error in place. Append a section "## Round 8 review notes"
(numbered: what was wrong, evidence, what changed; then points you are
unsure of). Edit only your assigned files plus new small source tests under
/home/user/sleight/proposals/self-formal/proto/review8/, named with your
files' numbers as a prefix. Scratch outputs and binaries go in
/tmp/claude-0/-home-user-sleight/dca6105d-73d0-5c03-b5b8-1c0e2e358cac/scratchpad/r8-<your-files>/,
never under proposals/, and never anywhere else (no stray files at `/` or
in the repository root; check your redirections). Other agents work in the
same checkout at the same time: do not commit, and run no git command that
changes state (checkout, reset, stash, restore, add). Install nothing and
write nothing outside your assigned files, `proto/review8/`, and your
scratch directory: no `make install`, `opam`, `ocamlfind install`, `apt`,
or configure scripts. Reply with a ≤12-line summary: error count per file,
the most serious ones, and your view of trustworthiness.
