# Round-6 review brief

You are a fresh, independent adversarial reviewer. The files under review
have already been through several review passes, recorded in sections at
their ends ("Review notes", "Second/Third/Fourth/Fifth review notes", and
"Coordinator notes"; 08–10 have had one pass). Per-file error counts per
round fell roughly 9–27, 8–22, 6–13, 4–9, 3–9: more errors very likely
remain. Earlier agents kept making false assumptions; your job is to find
what all earlier reviewers missed, AND errors introduced by later edits
(edits create new mistakes, break sentences, leave a body contradicting its
notes or a Coordinator note, or leave a note claiming a fix the body
doesn't reflect).

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
  `_build/default/bin/main.exe`. slc: `_build/release/slc`. MANUAL.md has
  the flags. Mind argument order with `--extract`/`--build` (an earlier run
  nearly overwrote a source file). Prioritise claims never re-run and
  claims changed in the latest passes.
- Logic/type-theory claims: check the reasoning step by step; flag
  overclaims and underclaims.
- Owner attributions; ASSUMPTIONS.md as owner views; proposals presented
  as decided; questions DESIGN.md already answers.
- Internal consistency, and cross-references to other files (open them).
- Prose: two-way sentences, vague nouns, Oxford commas, present tense.

Error clusters seen so far: inferences built on correct test results;
hedges drifting stronger or weaker during edits; false "DESIGN.md does not
say X"; untested claims presented as tested; condensations losing a
condition.

FIX each error in place. Append a section "## Round 6 review notes"
(numbered: what was wrong, evidence, what changed; then points you are
unsure of). Edit only your assigned files plus new small source tests under
/home/user/sleight/proposals/self-formal/proto/review6/. Scratch outputs and
binaries go in
/tmp/claude-0/-home-user-sleight/1366633a-e15e-566f-bd0e-9c4268fb4c7a/scratchpad/r6-<your-files>/,
never under proposals/. Do not commit. Reply with a ≤12-line summary:
error count per file, the most serious ones, and your view of
trustworthiness.
