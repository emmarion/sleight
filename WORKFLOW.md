# Vetted mode

This workflow applies only in vetted mode, which the owner starts with
"start vetted mode" and ends with "end vetted mode" (CLAUDE.md rule
21). At other times it does not apply.

1. **Every message is vetted.** No message about the design goes to the
   owner until a reviewer agent has approved it as free of errors.
   Short status notes are exempt. When the reviewer finds errors that
   the session agrees are errors, the session fixes them, and the
   reviewer approves the fixed message again before it is sent. The
   approved text is sent word for word, with a short note of any
   trivial points the reviewer raised but did not count as errors.
2. **Design before wording.** A decision is first agreed as a short
   rule, with no DESIGN.md prose. DESIGN.md wording is then drafted
   from the agreed rules, one section at a time, reviewed, and shown to
   the owner in the form CLAUDE.md rule 12 asks for.
3. **Check against DECISIONS.md.** Before proposing anything, check it
   against DECISIONS.md, so that a recommendation never contradicts an
   earlier decision, and drop any question that a decision already
   answers. Record each new decision there as soon as the owner makes
   it, and remove from OPEN.md any question it answers.
4. **What the reviewer is told.** The reviewer reads DESIGN.md,
   DECISIONS.md and OPEN.md in full, then the draft. It checks for:
   - claims about what DESIGN.md says that the file does not bear out;
   - questions that are not genuinely open;
   - proposals that are unsound or contradict a decision;
   - decisions recorded unfaithfully, or proposals presented as
     decided;
   - sentences that do not parse or read two ways, and vague nouns.

   It replies "APPROVED", or with a numbered list of errors, each
   quoting the text and giving a fix. The same reviewer is resumed for
   each round, so it can check the fixes against its earlier findings.
