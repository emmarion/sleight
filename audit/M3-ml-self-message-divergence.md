# M3. ML and self give different messages for some refusals

Status: observation. Both implementations refuse; only the wording
differs, which matters for shared `; error:` directives that
`self/bootstrap.sh` checks against both.

Seen in the audit:

- a `unique` pattern missing its cell binder on a constructor with fields:
  reference "B has 1 fields", self "unique constructor pattern needs
  fields and a cell binder"; on a nullary constructor both contain "cell
  binder" but differ otherwise;
- `(absurd (D _ u))`, an absurd branch written with a pattern but no
  body: reference "branch D is refuted; write (absurd D)", self
  "malformed branch".

`self/README.md` says slc's error messages are the reference's; these are
the exceptions found. The audit's tests use directive text both emit.
