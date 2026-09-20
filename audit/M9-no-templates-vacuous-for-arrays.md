# M9. `--no-templates` is a vacuous check for arrays

Status: observation about validation coverage.

`lib/ffi_templates.txt` has templates for `Nat`, `Half` and `String`
only, so an `Array` build or match extracts through `con_Array` and
`des_Array` whether templates are on or off, and the two extraction modes
emit the same code for it. ASSUMPTIONS 167's "non-template views" clause
is therefore true but not an independent check for arrays. The real
tier-1 check (UNIQUE.md U14) for arrays is `--no-extern`, which the test
runner and the audit both ran on every array program; all agreed. Worth
knowing before reading a "--no-templates passes" claim as evidence about
arrays.
