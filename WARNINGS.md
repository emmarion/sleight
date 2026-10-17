# Warnings

The warnings the compilers emit on their own: the reference
interpreter in `lib/` and slc in `self/` emit the same set, with the
same text. The descriptions here are a session's reading of the code.
The code that emits each warning and its `; warns:` tests are the
authority. A warning is written as `path:line:col: warning: text`,
followed by any notes (README.md); one about a form a macro placed at
`NoPos` carries no location, not even a file: `warning: text`. It goes to standard error and does
not stop elaboration. `--warnings-as-errors` makes a run that warns
fail.

The warnings a program asks for, through `;! warn`, `;! suppress` and
`compile-warn`, are a language feature and are specified in DESIGN.md
section 4. They are listed in item 9 only so that this file names every
warning text.

## 1. Shadowing a previous binder

`declaration of NAME shadows a previous binder`, with a note at the
shadowed binder. A second note, `using `_` here instead would be
equivalent`, is added when the new binder has the same canonical term
as the old one and the same slot, or is erased. The warning is given
for a binder written in the source that hides a name that a source
binder introduced earlier.
`lib/env.ml` (`report_shadows`), `self/core.sl`.
Tests: `tests/shadow_warn.sl`, `tests/shadow_covered_warn.sl`.

## 2. Shadowing a built-in

`declaration of NAME shadows a built-in`. A binder written in the
source hides a name that the built-ins minted (§42): a special form,
an annotation token or an opaque type.
`lib/env.ml` (`bind`), `self/core.sl`.
Tests: `tests/shadow_builtin_warn.sl`, `tests/universe_shadowed_bad.sl`.

## 3. Unnecessary decrease annotation

``unnecessary `(predates _)`; drop it`` or
``unnecessary `(subterm _)`; drop it``. A call inside a function body
carries a written decrease annotation (§19) that the elaborator would
have inferred on its own from a bare call (§48).
`lib/elab.ml` (`elab_call`), `self/elab.sl`.
Tests: `tests/vec_map.sl`, `tests/trans.sl`.

## 4. Unmarked same-level call

``same-level call to F is unmarked; mark it `tail` `` or
``... mark it `notail` ``. A call to a function of the caller's own
level carries neither mark (§19). The suggested mark is the one the
call's position would satisfy.
`lib/elab.ml` (`check_marks`), `self/elab.sl`.
Test: `tests/same_level_branch_callee.sl`.

## 5. Lopsided `match`

``lopsided `match`; flatten it with a `let-match` on C``. A `match` in
final position outside run position has exactly one branch whose body
is deep, meaning it has statements or is itself a `match` or
`cell-match`, and that branch is a reachable constructor branch `C`.
The suggested rewrite is a `let-match` with branches (§52).
`lib/elab.ml` (`elab_match`), `self/elab.sl`.
Tests: `tests/at_match.sl`, `tests/vec_append.sl`.

## 6. A runtime `absurd`

``a non-erased `match` with no non-absurd branch compiles to a runtime
`absurd`; mark the enclosing branch or function `absurd` instead``. A
non-erased match that is not an at-match has no real branch and no
`else`, in code that is not itself erased.
`lib/elab.ml` (`elab_match`), `self/elab.sl`.
Tests: `tests/match_no_branches_warn.sl`, `tests/else_phantom_only.sl`.

## 7. Phantom constructor with a non-erased field

``phantom constructor `C` has a non-erased field``. A `def-adts`
constructor marked `erased` (§21) declares a field `many` or `unique`.
`lib/elab.ml` (`elab_def_adts`), `self/elab.sl`.
Tests: `tests/phantom_warn.sl`, `tests/wrap_phantom_bad.sl`.

## 8. Indentation

Indentation is read as a claim about paren nesting, and the claim is
checked before the file is parsed, so a file that is then refused is
still reported on. `$` is not counted as nesting. Each of the
comparison warnings carries a note at the line it is compared with,
and a file that gets any of these warnings also gets a note naming
`bin/shape`, unless `--no-shape-note` is given. `bin/indent.exe` runs
this check alone. `lib/indent.ml`, `self/reader.sl`.

| text | when | test |
|---|---|---|
| `indentation uses a tab, not spaces only` | a line's indentation holds a tab | `tests/indent_tab_warn.sl` |
| `same indentation (I) as the previous checked line but nesting is N, expected M (...)` | two lines at one indentation start at different nestings | `tests/indent_unclosed_bad.sl` |
| `indentation increased (I -> J) but nesting did not increase (M -> N)` | a more indented line is not more nested | `tests/indent_warn.sl` |
| `dedented past indentation I (nesting M), but this line's nesting is N (expected less than M)` | a less indented line is not less nested than a level it closes | none |
| `dedented to indentation I, but an enclosing line at indentation J has nesting M, not less than this line's N` | a less indented line is not more nested than a level still open | none |
| `dedented back to indentation I, matching an earlier line, but nesting is M there vs N here` | a less indented line returns to an open level at another nesting | none |
| ``a `)` here closes more than is open (surplus `)`)`` | the first `)` with nothing open | `tests/indent_surplus_bad.sl` |
| `this form is never closed`, then `and this one` notes | forms still open at the end of the file, innermost first | `tests/indent_unclosed_bad.sl` |

## 9. The warnings a program asks for

Specified in DESIGN.md section 4.

- `application of C: MSG`, `call of F: MSG`, `match on T: MSG`, with
  a note at the `;! warn` pragma. `lib/elab.ml` (`warn_use`),
  `self/elab.sl`. Tests: `tests/warn_pragma.sl`,
  `tests/warn_pragma_function.sl`, `tests/warn_pragma_at.sl`.
- ``;! suppress warn` for NAME silenced nothing``. `lib/elab.ml` (`run_toplevel`),
  `self/elab.sl`. Test: `tests/suppress_warn.sl`.
- The text of a `compile-warn` (§4). Test: `tests/compile_warn.sl`.

## 10. Unused binder

`unused NAME; delete it`, ``…; delete its `let` ``,
``…; write `_` in its place`` or ``…; rename it `_NAME` ``, and
``NAME is referenced only in erased positions; declare it `erased` ``,
for a parameter with ``, or rename it `_NAME` `` added. Off unless
`--warn-unused` is given; the prelude is checked too, and a test opts
in with `; warn-unused: yes`. slc is built under it, and `dune test`
checks the prelude and the files tests need from outside `tests/` under
it (README.md). Not checked: top-level binders, names
starting with `_`, gensyms (DESIGN.md section 63), the type and value
constructors a `def-adts` defines, and names in types, returns and
match annotations. See
OPEN.md 30 and 31.
`lib/elab.ml` (`report_unused`), `self/elab.sl`. Tests:
`tests/unused_warn.sl`, `tests/unused_params_warn.sl`.
