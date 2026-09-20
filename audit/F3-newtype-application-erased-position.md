# F3. A newtype application in an erased position refused as a non-variable location

Status: fixed in `fa5747a` (`lib/elab.ml` `elab_form`'s `ValCtor` case,
`self/elab.sl` the matching `place` line); test
`tests/at_erased_newtype.sl`. Severity: rejects a valid program, with an
error carrying no source location.

## The rule

UNIQUE.md U8: the at-database is a partition of scope entries, and one of
its writers is "a newtype constructor application (the value with its
non-erased argument, U9)". DESIGN.md section 20: an erased position's value
is never computed, so nothing there has a word. Nothing forbids writing a
newtype application in an erased position.

## The defect

The `ValCtor` case computed the application's location from the argument
term. In a non-erased position every non-erased argument is first bound
to an anonymous temporary, so the term is a variable. In an erased
position that binding is skipped, so the term was an application such as
`(Zero)`, and `at_merge` raised its "locations must be variables"
contradiction, which surfaces without a line number. This was the only
producer of a non-variable location in the elaborator. Self also merged
unconditionally for an erased match scrutinee and so refused one shape
the reference accepted.

## Reproducer

```scheme
; expect: 0
(def-adts $ Box : -> Type enum newtype (many B : (many (Nat) n) -> (Box)))
(let (erased z) (B (Zero)))
(let (erased p) (coercible-sym (coercible-wrap (Shared) B (Zero))))
(let (erased w) (coerce (B (Zero)) p))
(def-fns _ $ erased probe : -> (erased (Nat) r)
  (match erased (B (Zero)) (((Nat) q)) ((B m) m)))
(Zero)
```

## The fix

Compute the location only in a non-erased position. This cannot weaken a
check: `check_results` verifies an `at` promise only when the environment
is not usage-erased, and an erased position always sets that flag.

## Caveats

None seen.
