# F1. An `at` return reconstructed from an erased binder's word

Status: fixed in `fa5747a` (`lib/elab.ml` `location_var`, `self/elab.sl`
`location-var`/`at-constant`); test `tests/at_erased_word.sl`.
Severity: soundness (wrong runtime value) and crash.

## The rule

DESIGN.md section 36: an `at` return is absent from a call's physical values, and
"the elaborator supplies its word from the caller's own binder for the
argument the promise names ... which the caller still holds physically".
DESIGN.md sections 14 and 29: an erased binding is stripped before the
interpreter runs, and an erased Const stores only an existence token.

## The defect

`canon` takes a `SlotHolds` argument to its at-class representative, the
smallest id in the class, which is usually an anonymous argument temporary
or call-return binder with no runtime word. `location_var` then scanned
the scope newest-first for a "readable" class member, where readable meant
"has the word flag or is in the value environment". Every `let` binder
got the word flag whatever its multiplicity, and `elab_let` at-merged an
`erased` binder into the right-hand side's class, so an erased binder was
the newest readable member and was chosen. It has no word: the emitted
code never binds it, and in run position it is bound to a token.

## Reproducer

```scheme
; expect: 1
(def-fns _ $ many move : (unique (Nat) x) -> (unique (Nat) r at x) x)
(let (unique n) (move (Succ (Zero))))
(let (erased z) n)
(def-unique _ $ unique inner : -> (unique (Nat) r at n) n)
(let (unique r) (inner))
(share r)
```

Before the fix the interpreter died with an OCaml assertion in
`lib/value.ml`, the extracted program printed `0`, and the self-hosted
compiler printed `0`. The correct answer is `1`.

## The fix

A candidate for the word must be non-erased. One condition added in
`location_var` and in self's two candidate sources; the runtime frames
self reads hold only emitted ids and needed no change.

## Caveats

This reads section 36's "still holds physically" as requiring a non-erased word,
and restricts only which member supplies it. The other reading is that an
erased binder should not join an at-class at all, since section 36 lists "a
forwarding `let`" among the writers without qualification; under that
reading the fix moves to `elab_let`. Both give the same results on the
tests; the owner may prefer the second.
