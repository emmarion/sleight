# F2. Self `let-match many` hands a unique-labelled field out at unique

Status: fixed in `fa5747a` (`self/elab.sl`, one line); tests
`tests/let_match_many_unique_field_bad.sl`,
`tests/let_match_many_alias_bad.sl`. Severity: soundness, in the
self-hosted compiler only.

## The rule

UNIQUE.md U4's destructuring table: a unique-labelled field under a
`many` scrutinee comes out `many`, "a shared cell shares everything it
owns, with no per-field bookkeeping". U4 says this governs `match`,
`let-match` and `comptime-match` alike.

## The defect

`self/elab.sl`'s `elab-let-match` computed its field multiplicities with
`under-list`, the identity on a non-erased position, instead of
`field-mults`, which demotes `Once` to `Many` under a `many` position.
Self's ordinary `match` and its `comptime-match` used `field-mults`
correctly; only `let-match` was wrong. The reference `lib/elab.ml` uses
`field_under` in all three and was correct, so the two implementations
disagreed.

## Reproducer

```scheme
; error: used at unique
(def-adts $ Cnt : -> Type enum (many C : (many (Nat) v) -> (Cnt)))
(def-adts $ Box : -> Type enum (many B : (unique (Cnt) c) -> (Box)))
(let (unique x) (B (C (Zero))))
(let (many y) (share x))
(let (many z) (share x))
(let-match many y (B n))
(let-match unique n (C v u))
(let (unique n2) (u (Succ (Succ (Succ (Zero))))))
(let-match many z (B m))
(let-match many (share m) (C w))
w
```

The reference refuses at line 8. Before the fix `slc` accepted this and
printed `3`: the block reached through the `many` alias `z` had been
overwritten in place through a `unique` alias the spec says cannot exist.
Under U14's tier 1, where every invocation allocates, the same program
would print `0`, so it also broke the erasure invariant.

## The fix

`under-list` to `field-mults` at that one site. A sweep of about a
hundred existing uniqueness tests through the rebuilt `slc` showed no
other accept/refuse change.

## Caveats

None seen. The bootstrap would not have caught this on its own, since no
existing test exercised a `let-match many` over a unique-labelled field.
