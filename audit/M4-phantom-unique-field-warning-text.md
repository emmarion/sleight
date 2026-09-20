# M4. The phantom-with-unique-field warning text says "many field"

Status: observation, wording only.

UNIQUE.md U4: "section 12's warning for a phantom constructor with a
`many` field covers a `unique` one too." The warning does fire for a
`unique` field, `lib/elab.ml` testing `e.mult <> Erased`, but its text
still reads "phantom constructor G has a many field":

```scheme
; warns: warning (line 3): phantom constructor G has a many field
(def-adts $ T : -> Type enum (many L : -> (T)) (erased G : (unique (Nat) n) -> (T)))
```

Both implementations warn identically. Behaviour is right; the wording,
"a non-erased field" say, is the owner's to choose.
