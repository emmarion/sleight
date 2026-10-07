# M1. `matchable-of` records no use of the Matchable entry

Status: observation, not acted on. Latent.

Every other non-erased occurrence of a variable goes through `Env.use`:
the atom case, constructor heads, calls, cell invocations, scrutinees and
their Matchables, `comptime-match`, `share`, special-form heads,
`coerce`'s source, `open-adt`, cell items. `matchable-of` returns the
opened entry directly (`lib/elab.ml`, `Sp.MatchableOf`) without recording
a use. A `unique` Matchable would therefore be handed out twice as two
live unique binders.

No route mints one: a Matchable enters scope `many` (DESIGN.md section 24,
`witness ~mult:Many`), `(let (unique m) (matchable-of T))` is refused as a
many value used at unique, and a unique-labelled field, a unique
parameter or a `(Unique)` coerce were each blocked earlier. So this is a
gap in uniformity rather than a live hole. Adding `use env l m x` there,
with the self mirror, would close it in the style of the surrounding
code.
