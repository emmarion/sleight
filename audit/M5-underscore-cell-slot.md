# M5. `_` not accepted as a `Cell` slot in a type

Status: observation, out of scope by DESIGN.md section 50.

`(unique (Cell B _) u)` in a signature is refused with "type mismatch:
expected (Slot), got (Univ)": every `_` in the type elaborator is minted
at type `Type`, and the `Cell` former then checks each slot against
`(Slot)`. DESIGN.md section 50 scopes `_` to "an argument to a type constructor, a
value constructor or a function (type formers perhaps later)", so this
matches the sugar as recorded. Section 38 already offers the intended spelling,
an abstract `(erased (Slot) s)` parameter. Only a question if the owner
wants `_` extended to type formers.
