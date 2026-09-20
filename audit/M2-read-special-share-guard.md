# M2. `read_special`'s share branch lacks the erased-position guard

Status: observation, cosmetic.

`Env`'s `read_special` handles a `(share f)` written at a special-form
head and refuses "share needs a unique value" when `f` is not unique,
with no regard to the position. `elab_special`'s `Sp.Share` case guards
the same check with `pos <> Erased`, since in an erased position nothing
is used and U3's degradation does not apply. So `((share f) args)` with a
many Special `f` is refused even in an erased position, while `(share f)`
as an expression there is accepted. The two should probably read the
same; nothing sound depends on it.
