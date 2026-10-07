# M8. `Ffi.claim_fn` never checks an implementation's result count

Status: observation, nit.

`Ffi.claim_fn` validates the number of non-erased parameters an extern's
signature declares against the table's `takes`, but never the length of
the list the implementation returns, which must be the signature's
physical results with `at` returns shed. With a fixed table this is
harmless, all four array externs agreeing (swap returns `[old]`, pluck
`[v]`, place `[]`, new `[array]`), but it is the half of DESIGN.md
section 42's "cannot be registered without its arity" that the code does
not enforce, and a mismatch would surface as an arity error at runtime
rather than at the claim.
