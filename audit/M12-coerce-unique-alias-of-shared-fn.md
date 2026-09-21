# M12. `coerce` via the sym of a delegate proof mints a unique alias of a shared Fn

Status: observation; appears sanctioned by U3 and U7.

`(coercible-of (delegate-of d))` on a `def-unique` `d` that delegates to
an `Fn` `f`
gives `Coercible (Unique) ... d (Shared) ... f`. `coercible-sym` is
unconditional (U7), so its sym relates `f` at `(Shared)` to `d` at
`(Unique)`, and `(coerce f symp)` in a unique position uses `f` at many
and yields a `unique` binder that is `d`'s pointer. U3 explicitly lists
"the result of a `coerce` in a non-erased position whose target side is
`(Unique)`" among the ways a unique value is born, and `check_marks`
requires a delegate to pass the function's non-erased parameters straight
through, so a delegate's callee cannot have captured uniques. The alias
is therefore a unique binder of a function that, called, runs code with
no unique captures. Believed harmless; recorded because it is another
case, beside Q4, where U1's "only reference" is literally false.
