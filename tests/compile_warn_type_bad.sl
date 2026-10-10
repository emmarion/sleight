; error: the message of `compile-warn` must be a `Const`, non-erased `String`; `n` has type `(Nat)`, not the prelude's `String`
(let ((many n)) 3)
(compile-warn n)
