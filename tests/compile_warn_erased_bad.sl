; error: the message of `compile-warn` must be a `Settled`, non-erased `String`; `s` is erased
(let ((erased s)) "erased")
(compile-warn s)
