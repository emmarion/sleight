; error: the message of `compile-warn` must be a `Const`, non-erased `String`; `s` is erased
(let ((erased s)) "erased")
(compile-warn s)
