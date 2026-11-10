; A tainted entry has no value for a message to be read from, as an erased one has none.
(let ((many a)) (sorry (((String) x))))
(compile-warn a)
; error: tests/sorry_message_bad.sl:3:15: error: the message of `compile-warn` must be a `Settled`, non-erased `String`; `a` relies on `sorry`
