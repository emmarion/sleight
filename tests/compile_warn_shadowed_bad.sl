; error: the message of `compile-warn` must be a `Settled`, non-erased `String`; `s` has type `(String)`, not the prelude's `String`
; The message must be the prelude's `String`, whatever the program has named `String` since.
; warns: tests/compile_warn_shadowed_bad.sl:5:13: warning: declaration of `String` shadows a previous binder
; warns: lib/prelude.sl:954:13: note: shadowed binder is here
(def-adts $ (String : -> Type) enum (many S : -> (String)))
(let ((many s)) (S))
(compile-warn s)
