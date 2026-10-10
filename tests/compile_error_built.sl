; error: tests/compile_error_built.sl:7:3: error: never called
; `compile-error` fires in the body of an erased function that is never called, with a message built by hand.

;! suppress warn SCons
(let ((many message)) (str-append "never " $ SCons #\c $ SCons #\a $ SCons #\l $ SCons #\l $ SCons #\e $ SCons #\d $ SNil))
(def-fns _ $ (erased g : (many (Nat) n) -> (many (Nat) m))
  (compile-error message))
3
