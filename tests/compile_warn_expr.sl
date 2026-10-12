; warns: tests/compile_warn_expr.sl:2:1: warning: ab
(compile-warn (str-append "a" "b"))
(def-fns _ $ (many hypothetical : (many (String) s) -> (many (String) r))
  (compile-warn (share s))
  s)
; error: the message of `compile-warn` must be a `Settled`, non-erased `String`
