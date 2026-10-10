; error: tests/compile_error_expr.sl:3:23: error: an argument
; `compile-error` stands as an expression, here an argument.
(let ((many x)) (Succ (compile-error "an argument")))
x
