; needs: ../std/macro
; error: the enclosing `let` expects 3 values, got 2
; error: tests/macro_splice_let_bad.sl:6:18: note: the expansion of `pass` here gave 2 forms
(def-macro (pass args) args)
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) r))
  (let ((many a) (pass (many b) (many c))) (values x x))
  a)
