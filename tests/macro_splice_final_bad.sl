; needs: ../std/macro
; error: a body needs a final expression
; error: tests/macro_splice_final_bad.sl:5:59: note: the expansion of `nothing` here gave no forms
(def-macro (nothing _args) (Nil _))
(def-fns _ $ (many f : (many (Nat) _x) -> (many (Nat) r)) (nothing))
