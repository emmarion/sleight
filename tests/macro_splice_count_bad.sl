; needs: ../std/macro
; error: `two` expects 2 arguments, got 1
; error: tests/macro_splice_count_bad.sl:6:65: note: the expansion of `nothing` here gave no forms
(def-macro (nothing _args) (Nil _))
(def-fns _ $ (many two : (many (Nat) a) (many (Nat) _b) -> (many (Nat) r)) a)
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) r)) (two x (nothing)))
