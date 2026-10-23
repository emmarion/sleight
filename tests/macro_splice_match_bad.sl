; needs: ../std/macro
; error: this `match` is missing a branch
; error: tests/macro_splice_match_bad.sl:5:74: note: the expansion of `pass` here gave 1 form
(def-macro (pass args) args)
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) r)) (match many x _ (pass ((Zero) x))))
