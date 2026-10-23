; needs: ../std/macro
(def-fns _ $ (erased e : (many (Nat) x) -> (many (Nat) r)) x)
(def-macro (m _args) (qq (e (Zero))))
(m)
; error: tests/macro_handle_erased_fn_bad.sl:3:26: error: erased function `e` called in a non-erased position
; error: tests/macro_handle_erased_fn_bad.sl:2:14: note: `e` is declared `erased` here
