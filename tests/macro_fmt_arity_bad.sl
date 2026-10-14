; needs: ../std/macro macro_fmt_lib
; error: fmt: wrong number of arguments
(def-fns _ $ (many show : (many (Nat) x) -> (many (String) s))
  ((fmt "~n and ~n") x))
