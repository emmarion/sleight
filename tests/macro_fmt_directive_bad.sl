; needs: ../std/macro macro_fmt_lib
; error: fmt: a `~` must be followed by `n`, `s` or `~`
(def-fns _ $ (many show : (many (Nat) x) -> (many (String) s))
  ((fmt "~q") x))
