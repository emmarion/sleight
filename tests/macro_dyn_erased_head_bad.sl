; needs: macro_lib
; error: `em` is an erased macro, expanded only where its head is constant-known and non-erased
(def-fns _ $ (many f : (erased (Macro) em) -> (many (Nat) c))
  (em nat-add 1 2))
