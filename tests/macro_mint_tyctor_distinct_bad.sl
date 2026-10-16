; needs: ../std/macro macro_mint_tyctor_lib
; error: type mismatch
(def-fns _ $ (many f : (many (opaque-list (Nat)) x) -> (many (opaque-list (Nat)) y))
  x)
