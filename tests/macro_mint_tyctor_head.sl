; needs: ../std/macro macro_mint_tyctor_lib
; expect: 7
(def-fns _ $ (many f : (erased (opaque-list (Nat)) x) -> (many (Nat) r))
  7)
(def-fns _ $ (many g : -> (many (Nat) r))
  7)
(g)
