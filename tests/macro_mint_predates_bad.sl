; needs: ../std/macro macro_lib macro_mint_lib
; error: is a constant a macro minted, which has no introduction order
(def-lvl L)
(let ((erased p)) (prove-predates (mint-list 3) L))
