; needs: ../std/macro macro_lib macro_mint_lib
; error: type mismatch
(let ((erased (Eq (List (Nat)) (mint-list 1) (mint-list 1)) e)) (Refl _ _))
