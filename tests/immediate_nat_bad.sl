; needs: ../std/immediate
; error: type mismatch: expected `(Immediate (Nat))`, got `(Immediate (U62))`
(let ((erased (Immediate (Nat)) q)) (ImmU62))
(Zero)
