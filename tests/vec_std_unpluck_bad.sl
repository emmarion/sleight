; needs: ../std/list ../std/vec
; error: type mismatch
; A Vec lent by vec-pluck takes back only a value at the plucked element's slot.
(def-fns _ $ (many go : -> (many (Nat) r))
  (let ((erased _) (unique v1) (erased p1)) (vec-push _ _ (vec-new (Nat)) (Succ 4)))
  (let-match erased p1 (SnocNil _ _))
  (let ((unique x) (unique lent)) (vec-pluck _ _ v1 (Zero) _ (NthHere _ _ _)))
  (let ((erased _) (unique v2) (erased _)) (vec-unpluck _ _ (Zero) (Succ 7) lent))
  (let ((many n) (erased _) (unique _)) (vec-len _ _ v2))
  n)
go
