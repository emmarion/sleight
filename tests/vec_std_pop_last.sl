; needs: ../std/macro ../std/list ../std/immediate ../std/vec
; expect: (MkPair _ _ 30 $ MkPair _ _ 20 1)
(def-fns _ $ (many go : -> (many (Pair (Nat) (Pair (Nat) (Nat))) r))
  (let ((erased _) (unique v1) (erased _)) (vec-push _ _ (vec-new (Nat)) (Succ 9)))
  (let ((erased _) (unique v2) (erased s2)) (vec-push _ _ v1 (Succ 19)))
  (let ((erased _) (unique v3) (erased s3)) (vec-push _ _ v2 (Succ 29)))
  (let ((unique c) (unique v4)) (vec-pop-last _ _ _ _ s3 v3))
  (let ((unique b) (unique v5)) (vec-pop-last _ _ _ _ s2 v4))
  (let ((many n) (erased _) (unique _)) (vec-len _ _ v5))
  (MkPair _ _ (share c) $ MkPair _ _ (share b) n))
go
