; needs: ../std/macro ../std/list ../std/immediate ../std/vec
; expect: (MkPair _ _ 10 21)
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))

(def-fns _ $ (many bump : (unique (Box) b) -> (unique (Box) c at b))
  (let-match unique b (MkBox n u))
  (u (Succ n)))

(def-fns _ $ (many read : (erased (List (Box)) xs) (many (Vec (Box) xs) v) (many (Nat) i) (erased (Box) x)
    (erased (Nth (Box) xs i x) nth) -> (many (Nat) n))
  (let ((many b)) (vec-get-many _ _ v i _ nth))
  (let-match many b (MkBox n))
  n)

(def-fns _ $ (many go : -> (many (Pair (Nat) (Nat)) r))
  (let ((erased _) (unique v1) (erased p1)) (vec-push _ _ (vec-new (Box)) (MkBox 10)))
  (let-match erased p1 (SnocNil _ _))
  (let ((erased _) (unique v2) (erased p2)) (vec-push _ _ v1 (MkBox 20)))
  (let-match erased p2 (SnocCons _ _ _ _ _ p3))
  (let-match erased p3 (SnocNil _ _))
  (let ((unique b) (unique lent)) (vec-pluck _ _ v2 (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (let ((unique b2)) (bump b))
  (let ((erased _) (unique v3) (erased s)) (vec-unpluck _ _ (Succ (Zero)) b2 lent))
  (let-match erased s (SetThere _ _ _ _ _ _ s1))
  (let-match erased s1 (SetHere _ _ _ _))
  (let ((many w)) (share v3))
  (MkPair _ _ (read _ w (Zero) _ (NthHere _ _ _)) (read _ w (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _)))))
go
