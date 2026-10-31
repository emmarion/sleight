; needs: ../std/macro ../std/list ../std/vec
; expect: (MkPair _ _ (MkPair _ _ (Cons _ 4 $ Cons _ 4 $ Cons _ 4 $ Cons _ 4 $ Cons _ 8 $ Cons _ 8 $ Cons _ 8 $ Cons _ 8 $ Cons _ 16 $ Cons _ 16 $ Cons _ 16 $ Cons _ 16 $ Cons _ 16 $ Cons _ 16 $ Cons _ 16 $ Cons _ 16 $ Cons _ 32 $ Nil _) $ Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 4 $ Cons _ 5 $ Cons _ 6 $ Cons _ 7 $ Cons _ 8 $ Cons _ 9 $ Cons _ 10 $ Nil _) 10)
(def-fns _ $ (many fill : (erased (List (Nat)) xs) (unique (Vec (Nat) xs) v) (subterm many (Nat) n) ->
    (erased (List (Nat)) ys) (unique (Vec (Nat) ys) w))
  (let-match many n (Succ k) ((Zero) (values xs v)))
  (let ((erased _) (unique v2) (erased _)) (vec-push _ _ v (Succ k)))
  (tail $ fill _ v2 k))

(def-fns _ $ (many caps : (erased (List (Nat)) xs) (unique (Vec (Nat) xs) v) (subterm many (Nat) n) ->
    (many (List (Nat)) r))
  (let-match many n (Succ k) ((Zero) (Nil _)))
  (let ((erased _) (unique v2) (erased _)) (vec-push _ _ v (Succ k)))
  (let ((many c) (unique v3)) (vec-capacity _ _ v2))
  (Cons _ c $ notail $ caps _ v3 k))

(def-fns _ $ (many drain : (erased (List (Nat)) xs) (unique (Vec (Nat) xs) v) (subterm many (Nat) n) ->
    (many (List (Nat)) r))
  (let-match many n (Succ k) ((Zero) (Nil _)))
  (let ((erased _) (unique r) (unique v2)) (vec-pop _ _ v))
  (match unique r _
    ((PopEmpty _) (Nil _))
    ((Popped _ _ _ x _) (Cons _ (share x) $ notail $ drain _ v2 k))))

(def-fns _ $ (many go : -> (many (Pair (Pair (List (Nat)) (List (Nat))) (Nat)) r))
  (let ((unique v0)) (vec-new (Nat)))
  (let ((erased _) (unique v1)) (fill _ v0 10))
  (let ((many n) (erased _) (unique v2)) (vec-len _ _ v1))
  (MkPair _ _ (MkPair _ _ (caps _ (vec-new (Nat)) 17) (drain _ v2 12)) n))
(go)
