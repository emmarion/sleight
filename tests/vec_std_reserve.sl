; needs: ../std/macro ../std/list ../std/vec
; expect: (Cons _ 4 $ Cons _ 6 $ Cons _ 10 $ Cons _ 8 $ Cons _ 8 $ Cons _ 4 $ Nil _)
(def-fns _ $ (many fill : (erased (List (Nat)) xs) (unique (Vec (Nat) xs) v) (subterm many (Nat) n) ->
    (erased (List (Nat)) ys) (unique (Vec (Nat) ys) w))
  (let-match many n (Succ k) ((Zero) (values xs v)))
  (let ((erased _) (unique v2) (erased _)) (vec-push _ _ v (Succ k)))
  (tail $ fill _ v2 k))

(def-fns _ $ (many cap-after : (erased (List (Nat)) xs) (unique (Vec (Nat) xs) v) -> (many (Nat) c))
  (let ((many c) (unique _)) (vec-capacity _ _ v))
  c)

(def-fns _ $ (many caps : -> (many (List (Nat)) r))
  (let ((erased _) (unique a)) (fill _ (vec-with-capacity (Nat) 1) 2))
  (let ((erased _) (unique b)) (fill _ (vec-with-capacity (Nat) 3) 4))
  (let ((unique c)) (vec-reserve _ _ (vec-new (Nat)) 10))
  (let ((erased _) (unique d0)) (fill _ (vec-new (Nat)) 4))
  (let ((unique d)) (vec-reserve _ _ d0 1))
  (let ((many cd) (unique d2)) (vec-capacity _ _ d))
  (let ((unique e)) (vec-reserve _ _ d2 3))
  (let ((many n) (erased _) (unique e2)) (vec-len _ _ e))
  (Cons _ (cap-after _ a) $ Cons _ (cap-after _ b) $ Cons _ (cap-after _ c) $ Cons _ cd $
    Cons _ (cap-after _ e2) $ Cons _ n $ Nil _))
caps
