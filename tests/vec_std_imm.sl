; needs: ../std/macro ../std/list ../std/immediate ../std/vec
; expect: (MkPair _ _ (Cons _ 4 $ Cons _ 4 $ Cons _ 4 $ Cons _ 4 $ Cons _ 8 $ Cons _ 8 $ Cons _ 8 $ Cons _ 8 $ Cons _ 16 $ Nil _) $ MkPair _ _ (MkU62 0 _) $ MkPair _ _ (MkU62 7 _) 32)
(let ((erased lt7)) (lt-trans 7 u8-modulus u62-modulus (prove-literal-lt 7 u8-modulus) u8-below-u62))

(def-fns _ $ (many caps : (erased (List (U62)) xs) (unique (Vec (U62) xs) v) (subterm many (Nat) n) ->
    (many (List (Nat)) r) (erased (List (U62)) ys) (unique (Vec (U62) ys) w))
  (let-match many n (Succ k) ((Zero) (values (Nil _) xs v)))
  (let ((erased _) (unique v2) (erased _)) (vec-push-imm _ _ v (MkU62 (Zero) u62-modulus-pos) (ImmU62)))
  (let ((many c) (unique v3)) (vec-capacity _ _ v2))
  (let ((many cs) (erased ys) (unique v4)) (notail $ caps _ v3 k))
  (values (Cons _ c cs) ys v4))

(def-fns _ $ (many go : -> (many (Pair (List (Nat)) (Pair (U62) (Pair (U62) (Nat)))) r))
  (let ((many cs) (erased _) (unique v1)) (caps _ (vec-new (U62)) 9))
  (let ((erased xs) (unique r) (unique v2)) (vec-pop _ _ v1))
  (let-match unique r (Popped _ _ _ top _) ((PopEmpty _) (MkPair _ _ cs $ MkPair _ _ (MkU62 (Zero) u62-modulus-pos) $ MkPair _ _ (MkU62 (Zero) u62-modulus-pos) 0)))
  (let ((many n) (erased l) (unique v3)) (vec-len _ _ v2))
  (let-match many n (Succ k) ((Zero) (let-match erased l (LengthNil _)) (MkPair _ _ cs $ MkPair _ _ (share top) $ MkPair _ _ (share top) 0)))
  (let ((erased x0) (erased nth)) (nth-exists _ xs n (Zero) l (LtZ k)))
  (let ((unique old) (erased _) (unique v4) (erased sp)) (vec-replace-imm _ _ v3 (Zero) (MkU62 7 lt7) x0 nth (ImmU62)))
  (let ((unique v5)) (vec-reserve-imm _ _ v4 (Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Succ $ Zero) (ImmU62)))
  (let ((many c) (unique v6)) (vec-capacity _ _ v5))
  (let ((many w)) (share v6))
  (MkPair _ _ cs $ MkPair _ _ (share old) $ MkPair _ _ (vec-get-many _ _ w (Zero) _ (setnth-nth _ _ _ _ _ sp)) c))
go
