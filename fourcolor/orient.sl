(let ((many i4)) (Succ i3))
(let ((many i6)) (Succ $ Succ i4))
(let ((many i8)) (Succ $ Succ i6))

(def-adts $ (PtAt : ((List (Nat)) env) ((Nat) i) ((Point) p) -> Type)
  enum
  (many MkPtAt : (erased (List (Nat)) env) (erased (Nat) i x y) (erased (Nth (Nat) env i x) px) (erased (Nth (Nat) env (Succ i) y) py)
     -> (PtAt env i (MkPoint x y))))

(def-fns _ $ (erased pt-at : (erased (Nat) x y) (erased (List (Nat)) env) -> (erased (PtAt (Cons (Nat) x (Cons (Nat) y env)) i0 (MkPoint x y)) a))
  (MkPtAt _ i0 x y (NthHere _ x _) (NthThere _ x _ i0 y (NthHere _ y env))))

(def-fns _ $ (erased pt-skip : (erased (List (Nat)) env) (erased (Nat) i) (erased (Point) p) (erased (Nat) x y) (erased (PtAt env i p) a) ->
    (erased (PtAt (Cons (Nat) x (Cons (Nat) y env)) (Succ (Succ i)) p) b))
  (let-match erased a (MkPtAt _ _ u v nu nv))
  (MkPtAt _ (Succ (Succ i)) u v (NthThere _ x _ _ u (NthThere _ y _ _ u nu)) (NthThere _ x _ _ v (NthThere _ y _ _ v nv))))

(def-fns _ $ (erased pts5 : (erased (Point) p q r s t) -> (erased (List (Nat)) env)
    (erased (PtAt env i0 p) a) (erased (PtAt env i2 q) b) (erased (PtAt env i4 r) c) (erased (PtAt env i6 s) d) (erased (PtAt env i8 t) e))
  (let-match erased p (MkPoint px py))
  (let-match erased q (MkPoint qx qy))
  (let-match erased r (MkPoint rx ry))
  (let-match erased s (MkPoint sx sy))
  (let-match erased t (MkPoint tx ty))
  (let ((erased e4)) (Cons _ tx $ Cons _ ty $ Nil (Nat)))
  (let ((erased e3)) (Cons _ sx $ Cons _ sy e4))
  (let ((erased e2)) (Cons _ rx $ Cons _ ry e3))
  (let ((erased e1)) (Cons _ qx $ Cons _ qy e2))
  (values (Cons _ px $ Cons _ py e1) (pt-at px py e1) (pt-skip _ _ _ px py $ pt-at qx qy e2)
    (pt-skip _ _ _ px py $ pt-skip _ _ _ qx qy $ pt-at rx ry e3)
    (pt-skip _ _ _ px py $ pt-skip _ _ _ qx qy $ pt-skip _ _ _ rx ry $ pt-at sx sy e4)
    (pt-skip _ _ _ px py $ pt-skip _ _ _ qx qy $ pt-skip _ _ _ rx ry $ pt-skip _ _ _ sx sy $ pt-at tx ty (Nil (Nat)))))

(def-macro (shoe args)
  (let-match many args (Cons _ i r1) (else (qq (compile-error "`shoe` takes the indices of three points"))))
  (let-match many r1 (Cons _ j r2) (else (qq (compile-error "`shoe` takes the indices of three points"))))
  (let-match many r2 (Cons _ k _) (else (qq (compile-error "`shoe` takes the indices of three points"))))
  (qq (EAdd (EAdd (EMul (EVar (~ i)) (EVar $ Succ (~ j))) (EMul (EVar (~ j)) (EVar $ Succ (~ k)))) (EMul (EVar (~ k)) (EVar $ Succ (~ i))))))

(def-fns _ $ (erased shoe-eval : (erased (List (Nat)) env) (erased (Nat) i j k) (erased (Point) p q r) (erased (Nat) s)
    (erased (PtAt env i p) a) (erased (PtAt env j q) b) (erased (PtAt env k r) c) (erased (Shoelace p q r s) h) ->
    (erased (Eval env (shoe i j k) s) v))
  (let-match erased a (MkPtAt _ _ px py ax ay))
  (let-match erased b (MkPtAt _ _ qx qy bx by))
  (let-match erased c (MkPtAt _ _ rx ry cx cy))
  (let-match erased h (MkShoelace _ _ _ _ _ _ m1 m2 m3 m12 _ p1 p2 p3 q1 q2))
  (EvAdd env _ _ m12 m3 s
    (EvAdd env _ _ m1 m2 m12 (EvMul env _ _ px qy m1 (EvVar env i px ax) (EvVar env (Succ j) qy by) p1)
      (EvMul env _ _ qx ry m2 (EvVar env j qx bx) (EvVar env (Succ k) ry cy) p2) q1)
    (EvMul env _ _ rx py m3 (EvVar env k rx cx) (EvVar env (Succ i) py ay) p3) q2))

(def-fns _ $ (many shoelace : (many (Point) p q r) -> (many (Nat) s) (erased (Shoelace p q r s) h))
  (let-match many p (MkPoint px py))
  (let-match many q (MkPoint qx qy))
  (let-match many r (MkPoint rx ry))
  (let ((many m1) (erased p1)) (mul px qy))
  (let ((many m2) (erased p2)) (mul qx ry))
  (let ((many m3) (erased p3)) (mul rx py))
  (let ((many m12) (erased q1)) (add m1 m2))
  (let ((many s) (erased q2)) (add m12 m3))
  (values s (MkShoelace px py qx qy rx ry m1 m2 m3 m12 s p1 p2 p3 q1 q2)))

(def-fns _ $ (erased shoe-fn : (erased (Point) p q r) (erased (Nat) s t) (erased (Shoelace p q r s) h) (erased (Shoelace p q r t) g) ->
    (erased (Eq (Nat) s t) e))
  (let ((erased env) (erased a) (erased b) (erased c) (erased _) (erased _)) (pts5 p q r p p))
  (eval-fn env _ s t (shoe-eval env i0 i2 i4 p q r s a b c h) (shoe-eval env i0 i2 i4 p q r t a b c g)))

(comptime-match many (ring-check (shoe i0 i2 i4) (shoe i2 i4 i0)) (Some _ rot-eq))

(def-fns _ $ (erased shoe-rot : (erased (Point) p q r) (erased (Nat) s) (erased (Shoelace p q r s) h) -> (erased (Shoelace q r p s) g))
  (let ((erased env) (erased a) (erased b) (erased c) (erased _) (erased _)) (pts5 p q r p p))
  (let ((erased t) (erased g)) (shoelace q r p))
  (let-match erased (ring-sound env _ _ s t rot-eq (shoe-eval env i0 i2 i4 p q r s a b c h) (shoe-eval env i2 i4 i0 q r p t b c a g)) (Refl _ _))
  g)

(def-fns _ $ (erased left-rot : (erased (Point) p q r) (erased (Left p q r) l) -> (erased (Left q r p) m))
  (let-match erased l (MkLeft _ _ _ s1 s2 h1 h2 lt))
  (MkLeft q r p s1 s2 (shoe-rot p q r s1 h1) (shoe-rot q p r s2 $ shoe-rot r q p s2 h2) lt))

(def-fns _ $ (erased absurd left-antisym : (erased (Point) p q r) (erased (Left p q r) l) (erased (Left q p r) m) -> (erased (False) f))
  (let-match erased l (MkLeft _ _ _ s1 s2 h1 h2 lt))
  (let-match erased m (MkLeft _ _ _ t1 t2 g1 g2 lt2))
  (let-match erased (shoe-fn q p r s2 t1 (shoe-rot r q p s2 h2) g1) (Refl _ _))
  (let-match erased (shoe-fn r p q s1 t2 (shoe-rot q r p s1 $ shoe-rot p q r s1 h1) g2) (Refl _ _))
  (lt-asym s2 s1 lt (lt-weaken s1 s2 lt2)))

(def-adts $ (Collinear : ((Point) p) ((Point) q) ((Point) r) -> Type)
  enum
  (many MkCollinear : (erased (Point) p q r) (erased (Nat) s) (erased (Shoelace p q r s) h1) (erased (Shoelace r q p s) h2)
     -> (Collinear p q r)))

(def-fns _ $ (erased absurd left-collinear : (erased (Point) p q r) (erased (Left p q r) l) (erased (Collinear p q r) c) -> (erased (False) f))
  (let-match erased l (MkLeft _ _ _ s1 s2 h1 h2 lt))
  (let-match erased c (MkCollinear _ _ _ s g1 g2))
  (let-match erased (shoe-fn p q r s1 s h1 g1) (Refl _ _))
  (let-match erased (shoe-fn r q p s2 s h2 g2) (Refl _ _))
  (lt-irrefl s lt))

(def-adts $ (Orient : ((Point) p) ((Point) q) ((Point) r) -> Type)
  enum
  (many OLeft : (erased (Point) p q r) (erased (Left p q r) l) -> (Orient p q r))
  (many ORight : (erased (Point) p q r) (erased (Left q p r) l) -> (Orient p q r))
  (many OOn : (erased (Point) p q r) (erased (Collinear p q r) c) -> (Orient p q r)))

(def-fns _ $ (many left-dec : (many (Point) p q r) -> (many (Orient p q r) o))
  (let ((many s1) (erased h1)) (shoelace p q r))
  (let ((many s2) (erased h2)) (shoelace r q p))
  (match many (nat-cmp s2 s1) _
    ((CLt _ _ _ _ lt) (OLeft p q r (MkLeft p q r s1 s2 h1 h2 lt)))
    ((CEq _ _ _) (OOn p q r (MkCollinear p q r s1 h1 h2)))
    ((CGt _ _ _ _ gt) (ORight p q r (MkLeft q p r s2 s1 (shoe-rot r q p s2 h2) (shoe-rot q r p s1 $ shoe-rot p q r s1 h1) gt)))))

(let ((many ta1)) (shoe i0 i2 i4))
(let ((many ta2)) (shoe i0 i6 i8))
(let ((many ta3)) (shoe i0 i2 i8))
(let ((many ta4)) (shoe i0 i4 i6))
