(let ((many i5)) (Succ i4))
(let ((many i7)) (Succ i6))
(let ((many i9)) (Succ i8))

(def-macro (sh args)
  (let-match many args (Cons _ ax r1) (else (qq (compile-error "`sh` takes six coordinates"))))
  (let-match many r1 (Cons _ ay r2) (else (qq (compile-error "`sh` takes six coordinates"))))
  (let-match many r2 (Cons _ bx r3) (else (qq (compile-error "`sh` takes six coordinates"))))
  (let-match many r3 (Cons _ by r4) (else (qq (compile-error "`sh` takes six coordinates"))))
  (let-match many r4 (Cons _ cx r5) (else (qq (compile-error "`sh` takes six coordinates"))))
  (let-match many r5 (Cons _ cy _) (else (qq (compile-error "`sh` takes six coordinates"))))
  (qq (EAdd (EAdd (EMul (~ ax) (~ by)) (EMul (~ bx) (~ cy))) (EMul (~ cx) (~ ay)))))

(def-fns _ $ (many nth-raw : (subterm many (Nat) k) -> (many (Raw) r))
  (match many k _
    ((Zero) (let-match many (qq (NthHere _ _ _)) (Cons _ r _)) r)
    ((Succ k1) (let ((many r1)) (notail $ nth-raw k1)) (let-match many (qq (NthThere _ _ _ _ _ (~ r1))) (Cons _ r _)) r)))

(def-macro (nthp args here mw)
  (let-match many args (Cons _ a _) ((Nil _) (macro-fail mw here "`nthp` takes an index")))
  (let ((unique mw1) (many n)) (arg-nat mw a))
  (let-match many n (Some _ k) ((None _) (macro-fail mw1 here "`nthp` takes a numeral")))
  (values mw1 (Cons _ (nth-raw k) (Nil _))))

(def-adts $ (PtE : ((List (Nat)) env) ((Expr) ex) ((Expr) ey) ((Point) p) -> Type)
  enum
  (many MkPtE : (erased (List (Nat)) env) (erased (Expr) ex ey) (erased (Nat) x y) (erased (Eval env ex x) vx) (erased (Eval env ey y) vy)
     -> (PtE env ex ey (MkPoint x y))))

(def-fns _ $ (erased shoe-ev : (erased (List (Nat)) env) (erased (Expr) ax ay bx by cx cy) (erased (Point) p q r) (erased (Nat) s)
    (erased (PtE env ax ay p) a) (erased (PtE env bx by q) b) (erased (PtE env cx cy r) c) (erased (Shoelace p q r s) h) ->
    (erased (Eval env (EAdd (EAdd (EMul ax by) (EMul bx cy)) (EMul cx ay)) s) v))
  (let-match erased a (MkPtE _ _ _ px py vax vay))
  (let-match erased b (MkPtE _ _ _ qx qy vbx vby))
  (let-match erased c (MkPtE _ _ _ rx ry vcx vcy))
  (let-match erased h (MkShoelace _ _ _ _ _ _ m1 m2 m3 m12 _ p1 p2 p3 q1 q2))
  (EvAdd env _ _ m12 m3 s
    (EvAdd env _ _ m1 m2 m12 (EvMul env _ _ px qy m1 vax vby p1) (EvMul env _ _ qx ry m2 vbx vcy p2) q1)
    (EvMul env _ _ rx py m3 vcx vay p3) q2))

; t is the sum of the products of the entries of xs with those of ns.
(def-adts $ (Dot : ((List (Nat)) xs) ((List (Nat)) ns) ((Nat) t) -> Type)
  enum
  (many DotNil : -> (Dot (Nil (Nat)) (Nil (Nat)) (Zero)))
  (many DotCons : (erased (Nat) x n xn t u) (erased (List (Nat)) xs ns) (erased (Mul x n xn) m) (erased (Dot xs ns t) d) (erased (Add xn t u) a)
     -> (Dot (Cons (Nat) x xs) (Cons (Nat) n ns) u)))

(def-adts $ (LeAll : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
  enum
  (many LeNil : -> (LeAll (Nil (Nat)) (Nil (Nat))))
  (many LeCons : (erased (Nat) x y) (erased (List (Nat)) xs ys) (erased (Lt x (Succ y)) l) (erased (LeAll xs ys) rest)
     -> (LeAll (Cons (Nat) x xs) (Cons (Nat) y ys))))

; xs is below ys entrywise, strictly at some entry whose weight in ns is positive.
(def-adts $ (Dom : ((List (Nat)) xs) ((List (Nat)) ys) ((List (Nat)) ns) -> Type)
  enum
  (many DomHere : (erased (Nat) x y n) (erased (List (Nat)) xs ys ns) (erased (Lt x y) l) (erased (Lt (Zero) n) pos) (erased (LeAll xs ys) rest)
     -> (Dom (Cons (Nat) x xs) (Cons (Nat) y ys) (Cons (Nat) n ns)))
  (many DomThere : (erased (Nat) x y n) (erased (List (Nat)) xs ys ns) (erased (Lt x (Succ y)) l) (erased (Dom xs ys ns) rest)
     -> (Dom (Cons (Nat) x xs) (Cons (Nat) y ys) (Cons (Nat) n ns))))

(def-fns _ $ (erased mul-mono : (erased (Nat) a b n x y) (erased (Lt a (Succ b)) l) (erased (Mul a n x) ma) (erased (Mul b n y) mb) ->
    (erased (Lt x (Succ y)) r))
  (let ((erased d) (erased p)) (sub b a l))
  (let ((erased dn) (erased md)) (mul d n))
  (add-le-left x dn y (mul-distr a d b n x dn y p ma md mb)))

(def-fns _ $ (erased mul-strict : (erased (Nat) a b n x y) (erased (Lt a b) l) (erased (Lt (Zero) n) pos) (erased (Mul a n x) ma) (erased (Mul b n y) mb) ->
    (erased (Lt x y) r))
  (let ((erased d) (erased p)) (lt-diff a b l))
  (let ((erased dn) (erased md)) (mul (Succ d) n))
  (let-match erased md (MulSucc _ _ c _ md1 pc))
  (add-pos-lt x dn y (mul-distr a (Succ d) b n x dn y p ma md mb) (lt-le-trans (Zero) n dn pos (add-le-right c n dn pc))))

(def-fns _ $ (erased add-lt-le : (erased (Nat) a b c d x y) (erased (Lt a (Succ b)) l) (erased (Lt c (Succ d)) k) (erased (Add a c x) p) (erased (Add b d y) q) ->
    (erased (Lt x (Succ y)) r))
  (let ((erased w) (erased o)) (add b c))
  (lt-le-trans x (Succ w) (Succ y) (add-mono-le c a b x w l (add-comm a c x p) (add-comm b c w o))
    (LtS w (Succ y) (add-mono-le b c d w y k o q))))

(def-fns _ $ (erased le-all-dot : (erased (List (Nat)) xs ys ns) (erased (Nat) t u) (subterm erased (LeAll xs ys) le)
    (erased (Dot xs ns t) dx) (erased (Dot ys ns u) dy) -> (erased (Lt t (Succ u)) r))
  (let-match erased le (LeCons x y xs1 ys1 l le1)
    ((LeNil) (let-match erased dx (DotNil)) (let-match erased dy (DotNil)) (LtZ (Zero))))
  (let-match erased dx (DotCons _ n xn t1 _ _ ns1 mx dx1 ax))
  (let-match erased dy (DotCons _ _ yn u1 _ _ _ my dy1 ay))
  (add-lt-le xn yn t1 u1 t u (mul-mono x y n xn yn l mx my) (le-all-dot xs1 ys1 ns1 t1 u1 le1 dx1 dy1) ax ay))

(def-fns _ $ (erased dom-dot : (erased (List (Nat)) xs ys ns) (erased (Nat) t u) (subterm erased (Dom xs ys ns) dm)
    (erased (Dot xs ns t) dx) (erased (Dot ys ns u) dy) -> (erased (Lt t u) r))
  (match erased dm _
    ((DomHere x y n xs1 ys1 ns1 l pos le)
      (let-match erased dx (DotCons _ _ xn t1 _ _ _ mx dx1 ax))
      (let-match erased dy (DotCons _ _ yn u1 _ _ _ my dy1 ay))
      (add-lt xn yn t1 u1 t u (mul-strict x y n xn yn l pos mx my) (le-all-dot xs1 ys1 ns1 t1 u1 le dx1 dy1) ax ay))
    ((DomThere x y n xs1 ys1 ns1 l dm1)
      (let-match erased dx (DotCons _ _ xn t1 _ _ _ mx dx1 ax))
      (let-match erased dy (DotCons _ _ yn u1 _ _ _ my dy1 ay))
      (add-lt t1 u1 xn yn t u (dom-dot xs1 ys1 ns1 t1 u1 dm1 dx1 dy1) (mul-mono x y n xn yn l mx my)
        (add-comm xn t1 t ax) (add-comm yn u1 u ay)))))

(def-macro (ev args)
  (let-match many args (Cons _ k _) ((Nil _) (qq (compile-error "`ev` takes an index"))))
  (qq (EvVar _ _ _ (nthp (~ k)))))

(def-macro (dotx args)
  (let-match many args (Cons _ x r1) ((Nil _) (qq (ENum i0))))
  (let-match many r1 (Cons _ n r2) ((Nil _) (qq (compile-error "`dotx` takes values and weights in pairs"))))
  (qq (EAdd (EMul (~ x) (~ n)) (~@ $ notail $ dotx r2))))

(def-fns _ $ (erased ev-dot : (erased (List (Nat)) env) (erased (Expr) ex en er) (erased (Nat) x n t) (erased (List (Nat)) xs ns)
    (erased (Eval env ex x) vx) (erased (Eval env en n) vn) (erased (Eval env er t) vr) (erased (Dot xs ns t) d) ->
    (erased (Nat) u) (erased (Dot (Cons (Nat) x xs) (Cons (Nat) n ns) u) d2) (erased (Eval env (EAdd (EMul ex en) er) u) v))
  (let ((erased xn) (erased m)) (mul x n))
  (let ((erased u) (erased a)) (add xn t))
  (values u (DotCons x n xn t u xs ns m d a) (EvAdd env _ _ xn t u (EvMul env _ _ x n xn vx vn m) vr a)))

(def-fns _ $ (erased coll-rot : (erased (Point) p q r) (erased (Collinear p q r) c) -> (erased (Collinear q r p) d))
  (let-match erased c (MkCollinear _ _ _ s h1 h2))
  (MkCollinear q r p s (shoe-rot p q r s h1) (shoe-rot q p r s $ shoe-rot r q p s h2)))

(def-fns _ $ (erased coll-rev : (erased (Point) p q r) (erased (Collinear p q r) c) -> (erased (Collinear r q p) d))
  (let-match erased c (MkCollinear _ _ _ s h1 h2))
  (MkCollinear r q p s h2 h1))

(def-fns _ $ (erased coll-swap : (erased (Point) p q r) (erased (Collinear p q r) c) -> (erased (Collinear q p r) d))
  (coll-rot r q p (coll-rev p q r c)))

(def-fns _ $ (erased coll-same : (erased (Point) u v) -> (erased (Collinear u v u) c))
  (let ((erased s) (erased h)) (shoelace u v u))
  (MkCollinear u v u s h h))

(def-fns _ $ (erased absurd offline-coll : (erased (Point) a b r) (erased (OffLine a b r) o) (erased (Collinear a b r) c) -> (erased (False) f))
  (match erased o _
    (absurd (OffLeft _ _ _ l) (left-collinear a b r l c))
    (absurd (OffRight _ _ _ l) (left-collinear b a r l (coll-swap a b r c)))))

; r is left of the line from p to q, or on it.
(def-adts $ (Weak : ((Point) p) ((Point) q) ((Point) r) -> Type)
  enum
  (many MkWeak : (erased (Point) p q r) (erased (Nat) s1 s2)
      (erased (Shoelace p q r s1) h1) (erased (Shoelace r q p s2) h2) (erased (Lt s2 (Succ s1)) l)
      -> (Weak p q r)))

(def-fns _ $ (erased left-weak : (erased (Point) p q r) (erased (Left p q r) l) -> (erased (Weak p q r) w))
  (let-match erased l (MkLeft _ _ _ s1 s2 h1 h2 lt))
  (MkWeak p q r s1 s2 h1 h2 (lt-weaken s2 s1 lt)))

(def-fns _ $ (erased coll-weak : (erased (Point) p q r) (erased (Collinear p q r) c) -> (erased (Weak p q r) w))
  (let-match erased c (MkCollinear _ _ _ s h1 h2))
  (MkWeak p q r s s h1 h2 (lt-succ s)))

; The shoelace halves of pqr, read off a claim about qpr.
(def-fns _ $ (erased weak-rev : (erased (Point) p q r) (erased (Weak q p r) w) ->
    (erased (Nat) a b) (erased (Shoelace p q r a) ha) (erased (Shoelace r q p b) hb) (erased (Lt a (Succ b)) l))
  (let-match erased w (MkWeak _ _ _ s1 s2 h1 h2 l))
  (values s2 s1 (shoe-rot r p q s2 h2) (shoe-rot p r q s1 $ shoe-rot q p r s1 h1) l))

(def-fns _ $ (erased left-rev : (erased (Point) p q r) (erased (Left q p r) w) ->
    (erased (Nat) a b) (erased (Shoelace p q r a) ha) (erased (Shoelace r q p b) hb) (erased (Lt a b) l))
  (let-match erased w (MkLeft _ _ _ s1 s2 h1 h2 l))
  (values s2 s1 (shoe-rot r p q s2 h2) (shoe-rot p r q s1 $ shoe-rot q p r s1 h1) l))

(comptime-match many (ring-check (sh (EVar i0) (EVar i1) (EVar i0) (EVar i2) (EVar i0) (EVar i3))
    (sh (EVar i0) (EVar i3) (EVar i0) (EVar i2) (EVar i0) (EVar i1)))
  (Some _ vert-eq))

(def-fns _ $ (erased coll-vert : (erased (Nat) x py qy ry) -> (erased (Collinear (MkPoint x py) (MkPoint x qy) (MkPoint x ry)) c))
  (let ((erased env)) (Cons _ x $ Cons _ py $ Cons _ qy $ Cons _ ry $ Nil (Nat)))
  (let ((erased p)) (MkPtE env (EVar i0) (EVar i1) x py (ev 0) (ev 1)))
  (let ((erased q)) (MkPtE env (EVar i0) (EVar i2) x qy (ev 0) (ev 2)))
  (let ((erased r)) (MkPtE env (EVar i0) (EVar i3) x ry (ev 0) (ev 3)))
  (let ((erased s) (erased h1)) (shoelace (MkPoint x py) (MkPoint x qy) (MkPoint x ry)))
  (let ((erased t) (erased h2)) (shoelace (MkPoint x ry) (MkPoint x qy) (MkPoint x py)))
  (let-match erased (ring-sound env _ _ s t vert-eq (shoe-ev env _ _ _ _ _ _ _ _ _ s p q r h1) (shoe-ev env _ _ _ _ _ _ _ _ _ t r q p h2)) (Refl _ _))
  (MkCollinear _ _ _ s h1 h2))

; Points s, q, w with x-offsets al and be between them, and a line from u to v rising by ga in x.
(let ((many a-sx)) (EVar i0))
(let ((many a-qx)) (EAdd (EVar i0) (EVar i1)))
(let ((many a-wx)) (EAdd a-qx (EVar i2)))
(let ((many a-ux)) (EVar i3))
(let ((many a-vx)) (EAdd (EVar i3) (EVar i4)))
(let ((many a-n)) (EAdd (EVar i1) (EVar i2)))
(comptime-match many (ring-check
    (dotx (sh a-ux (EVar i8) a-vx (EVar i9) a-qx (EVar i6)) a-n (sh a-sx (EVar i5) a-vx (EVar i9) a-ux (EVar i8)) (EVar i2)
      (sh a-wx (EVar i7) a-vx (EVar i9) a-ux (EVar i8)) (EVar i1) (sh a-qx (EVar i6) a-wx (EVar i7) a-sx (EVar i5)) (EVar i4))
    (dotx (sh a-qx (EVar i6) a-vx (EVar i9) a-ux (EVar i8)) a-n (sh a-ux (EVar i8) a-vx (EVar i9) a-sx (EVar i5)) (EVar i2)
      (sh a-ux (EVar i8) a-vx (EVar i9) a-wx (EVar i7)) (EVar i1) (sh a-sx (EVar i5) a-wx (EVar i7) a-qx (EVar i6)) (EVar i4)))
  (Some _ ai-eq))

(def-fns _ $ (erased ai : (erased (Nat) sx al be ux ga sy qy wy uy vy qx wx vx n)
    (erased (Add sx al qx) pq) (erased (Add qx be wx) pw) (erased (Add ux ga vx) pv) (erased (Add al be n) pn)
    (erased (Nat) a1 a2 b1 b2 c1 c2 e1 e2)
    (erased (Shoelace (MkPoint ux uy) (MkPoint vx vy) (MkPoint qx qy) a1) ha1)
    (erased (Shoelace (MkPoint qx qy) (MkPoint vx vy) (MkPoint ux uy) a2) ha2)
    (erased (Shoelace (MkPoint ux uy) (MkPoint vx vy) (MkPoint sx sy) b1) hb1)
    (erased (Shoelace (MkPoint sx sy) (MkPoint vx vy) (MkPoint ux uy) b2) hb2)
    (erased (Shoelace (MkPoint ux uy) (MkPoint vx vy) (MkPoint wx wy) c1) hc1)
    (erased (Shoelace (MkPoint wx wy) (MkPoint vx vy) (MkPoint ux uy) c2) hc2)
    (erased (Shoelace (MkPoint sx sy) (MkPoint wx wy) (MkPoint qx qy) e1) he1)
    (erased (Shoelace (MkPoint qx qy) (MkPoint wx wy) (MkPoint sx sy) e2) he2) ->
    (erased (Nat) t)
    (erased (Dot (Cons (Nat) a1 $ Cons (Nat) b2 $ Cons (Nat) c2 $ Cons (Nat) e2 $ Nil (Nat)) (Cons (Nat) n $ Cons (Nat) be $ Cons (Nat) al $ Cons (Nat) ga $ Nil (Nat)) t) dl)
    (erased (Dot (Cons (Nat) a2 $ Cons (Nat) b1 $ Cons (Nat) c1 $ Cons (Nat) e1 $ Nil (Nat)) (Cons (Nat) n $ Cons (Nat) be $ Cons (Nat) al $ Cons (Nat) ga $ Nil (Nat)) t) dr))
  (let ((erased env)) (Cons _ sx $ Cons _ al $ Cons _ be $ Cons _ ux $ Cons _ ga $ Cons _ sy $ Cons _ qy $ Cons _ wy $ Cons _ uy $ Cons _ vy $ Nil (Nat)))
  (let ((erased vqx)) (EvAdd env _ _ sx al qx (ev 0) (ev 1) pq))
  (let ((erased s)) (MkPtE env a-sx (EVar i5) sx sy (ev 0) (ev 5)))
  (let ((erased q)) (MkPtE env a-qx (EVar i6) qx qy vqx (ev 6)))
  (let ((erased w)) (MkPtE env a-wx (EVar i7) wx wy (EvAdd env _ _ qx be wx vqx (ev 2) pw) (ev 7)))
  (let ((erased u)) (MkPtE env a-ux (EVar i8) ux uy (ev 3) (ev 8)))
  (let ((erased v)) (MkPtE env a-vx (EVar i9) vx vy (EvAdd env _ _ ux ga vx (ev 3) (ev 4) pv) (ev 9)))
  (let ((erased vn)) (EvAdd env _ _ al be n (ev 1) (ev 2) pn))
  (let ((erased l4) (erased dl4) (erased vl4)) (ev-dot env _ _ _ e2 ga _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ e2 q w s he2) (ev 4) (EvNum env i0) (DotNil)))
  (let ((erased l3) (erased dl3) (erased vl3)) (ev-dot env _ _ _ c2 al _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ c2 w v u hc2) (ev 1) vl4 dl4))
  (let ((erased l2) (erased dl2) (erased vl2)) (ev-dot env _ _ _ b2 be _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ b2 s v u hb2) (ev 2) vl3 dl3))
  (let ((erased l1) (erased dl1) (erased vl1)) (ev-dot env _ _ _ a1 n _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ a1 u v q ha1) vn vl2 dl2))
  (let ((erased r4) (erased dr4) (erased vr4)) (ev-dot env _ _ _ e1 ga _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ e1 s w q he1) (ev 4) (EvNum env i0) (DotNil)))
  (let ((erased r3) (erased dr3) (erased vr3)) (ev-dot env _ _ _ c1 al _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ c1 u v w hc1) (ev 1) vr4 dr4))
  (let ((erased r2) (erased dr2) (erased vr2)) (ev-dot env _ _ _ b1 be _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ b1 u v s hb1) (ev 2) vr3 dr3))
  (let ((erased r1) (erased dr1) (erased vr1)) (ev-dot env _ _ _ a2 n _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ a2 q v u ha2) vn vr2 dr2))
  (let-match erased (ring-sound env _ _ l1 r1 ai-eq vl1 vr1) (Refl _ _))
  (values l1 dl1 dr1))

(def-adts $ (XLe : ((Point) p) ((Point) q) -> Type)
  enum
  (many MkXLe : (erased (Nat) px py qx qy d) (erased (Add px d qx) a) -> (XLe (MkPoint px py) (MkPoint qx qy))))

(def-fns _ $ (erased flat : (erased (Nat) sx sy qx qy wx wy al be) (erased (Add al be (Zero)) pn) (erased (Add sx al qx) pq)
    (erased (Add qx be wx) pw) -> (erased (Collinear (MkPoint sx sy) (MkPoint wx wy) (MkPoint qx qy)) c))
  (let-match erased pn (AddZero _))
  (let-match erased (add-fn sx (Zero) qx sx pq (add-zero-right sx)) (Refl _ _))
  (let-match erased (add-fn sx (Zero) wx sx pw (add-zero-right sx)) (Refl _ _))
  (coll-vert sx sy wy qy))

; For q between s and w in x, and u at or before v: when s and w are weakly left of uv, q weakly right of uv and
; weakly left of sw, with q strictly right of uv or s and w strictly left of it, the three of s, w, q share an x.
(def-fns _ $ (erased sq-up : (erased (Point) u v s w q) (erased (XLe u v) xuv) (erased (XLe s q) xsq) (erased (XLe q w) xqw)
    (erased (Weak u v s) ws) (erased (Weak u v w) ww) (erased (Weak s w q) wq) (erased (Weak v u q) wu)
    (erased (Or (Left v u q) (Pair (Left u v s) (Left u v w))) st) -> (erased (Collinear s w q) c))
  (let-match erased xuv (MkXLe ux uy vx vy ga pv))
  (let-match erased xsq (MkXLe sx sy qx qy al pq))
  (let-match erased xqw (MkXLe _ _ wx wy be pw))
  (let ((erased n) (erased pn)) (add al be))
  (let-match erased n (Succ n1) ((Zero) (flat sx sy qx qy wx wy al be pn pq pw)))
  (let-match erased wq (MkWeak _ _ _ e1 e2 he1 he2 le))
  (match erased st _
    (absurd (OrL _ _ l)
      (let ((erased a1) (erased a2) (erased ha1) (erased ha2) (erased la)) (left-rev u v q l))
      (let-match erased ws (MkWeak _ _ _ b1 b2 hb1 hb2 lb))
      (let-match erased ww (MkWeak _ _ _ c1 c2 hc1 hc2 lc))
      (let ((erased t) (erased dl) (erased dr)) (ai sx al be ux ga sy qy wy uy vy qx wx vx n pq pw pv pn a1 a2 b1 b2 c1 c2 e1 e2 ha1 ha2 hb1 hb2 hc1 hc2 he1 he2))
      (lt-irrefl t (dom-dot _ _ _ t t (DomHere _ _ _ _ _ _ la (LtZ n1) (LeCons _ _ _ _ lb $ LeCons _ _ _ _ lc $ LeCons _ _ _ _ le $ LeNil)) dl dr)))
    (absurd (OrR _ _ lp)
      (let-match erased lp (MkPair _ _ l1 l2))
      (let ((erased a1) (erased a2) (erased ha1) (erased ha2) (erased la)) (weak-rev u v q wu))
      (let-match erased l1 (MkLeft _ _ _ b1 b2 hb1 hb2 lb))
      (let-match erased l2 (MkLeft _ _ _ c1 c2 hc1 hc2 lc))
      (let ((erased t) (erased dl) (erased dr)) (ai sx al be ux ga sy qy wy uy vy qx wx vx n pq pw pv pn a1 a2 b1 b2 c1 c2 e1 e2 ha1 ha2 hb1 hb2 hc1 hc2 he1 he2))
      (lt-irrefl t (dom-dot (Cons _ a1 $ Cons _ b2 $ Cons _ c2 $ Cons _ e2 $ Nil (Nat)) (Cons _ a2 $ Cons _ b1 $ Cons _ c1 $ Cons _ e1 $ Nil (Nat))
          (Cons _ n $ Cons _ be $ Cons _ al $ Cons _ ga $ Nil (Nat)) t t
          (match erased al _
            ((Succ al1) (DomThere _ _ _ _ _ _ la $ DomThere _ _ _ _ _ _ (lt-weaken b2 b1 lb) $ DomHere _ _ _ _ _ _ lc (LtZ al1) (LeCons _ _ _ _ le $ LeNil)))
            ((Zero) (let-match erased pn (AddZero _))
              (DomThere _ _ _ _ _ _ la $ DomHere _ _ _ _ _ _ lb (LtZ n1) (LeCons _ _ _ _ (lt-weaken c2 c1 lc) $ LeCons _ _ _ _ le $ LeNil))))
          dl dr)))))

; sq-up with every side reversed.
(def-fns _ $ (erased sq-down : (erased (Point) u v s w q) (erased (XLe u v) xuv) (erased (XLe s q) xsq) (erased (XLe q w) xqw)
    (erased (Weak v u s) ws) (erased (Weak v u w) ww) (erased (Weak w s q) wq) (erased (Weak u v q) wu)
    (erased (Or (Left u v q) (Pair (Left v u s) (Left v u w))) st) -> (erased (Collinear s w q) c))
  (let-match erased xuv (MkXLe ux uy vx vy ga pv))
  (let-match erased xsq (MkXLe sx sy qx qy al pq))
  (let-match erased xqw (MkXLe _ _ wx wy be pw))
  (let ((erased n) (erased pn)) (add al be))
  (let-match erased n (Succ n1) ((Zero) (flat sx sy qx qy wx wy al be pn pq pw)))
  (let ((erased e1) (erased e2) (erased he1) (erased he2) (erased le)) (weak-rev s w q wq))
  (match erased st _
    (absurd (OrL _ _ l)
      (let-match erased l (MkLeft _ _ _ a1 a2 ha1 ha2 la))
      (let ((erased b1) (erased b2) (erased hb1) (erased hb2) (erased lb)) (weak-rev u v s ws))
      (let ((erased c1) (erased c2) (erased hc1) (erased hc2) (erased lc)) (weak-rev u v w ww))
      (let ((erased t) (erased dl) (erased dr)) (ai sx al be ux ga sy qy wy uy vy qx wx vx n pq pw pv pn a1 a2 b1 b2 c1 c2 e1 e2 ha1 ha2 hb1 hb2 hc1 hc2 he1 he2))
      (lt-irrefl t (dom-dot _ _ _ t t (DomHere _ _ _ _ _ _ la (LtZ n1) (LeCons _ _ _ _ lb $ LeCons _ _ _ _ lc $ LeCons _ _ _ _ le $ LeNil)) dr dl)))
    (absurd (OrR _ _ lp)
      (let-match erased lp (MkPair _ _ l1 l2))
      (let-match erased wu (MkWeak _ _ _ a1 a2 ha1 ha2 la))
      (let ((erased b1) (erased b2) (erased hb1) (erased hb2) (erased lb)) (left-rev u v s l1))
      (let ((erased c1) (erased c2) (erased hc1) (erased hc2) (erased lc)) (left-rev u v w l2))
      (let ((erased t) (erased dl) (erased dr)) (ai sx al be ux ga sy qy wy uy vy qx wx vx n pq pw pv pn a1 a2 b1 b2 c1 c2 e1 e2 ha1 ha2 hb1 hb2 hc1 hc2 he1 he2))
      (lt-irrefl t (dom-dot (Cons _ a2 $ Cons _ b1 $ Cons _ c1 $ Cons _ e1 $ Nil (Nat)) (Cons _ a1 $ Cons _ b2 $ Cons _ c2 $ Cons _ e2 $ Nil (Nat))
          (Cons _ n $ Cons _ be $ Cons _ al $ Cons _ ga $ Nil (Nat)) t t
          (match erased al _
            ((Succ al1) (DomThere _ _ _ _ _ _ la $ DomThere _ _ _ _ _ _ (lt-weaken b1 b2 lb) $ DomHere _ _ _ _ _ _ lc (LtZ al1) (LeCons _ _ _ _ le $ LeNil)))
            ((Zero) (let-match erased pn (AddZero _))
              (DomThere _ _ _ _ _ _ la $ DomHere _ _ _ _ _ _ lb (LtZ n1) (LeCons _ _ _ _ (lt-weaken c1 c2 lc) $ LeCons _ _ _ _ le $ LeNil))))
          dr dl)))))

(def-adts $ (LexLt : ((Point) p) ((Point) q) -> Type)
  enum
  (many LexX : (erased (Nat) px py qx qy) (erased (Lt px qx) l) -> (LexLt (MkPoint px py) (MkPoint qx qy)))
  (many LexY : (erased (Nat) x py qy) (erased (Lt py qy) l) -> (LexLt (MkPoint x py) (MkPoint x qy))))

(def-fns _ $ (erased lex-xle : (erased (Point) p q) (erased (LexLt p q) l) -> (erased (XLe p q) x))
  (let-match erased l (LexX px py qx qy lt) ((LexY x py qy _) (MkXLe x py x qy (Zero) (add-zero-right x))))
  (let ((erased d) (erased a)) (sub qx px (lt-weaken px qx lt)))
  (MkXLe px py qx qy d a))

(comptime-match many (ring-check (EAdd (sh (EVar i0) (EVar i1) (EVar i0) (EAdd (EVar i1) (EVar i2)) (EAdd (EVar i0) (EVar i3)) (EVar i4)) (EMul (EVar i2) (EVar i3)))
    (sh (EAdd (EVar i0) (EVar i3)) (EVar i4) (EVar i0) (EAdd (EVar i1) (EVar i2)) (EVar i0) (EVar i1)))
  (Some _ vh-eq))

; Nothing at or after t in x is strictly left of a ray from t straight up.
(def-fns _ $ (erased absurd vh : (erased (Nat) tx ty py qx qy g) (erased (Lt ty py) lt) (erased (Add tx g qx) aq)
    (erased (Left (MkPoint tx ty) (MkPoint tx py) (MkPoint qx qy)) l) -> (erased (False) f))
  (let ((erased d) (erased pd)) (sub py ty (lt-weaken ty py lt)))
  (let ((erased env)) (Cons _ tx $ Cons _ ty $ Cons _ d $ Cons _ g $ Cons _ qy $ Nil (Nat)))
  (let ((erased vpy)) (EvAdd env _ _ ty d py (ev 1) (ev 2) pd))
  (let ((erased vqx)) (EvAdd env _ _ tx g qx (ev 0) (ev 3) aq))
  (let ((erased t)) (MkPtE env (EVar i0) (EVar i1) tx ty (ev 0) (ev 1)))
  (let ((erased p)) (MkPtE env (EVar i0) (EAdd (EVar i1) (EVar i2)) tx py (ev 0) vpy))
  (let ((erased q)) (MkPtE env (EAdd (EVar i0) (EVar i3)) (EVar i4) qx qy vqx (ev 4)))
  (let-match erased l (MkLeft _ _ _ s1 s2 h1 h2 ls))
  (let ((erased dg) (erased m) (erased vdg)) (ev-mul env _ _ d g (ev 2) (ev 3)))
  (let ((erased z) (erased a) (erased vz)) (ev-add env _ _ s1 dg (shoe-ev env _ _ _ _ _ _ _ _ _ s1 t p q h1) vdg))
  (let-match erased (ring-sound env _ _ z s2 vh-eq vz (shoe-ev env _ _ _ _ _ _ _ _ _ s2 q p t h2)) (Refl _ _))
  (lt-asym s2 s1 ls (add-le-left s1 dg s2 a)))

(comptime-match many (ring-check
    (dotx (sh (EAdd (EVar i0) (EVar i4)) (EVar i5) (EAdd (EVar i0) (EVar i2)) (EVar i3) (EVar i0) (EVar i1)) (EVar i6)
      (sh (EAdd (EVar i0) (EVar i6)) (EVar i7) (EAdd (EVar i0) (EVar i4)) (EVar i5) (EVar i0) (EVar i1)) (EVar i2)
      (sh (EVar i0) (EVar i1) (EAdd (EVar i0) (EVar i2)) (EVar i3) (EAdd (EVar i0) (EVar i6)) (EVar i7)) (EVar i4))
    (dotx (sh (EVar i0) (EVar i1) (EAdd (EVar i0) (EVar i2)) (EVar i3) (EAdd (EVar i0) (EVar i4)) (EVar i5)) (EVar i6)
      (sh (EVar i0) (EVar i1) (EAdd (EVar i0) (EVar i4)) (EVar i5) (EAdd (EVar i0) (EVar i6)) (EVar i7)) (EVar i2)
      (sh (EAdd (EVar i0) (EVar i6)) (EVar i7) (EAdd (EVar i0) (EVar i2)) (EVar i3) (EVar i0) (EVar i1)) (EVar i4)))
  (Some _ ht-eq))

(def-fns _ $ (erased absurd left-turn-absurd : (erased (Nat) tx ty px py qx qy rx ry gp1 gq gr)
    (erased (Add tx (Succ gp1) px) ap) (erased (Add tx gq qx) aq) (erased (Add tx gr rx) ar)
    (erased (Left (MkPoint tx ty) (MkPoint px py) (MkPoint qx qy)) l1) (erased (Left (MkPoint tx ty) (MkPoint qx qy) (MkPoint rx ry)) l2)
    (erased (Weak (MkPoint px py) (MkPoint tx ty) (MkPoint rx ry)) w) -> (erased (False) f))
  (let ((erased env)) (Cons _ tx $ Cons _ ty $ Cons _ (Succ gp1) $ Cons _ py $ Cons _ gq $ Cons _ qy $ Cons _ gr $ Cons _ ry $ Nil (Nat)))
  (let ((erased t)) (MkPtE env (EVar i0) (EVar i1) tx ty (ev 0) (ev 1)))
  (let ((erased p)) (MkPtE env (EAdd (EVar i0) (EVar i2)) (EVar i3) px py (EvAdd env _ _ tx (Succ gp1) px (ev 0) (ev 2) ap) (ev 3)))
  (let ((erased q)) (MkPtE env (EAdd (EVar i0) (EVar i4)) (EVar i5) qx qy (EvAdd env _ _ tx gq qx (ev 0) (ev 4) aq) (ev 5)))
  (let ((erased r)) (MkPtE env (EAdd (EVar i0) (EVar i6)) (EVar i7) rx ry (EvAdd env _ _ tx gr rx (ev 0) (ev 6) ar) (ev 7)))
  (let-match erased l1 (MkLeft _ _ _ a1 a2 ha1 ha2 la))
  (let-match erased l2 (MkLeft _ _ _ b1 b2 hb1 hb2 lb))
  (let ((erased c1) (erased c2) (erased hc1) (erased hc2) (erased lc)) (weak-rev _ _ _ w))
  (let ((erased z3) (erased dl3) (erased vl3)) (ev-dot env _ _ _ c1 gq _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ c1 t p r hc1) (ev 4) (EvNum env i0) (DotNil)))
  (let ((erased z2) (erased dl2) (erased vl2)) (ev-dot env _ _ _ b2 (Succ gp1) _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ b2 r q t hb2) (ev 2) vl3 dl3))
  (let ((erased z1) (erased dl1) (erased vl1)) (ev-dot env _ _ _ a2 gr _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ a2 q p t ha2) (ev 6) vl2 dl2))
  (let ((erased r3) (erased dr3) (erased vr3)) (ev-dot env _ _ _ c2 gq _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ c2 r p t hc2) (ev 4) (EvNum env i0) (DotNil)))
  (let ((erased r2) (erased dr2) (erased vr2)) (ev-dot env _ _ _ b1 (Succ gp1) _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ b1 t q r hb1) (ev 2) vr3 dr3))
  (let ((erased r1) (erased dr1) (erased vr1)) (ev-dot env _ _ _ a1 gr _ _ _ (shoe-ev env _ _ _ _ _ _ _ _ _ a1 t p q ha1) (ev 6) vr2 dr2))
  (let-match erased (ring-sound env _ _ z1 r1 ht-eq vl1 vr1) (Refl _ _))
  (lt-irrefl z1 (dom-dot _ _ _ z1 z1 (DomThere _ _ _ _ _ _ (lt-weaken a2 a1 la) $ DomHere _ _ _ _ _ _ lb (LtZ gp1) (LeCons _ _ _ _ lc $ LeNil)) dl1 dr1)))

; Around t, the order by direction of points lexicographically after t is transitive.
(def-fns _ $ (erased left-turn : (erased (Point) t p q r) (erased (LexLt t p) lp) (erased (XLe t q) xq) (erased (XLe t r) xr)
    (erased (Left t p q) l1) (erased (Left t q r) l2) -> (erased (Left t p r) l))
  (let-match erased xq (MkXLe tx ty qx qy gq aq))
  (let-match erased xr (MkXLe _ _ rx ry gr ar))
  (let-match erased lp (LexX _ _ px py ltp) (absurd (LexY _ _ py lty) (vh tx ty py qx qy gq lty aq l1)))
  (let ((erased gp1) (erased ap)) (lt-diff tx px ltp))
  (match erased (left-dec t p r) _
    ((OLeft _ _ _ l) l)
    (absurd (ORight _ _ _ l) (left-turn-absurd tx ty px py qx qy rx ry gp1 gq gr ap aq ar l1 l2 (left-weak p t r l)))
    (absurd (OOn _ _ _ c) (left-turn-absurd tx ty px py qx qy rx ry gp1 gq gr ap aq ar l1 l2 (coll-weak p t r $ coll-swap t p r c)))))

(def-fns _ $ (erased lex-trans : (erased (Point) p q r) (erased (LexLt p q) l1) (erased (LexLt q r) l2) -> (erased (LexLt p r) l))
  (match erased l1 _
    ((LexX px py qx qy a)
      (match erased l2 _
        ((LexX _ _ rx ry b) (LexX px py rx ry (lt-trans px qx rx a b)))
        ((LexY _ _ ry _) (LexX px py qx ry a))))
    ((LexY x py qy a)
      (match erased l2 _
        ((LexX _ _ rx ry b) (LexX x py rx ry b))
        ((LexY _ _ ry b) (LexY x py ry (lt-trans py qy ry a b)))))))

(def-fns _ $ (erased absurd lex-irrefl : (erased (Point) p) (erased (LexLt p p) l) -> (erased (False) f))
  (match erased l _
    (absurd (LexX px _ _ _ a) (lt-irrefl px a))
    (absurd (LexY _ py _ a) (lt-irrefl py a))))

(def-fns _ $ (erased absurd lex-cycle : (erased (Point) p q) (erased (LexLt p q) l1) (erased (LexLt q p) l2) -> (erased (False) f))
  (lex-irrefl p (lex-trans p q p l1 l2)))

(def-fns _ $ (erased absurd collinear-left : (erased (Point) p q r) (erased (Collinear p q r) c) (erased (Left p q r) l) -> (erased (False) f))
  (left-collinear p q r l c))

(def-fns _ $ (erased weak-same : (erased (Point) u v) -> (erased (Weak u v u) w))
  (coll-weak u v u (coll-same u v)))

(def-fns _ $ (erased weak-end : (erased (Point) u v) -> (erased (Weak u v v) w))
  (coll-weak u v v (coll-rot v u v (coll-same v u))))

(def-fns _ $ (erased weak-start : (erased (Point) u v) -> (erased (Weak v u u) w))
  (coll-weak v u u (coll-rot u v u (coll-same u v))))

; The cases of the sweep lemmas below; each rules out two segments crossing in its own configuration.
(def-fns _ $ (erased absurd geo-k1 : (erased (Point) a b c d p) (erased (LexLt a b) lab) (erased (LexLt c p) lcp) (erased (LexLt p d) lpd)
    (erased (Left a b c) l1) (erased (Left a b d) l2) (erased (Left b a p) l3) (erased (Left c d p) l4) -> (erased (False) f))
  (collinear-left c d p (sq-up a b c d p (lex-xle a b lab) (lex-xle c p lcp) (lex-xle p d lpd)
    (left-weak a b c l1) (left-weak a b d l2) (left-weak c d p l4) (left-weak b a p l3) (OrL _ _ l3)) l4))

(def-fns _ $ (erased absurd geo-k2 : (erased (Point) c d a b) (erased (LexLt c d) lcd) (erased (LexLt a c) lac) (erased (LexLt c b) lcb)
    (erased (Left c d a) l1) (erased (Left c d b) l2) (erased (Left a b c) l3) -> (erased (False) f))
  (collinear-left a b c (sq-up c d a b c (lex-xle c d lcd) (lex-xle a c lac) (lex-xle c b lcb)
    (left-weak c d a l1) (left-weak c d b l2) (left-weak a b c l3) (weak-start c d) (OrR _ _ (MkPair _ _ l1 l2))) l3))

(def-fns _ $ (erased absurd geo-k3 : (erased (Point) c d a b p) (erased (LexLt c d) lcd) (erased (LexLt a p) lap) (erased (LexLt p b) lpb)
    (erased (Left d c a) l1) (erased (Left d c b) l2) (erased (Left b a p) l3) (erased (Left c d p) l4) -> (erased (False) f))
  (collinear-left b a p (coll-swap a b p $ sq-down c d a b p (lex-xle c d lcd) (lex-xle a p lap) (lex-xle p b lpb)
    (left-weak d c a l1) (left-weak d c b l2) (left-weak b a p l3) (left-weak c d p l4) (OrL _ _ l4)) l3))

(def-fns _ $ (erased absurd geo-k4 : (erased (Point) a b c d) (erased (LexLt a b) lab) (erased (LexLt c a) lca) (erased (LexLt a d) lad)
    (erased (Left b a c) l1) (erased (Left b a d) l2) (erased (Left d c a) l3) -> (erased (False) f))
  (collinear-left d c a (coll-swap c d a $ sq-down a b c d a (lex-xle a b lab) (lex-xle c a lca) (lex-xle a d lad)
    (left-weak b a c l1) (left-weak b a d l2) (left-weak d c a l3) (weak-same a b) (OrR _ _ (MkPair _ _ l1 l2))) l3))

(def-fns _ $ (erased absurd geo-k5 : (erased (Point) c d a b) (erased (LexLt c d) lcd) (erased (LexLt a d) lad) (erased (LexLt d b) ldb)
    (erased (Left d c a) l1) (erased (Left d c b) l2) (erased (Left b a d) l3) -> (erased (False) f))
  (collinear-left b a d (coll-swap a b d $ sq-down c d a b d (lex-xle c d lcd) (lex-xle a d lad) (lex-xle d b ldb)
    (left-weak d c a l1) (left-weak d c b l2) (left-weak b a d l3) (weak-end c d) (OrR _ _ (MkPair _ _ l1 l2))) l3))

(def-fns _ $ (erased absurd geo-k6 : (erased (Point) a b c d) (erased (LexLt a b) lab) (erased (LexLt c b) lcb) (erased (LexLt b d) lbd)
    (erased (Left a b c) l1) (erased (Left a b d) l2) (erased (Left c d b) l3) -> (erased (False) f))
  (collinear-left c d b (sq-up a b c d b (lex-xle a b lab) (lex-xle c b lcb) (lex-xle b d lbd)
    (left-weak a b c l1) (left-weak a b d l2) (left-weak c d b l3) (coll-weak b a b (coll-same b a)) (OrR _ _ (MkPair _ _ l1 l2))) l3))

(def-fns _ $ (erased absurd geo-k7 : (erased (Point) a b c p) (erased (LexLt a b) lab) (erased (LexLt c p) lcp) (erased (LexLt p b) lpb)
    (erased (Left a b c) l1) (erased (Left c b p) l2) (erased (Left b a p) l3) -> (erased (False) f))
  (collinear-left c b p (sq-up a b c b p (lex-xle a b lab) (lex-xle c p lcp) (lex-xle p b lpb)
    (left-weak a b c l1) (weak-end a b) (left-weak c b p l2) (left-weak b a p l3) (OrL _ _ l3)) l2))

(def-fns _ $ (erased absurd geo-k8 : (erased (Point) a b c p) (erased (LexLt c b) lcb) (erased (LexLt a p) lap) (erased (LexLt p b) lpb)
    (erased (Left b c a) l1) (erased (Left b a p) l2) (erased (Left c b p) l3) -> (erased (False) f))
  (collinear-left b a p (coll-swap a b p $ sq-down c b a b p (lex-xle c b lcb) (lex-xle a p lap) (lex-xle p b lpb)
    (left-weak b c a l1) (coll-weak b c b (coll-same b c)) (left-weak b a p l2) (left-weak c b p l3) (OrL _ _ l3)) l2))

(def-fns _ $ (erased absurd geo-k9 : (erased (Point) a b d p) (erased (LexLt a b) lab) (erased (LexLt a p) lap) (erased (LexLt p d) lpd)
    (erased (Left a b d) l1) (erased (Left b a p) l2) (erased (Left a d p) l3) -> (erased (False) f))
  (collinear-left a d p (sq-up a b a d p (lex-xle a b lab) (lex-xle a p lap) (lex-xle p d lpd)
    (weak-same a b) (left-weak a b d l1) (left-weak a d p l3) (left-weak b a p l2) (OrL _ _ l2)) l3))

; Along the sweep line through any point both segments cross, ab is below cd. Each segment runs from its
; lexicographically smaller end.
(def-adts $ (Below : ((Edge) e) ((Edge) f) -> Type)
  enum
  (many BelowL : (erased (Point) a b c d) (erased (LexLt a c) l) (erased (Left a b c) h) -> (Below (MkEdge a b) (MkEdge c d)))
  (many BelowR : (erased (Point) a b c d) (erased (LexLt c a) l) (erased (Left d c a) h) -> (Below (MkEdge a b) (MkEdge c d)))
  (many BelowS : (erased (Point) a b d) (erased (Left a b d) h) -> (Below (MkEdge a b) (MkEdge a d))))

; A point p met by the sweep is never below a segment and above a higher one.
(def-fns _ $ (erased absurd sweep-under-over : (erased (Point) a b c d p) (erased (Below (MkEdge a b) (MkEdge c d)) bl)
    (erased (Compatible a b c d) cp) (erased (LexLt a b) lab) (erased (LexLt c d) lcd) (erased (LexLt a p) lap) (erased (LexLt p b) lpb)
    (erased (LexLt c p) lcp) (erased (LexLt p d) lpd) (erased (Left b a p) under) (erased (Left c d p) over) -> (erased (False) f))
  (match erased bl _
    (absurd (BelowL _ _ _ _ lac h)
      (match erased cp _
        (absurd (ShareCA _ _ _ _) (lex-irrefl a lac))
        (absurd (ShareCB _ _ _ _) (lex-cycle b p lcp lpb))
        (absurd (ShareDA _ _ _ _) (lex-cycle a c lac lcd))
        (absurd (ShareDB _ _ _ _) (geo-k7 a b c p lab lcp lpb h over under))
        (absurd (SplitByAB _ _ _ _ ss _ _)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ _ ld) (geo-k1 a b c d p lab lcp lpd h ld under over))
            (absurd (BothRight _ _ _ _ lc _) (left-antisym a b c h lc))))
        (absurd (SplitByCD _ _ _ _ _ od ss)
          (match erased od _
            (absurd (OffLeft _ _ _ ld) (geo-k1 a b c d p lab lcp lpd h ld under over))
            (absurd (OffRight _ _ _ _)
              (match erased ss _
                (absurd (BothLeft _ _ _ _ la lb) (geo-k2 c d a b lcd lac (lex-trans c p b lcp lpb) la lb h))
                (absurd (BothRight _ _ _ _ la lb) (geo-k3 c d a b p lcd lap lpb la lb under over))))))))
    (absurd (BelowR _ _ _ _ lca h)
      (match erased cp _
        (absurd (ShareCA _ _ _ _) (lex-irrefl a lca))
        (absurd (ShareCB _ _ _ _) (lex-cycle b a lca lab))
        (absurd (ShareDA _ _ _ _) (lex-cycle a p lap lpd))
        (absurd (ShareDB _ _ _ _) (geo-k8 a b c p lcd lap lpb h under over))
        (absurd (SplitByAB _ _ _ _ ss _ ob)
          (match erased ob _
            (absurd (OffRight _ _ _ lb) (geo-k3 c d a b p lcd lap lpb h lb under over))
            (absurd (OffLeft _ _ _ _)
              (match erased ss _
                (absurd (BothLeft _ _ _ _ lc ld) (geo-k1 a b c d p lab lcp lpd lc ld under over))
                (absurd (BothRight _ _ _ _ lc ld) (geo-k4 a b c d lab lca (lex-trans a p d lap lpd) lc ld h))))))
        (absurd (SplitByCD _ _ _ _ _ _ ss)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ la _) (left-antisym c d a la h))
            (absurd (BothRight _ _ _ _ _ lb) (geo-k3 c d a b p lcd lap lpb h lb under over))))))
    (absurd (BelowS _ _ _ h) (geo-k9 a b d p lab lap lpd h under over))))

; A segment ending at a point of the other's span ends above it, when the other is below.
(def-fns _ $ (erased absurd sweep-end-under : (erased (Point) a b c d) (erased (Below (MkEdge a b) (MkEdge c d)) bl)
    (erased (Compatible a b c d) cp) (erased (LexLt c d) lcd) (erased (LexLt a d) lad) (erased (LexLt d b) ldb)
    (erased (Left b a d) under) -> (erased (False) f))
  (match erased bl _
    (absurd (BelowL _ _ _ _ lac h)
      (match erased cp _
        (absurd (ShareCA _ _ _ _) (lex-irrefl a lac))
        (absurd (ShareCB _ _ _ _) (lex-cycle b d lcd ldb))
        (absurd (ShareDA _ _ _ _) (lex-irrefl a lad))
        (absurd (ShareDB _ _ _ _) (lex-irrefl b ldb))
        (absurd (SplitByAB _ _ _ _ ss _ _)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ _ ld) (left-antisym a b d ld under))
            (absurd (BothRight _ _ _ _ lc _) (left-antisym a b c h lc))))
        (absurd (SplitByCD _ _ _ _ _ _ ss)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ la lb) (geo-k2 c d a b lcd lac (lex-trans c d b lcd ldb) la lb h))
            (absurd (BothRight _ _ _ _ la lb) (geo-k5 c d a b lcd lad ldb la lb under))))))
    (absurd (BelowR _ _ _ _ lca h)
      (match erased cp _
        (absurd (ShareCA _ _ _ _) (lex-irrefl a lca))
        (absurd (ShareCB _ _ _ _) (lex-cycle b d (lex-trans b a d lca lad) ldb))
        (absurd (ShareDA _ _ _ _) (lex-irrefl a lad))
        (absurd (ShareDB _ _ _ _) (lex-irrefl b ldb))
        (absurd (SplitByAB _ _ _ _ ss _ _)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ _ ld) (left-antisym a b d ld under))
            (absurd (BothRight _ _ _ _ lc ld) (geo-k4 a b c d (lex-trans a d b lad ldb) lca lad lc ld h))))
        (absurd (SplitByCD _ _ _ _ _ _ ss)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ la _) (left-antisym c d a la h))
            (absurd (BothRight _ _ _ _ la lb) (geo-k5 c d a b lcd lad ldb la lb under))))))
    (absurd (BelowS _ _ _ h) (left-antisym a b d h under))))

; A segment ending at a point of the other's span ends below it, when the other is above.
(def-fns _ $ (erased absurd sweep-end-over : (erased (Point) a b c d) (erased (Below (MkEdge a b) (MkEdge c d)) bl)
    (erased (Compatible a b c d) cp) (erased (LexLt a b) lab) (erased (LexLt c b) lcb) (erased (LexLt b d) lbd)
    (erased (Left c d b) over) -> (erased (False) f))
  (match erased bl _
    (absurd (BelowL _ _ _ _ lac h)
      (match erased cp _
        (absurd (ShareCA _ _ _ _) (lex-irrefl a lac))
        (absurd (ShareCB _ _ _ _) (lex-irrefl b lcb))
        (absurd (ShareDA _ _ _ _) (lex-cycle a b lab lbd))
        (absurd (ShareDB _ _ _ _) (lex-irrefl b lbd))
        (absurd (SplitByAB _ _ _ _ ss _ _)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ lc ld) (geo-k6 a b c d lab lcb lbd lc ld over))
            (absurd (BothRight _ _ _ _ lc _) (left-antisym a b c h lc))))
        (absurd (SplitByCD _ _ _ _ _ _ ss)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ la lb) (geo-k2 c d a b (lex-trans c b d lcb lbd) lac lcb la lb h))
            (absurd (BothRight _ _ _ _ _ lb) (left-antisym c d b over lb))))))
    (absurd (BelowR _ _ _ _ lca h)
      (match erased cp _
        (absurd (ShareCA _ _ _ _) (lex-irrefl a lca))
        (absurd (ShareCB _ _ _ _) (lex-irrefl b lcb))
        (absurd (ShareDA _ _ _ _) (lex-cycle a b lab lbd))
        (absurd (ShareDB _ _ _ _) (lex-irrefl b lbd))
        (absurd (SplitByAB _ _ _ _ ss _ _)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ lc ld) (geo-k6 a b c d lab lcb lbd lc ld over))
            (absurd (BothRight _ _ _ _ lc ld) (geo-k4 a b c d lab lca (lex-trans a b d lab lbd) lc ld h))))
        (absurd (SplitByCD _ _ _ _ _ _ ss)
          (match erased ss _
            (absurd (BothLeft _ _ _ _ la _) (left-antisym c d a la h))
            (absurd (BothRight _ _ _ _ _ lb) (left-antisym c d b over lb))))))
    (absurd (BelowS _ _ _ h) (left-antisym _ _ _ h (left-rot _ _ _ $ left-rot _ _ _ over)))))
