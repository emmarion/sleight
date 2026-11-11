(def-adts $ (QPoint : -> Type)
  enum
  (many MkQPoint : (many (Q) x) (many (Q) y) -> (QPoint)))

(def-adts $ (Shoe : (Type T) ((TyCtor (T a) (T b) (T c) -> Type) M) ((TyCtor (T a) (T b) (T c) -> Type) A)
    (T px) (T py) (T qx) (T qy) (T rx) (T ry) (T s) -> Type)
  enum
  (many MkShoe : (erased Type T) (erased (TyCtor (T a) (T b) (T c) -> Type) M A) (erased T px py qx qy rx ry m1 m2 m3 m12 s)
      (erased (M px qy m1) p1) (erased (M qx ry m2) p2) (erased (M rx py m3) p3) (erased (A m1 m2 m12) q1) (erased (A m12 m3 s) q2)
      -> (Shoe T M A px py qx qy rx ry s)))

(def-adts $ (QShoelace : ((QPoint) p) ((QPoint) q) ((QPoint) r) ((Q) s) -> Type)
  enum
  (many MkQShoelace : (erased (Q) px py qx qy rx ry s) (erased (Shoe (Q) QMult QPlus px py qx qy rx ry s) h)
      -> (QShoelace (MkQPoint px py) (MkQPoint qx qy) (MkQPoint rx ry) s)))

(def-adts $ (QLeft : ((QPoint) p) ((QPoint) q) ((QPoint) r) -> Type)
  enum
  (many MkQLeft : (erased (QPoint) p q r) (erased (Q) s1 s2)
      (erased (QShoelace p q r s1) h1) (erased (QShoelace r q p s2) h2) (erased (QLt s2 s1) l)
      -> (QLeft p q r)))

(def-adts $ (QPointApart : ((QPoint) p) ((QPoint) q) -> Type)
  enum
  (many QApartX : (erased (Q) px py qx qy) (erased (Apart (Q) QLt px qx) d) -> (QPointApart (MkQPoint px py) (MkQPoint qx qy)))
  (many QApartY : (erased (Q) px py qx qy) (erased (Apart (Q) QLt py qy) d) -> (QPointApart (MkQPoint px py) (MkQPoint qx qy))))

(def-adts $ (QScaled : ((Z) k) ((Q) x) ((Z) w) -> Type)
  enum
  (many MkQScaled : (erased (Z) k n w t) (erased (Nat) d) (erased (ZMul n k t) h1) (erased (ZMul w (Zpos d) t) h2)
      -> (QScaled k (Qmake n d) w)))

(def-adts $ (Grid : -> Type)
  enum
  (many MkGrid : (many (Nat) k) (many (Z) o) -> (Grid)))

(def-adts $ (GridAt : ((Grid) g) ((Q) x) ((Nat) n) -> Type)
  enum
  (many MkGridAt : (erased (Nat) k n) (erased (Z) o w z) (erased (Q) x)
      (erased (QScaled (Zpos k) x w) s) (erased (ZAdd w o z) h) (erased (ZView z n (Zero)) v)
      -> (GridAt (MkGrid k o) x n)))

(def-adts $ (OnGrid : ((Grid) g) ((QPoint) q) ((Point) n) -> Type)
  enum
  (many MkOnGrid : (erased (Grid) g) (erased (Q) x y) (erased (Nat) nx ny) (erased (GridAt g x nx) hx) (erased (GridAt g y ny) hy)
      -> (OnGrid g (MkQPoint x y) (MkPoint nx ny))))

(def-adts $ (GridList : ((Grid) g) ((List (QPoint)) qs) ((List (Point)) ns) -> Type)
  enum
  (many GridNil : (erased (Grid) g) -> (GridList g (Nil (QPoint)) (Nil (Point))))
  (many GridCons : (erased (Grid) g) (erased (QPoint) q) (erased (Point) n) (erased (List (QPoint)) qs) (erased (List (Point)) ns)
      (erased (OnGrid g q n) h) (erased (GridList g qs ns) rest)
      -> (GridList g (Cons (QPoint) q qs) (Cons (Point) n ns))))

(comptime-match many (zring-check (ZEMul (ZEMul (zvar 0) (zvar 1)) (ZEMul (zvar 2) (zvar 3))) (ZEMul (ZEMul (zvar 0) (zvar 2)) (ZEMul (zvar 1) (zvar 3))))
  (Some _ zr-grid-mul))

(def-fns _ $ (erased qscaled-mul : (erased (Z) k1 k2 k w1 w2 w) (erased (Q) x y z) (erased (QScaled k1 x w1) s1) (erased (QScaled k2 y w2) s2)
    (erased (QMult x y z) h) (erased (ZMul k1 k2 k) hk) (erased (ZMul w1 w2 w) hw) -> (erased (QScaled k z w) s))
  (let-match erased s1 (MkQScaled _ n1 _ t1 d1 a1 b1))
  (let-match erased s2 (MkQScaled _ n2 _ t2 d2 a2 b2))
  (let-match erased h (MkQMult _ _ n _ _ d hn hd))
  (let ((erased t) (erased ht)) (zmul t1 t2))
  (let ((erased u) (erased hu)) (zmul n k))
  (let ((erased v) (erased hv)) (zmul w (Zpos d)))
  (let-match erased (zring-sound (Cons _ n1 $ Cons _ n2 $ Cons _ k1 $ Cons _ k2 $ Nil (Z)) _ _ u t zr-grid-mul
    (zev-mul (zev-mul (zev-var 0) (zev-var 1) hn) (zev-mul (zev-var 2) (zev-var 3) hk) hu)
    (zev-mul (zev-mul (zev-var 0) (zev-var 2) a1) (zev-mul (zev-var 1) (zev-var 3) a2) ht)) (Refl _ _))
  (let-match erased (zring-sound (Cons _ w1 $ Cons _ w2 $ Cons _ (Zpos d1) $ Cons _ (Zpos d2) $ Nil (Z)) _ _ v t zr-grid-mul
    (zev-mul (zev-mul (zev-var 0) (zev-var 1) hw) (zev-mul (zev-var 2) (zev-var 3) hd) hv)
    (zev-mul (zev-mul (zev-var 0) (zev-var 2) b1) (zev-mul (zev-var 1) (zev-var 3) b2) ht)) (Refl _ _))
  (MkQScaled k n w u d hu hv))

(comptime-match many (zring-check (ZEMul (ZEAdd (ZEMul (zvar 0) (zvar 3)) (ZEMul (zvar 1) (zvar 2))) (zvar 4))
    (ZEAdd (ZEMul (ZEMul (zvar 0) (zvar 4)) (zvar 3)) (ZEMul (ZEMul (zvar 1) (zvar 4)) (zvar 2))))
  (Some _ zr-grid-plus-l))

(comptime-match many (zring-check (ZEMul (ZEAdd (zvar 0) (zvar 1)) (ZEMul (zvar 2) (zvar 3)))
    (ZEAdd (ZEMul (ZEMul (zvar 0) (zvar 2)) (zvar 3)) (ZEMul (ZEMul (zvar 1) (zvar 3)) (zvar 2))))
  (Some _ zr-grid-plus-r))

(def-fns _ $ (erased qscaled-plus : (erased (Z) k w1 w2 w) (erased (Q) x y z) (erased (QScaled k x w1) s1) (erased (QScaled k y w2) s2)
    (erased (QPlus x y z) h) (erased (ZAdd w1 w2 w) hw) -> (erased (QScaled k z w) s))
  (let-match erased s1 (MkQScaled _ n1 _ t1 d1 a1 b1))
  (let-match erased s2 (MkQScaled _ n2 _ t2 d2 a2 b2))
  (let-match erased h (MkQPlus _ _ l r n _ _ d hl hr hn hd))
  (let ((erased p1) (erased hp1)) (zmul t1 (Zpos d2)))
  (let ((erased p2) (erased hp2)) (zmul t2 (Zpos d1)))
  (let ((erased p) (erased hp)) (zadd p1 p2))
  (let ((erased u) (erased hu)) (zmul n k))
  (let ((erased v) (erased hv)) (zmul w (Zpos d)))
  (let-match erased (zring-sound (Cons _ n1 $ Cons _ n2 $ Cons _ (Zpos d1) $ Cons _ (Zpos d2) $ Cons _ k $ Nil (Z)) _ _ u p zr-grid-plus-l
    (zev-mul (zev-add (zev-mul (zev-var 0) (zev-var 3) hl) (zev-mul (zev-var 1) (zev-var 2) hr) hn) (zev-var 4) hu)
    (zev-add (zev-mul (zev-mul (zev-var 0) (zev-var 4) a1) (zev-var 3) hp1) (zev-mul (zev-mul (zev-var 1) (zev-var 4) a2) (zev-var 2) hp2) hp)) (Refl _ _))
  (let-match erased (zring-sound (Cons _ w1 $ Cons _ w2 $ Cons _ (Zpos d1) $ Cons _ (Zpos d2) $ Nil (Z)) _ _ v p zr-grid-plus-r
    (zev-mul (zev-add (zev-var 0) (zev-var 1) hw) (zev-mul (zev-var 2) (zev-var 3) hd) hv)
    (zev-add (zev-mul (zev-mul (zev-var 0) (zev-var 2) b1) (zev-var 3) hp1) (zev-mul (zev-mul (zev-var 1) (zev-var 3) b2) (zev-var 2) hp2) hp)) (Refl _ _))
  (MkQScaled k n w u d hu hv))

(comptime-match many (zring-check (ZEMul (ZEMul (zvar 0) (zvar 1)) (zvar 2)) (ZEMul (ZEMul (zvar 0) (zvar 2)) (zvar 1))) (Some _ zr-grid-rot))

(def-fns _ $ (erased zmul-rot : (erased (Z) a b c ab x ac y) (erased (ZMul a b ab) h1) (erased (ZMul ab c x) h2) (erased (ZMul a c ac) h3)
    (erased (ZMul ac b y) h4) -> (erased (Eq (Z) x y) e))
  (zring-sound (Cons _ a $ Cons _ b $ Cons _ c $ Nil (Z)) _ _ x y zr-grid-rot
    (zev-mul (zev-mul (zev-var 0) (zev-var 1) h1) (zev-var 2) h2) (zev-mul (zev-mul (zev-var 0) (zev-var 2) h3) (zev-var 1) h4)))

(def-fns _ $ (erased qscaled-lt : (erased (Z) k w1 w2) (erased (Q) x y) (erased (ZLt (Z0) k) hk) (erased (QScaled k x w1) s1) (erased (QScaled k y w2) s2)
    (erased (QLt x y) h) -> (erased (ZLt w1 w2) r))
  (let-match erased s1 (MkQScaled _ n1 _ t1 d1 a1 b1))
  (let-match erased s2 (MkQScaled _ n2 _ t2 d2 a2 b2))
  (let-match erased h (MkQLt _ _ l r _ _ hl hr lt))
  (let ((erased lk) (erased hlk)) (zmul l k))
  (let ((erased rk) (erased hrk)) (zmul r k))
  (let ((erased x1) (erased hx1)) (zmul t1 (Zpos d2)))
  (let ((erased y1) (erased hy1)) (zmul t2 (Zpos d1)))
  (let ((erased u) (erased hu)) (zmul w2 (Zpos d1)))
  (let ((erased y2) (erased hy2)) (zmul u (Zpos d2)))
  (let-match erased (zmul-rot n1 (Zpos d2) k l lk t1 x1 hl hlk a1 hx1) (Refl _ _))
  (let-match erased (zmul-rot n2 (Zpos d1) k r rk t2 y1 hr hrk a2 hy1) (Refl _ _))
  (let-match erased (zmul-rot w2 (Zpos d2) (Zpos d1) t2 y1 u y2 b2 hy1 hu hy2) (Refl _ _))
  (let ((erased lt2)) (zmul-lt-mono-pos-r l r k lk rk hk lt hlk hrk))
  (zmul-lt-reg-r w1 w2 (Zpos d1) t1 u (zpos-is-pos d1) b1 hu (zmul-lt-reg-r t1 u (Zpos d2) lk rk (zpos-is-pos d2) hx1 hy2 lt2)))

(def-macro (zshoe args)
  (let-match many args (Cons _ a r1) (else (qq (compile-error "`zshoe` takes six expressions"))))
  (let-match many r1 (Cons _ b r2) (else (qq (compile-error "`zshoe` takes six expressions"))))
  (let-match many r2 (Cons _ c r3) (else (qq (compile-error "`zshoe` takes six expressions"))))
  (let-match many r3 (Cons _ d r4) (else (qq (compile-error "`zshoe` takes six expressions"))))
  (let-match many r4 (Cons _ e r5) (else (qq (compile-error "`zshoe` takes six expressions"))))
  (let-match many r5 (Cons _ f _) (else (qq (compile-error "`zshoe` takes six expressions"))))
  (qq (ZEAdd (ZEAdd (ZEMul (~ a) (~ d)) (ZEMul (~ c) (~ f))) (ZEMul (~ e) (~ b)))))

(def-fns _ $ (erased zshoe-ev : (erased (List (Z)) env) (erased (ZExpr) e1 e2 e3 e4 e5 e6) (erased (Z) z1 z2 z3 z4 z5 z6 s)
    (erased (ZEval env e1 z1) v1) (erased (ZEval env e2 z2) v2) (erased (ZEval env e3 z3) v3) (erased (ZEval env e4 z4) v4)
    (erased (ZEval env e5 z5) v5) (erased (ZEval env e6 z6) v6) (erased (Shoe (Z) ZMul ZAdd z1 z2 z3 z4 z5 z6 s) h) ->
    (erased (ZEval env (zshoe e1 e2 e3 e4 e5 e6) s) v))
  (let-match erased h (MkShoe _ _ _ _ _ _ _ _ _ m1 m2 m3 m12 _ p1 p2 p3 q1 q2))
  (zev-add (zev-add (zev-mul v1 v4 p1) (zev-mul v3 v6 p2) q1) (zev-mul v5 v2 p3) q2))

(def-fns _ $ (erased qshoe-scaled : (erased (Z) k kk w1 w2 w3 w4 w5 w6) (erased (Q) x1 x2 x3 x4 x5 x6 s)
    (erased (Shoe (Q) QMult QPlus x1 x2 x3 x4 x5 x6 s) h) (erased (ZMul k k kk) hk)
    (erased (QScaled k x1 w1) a1) (erased (QScaled k x2 w2) a2) (erased (QScaled k x3 w3) a3)
    (erased (QScaled k x4 w4) a4) (erased (QScaled k x5 w5) a5) (erased (QScaled k x6 w6) a6) ->
    (erased (Z) t) (erased (Shoe (Z) ZMul ZAdd w1 w2 w3 w4 w5 w6 t) g) (erased (QScaled kk s t) b))
  (let-match erased h (MkShoe _ _ _ _ _ _ _ _ _ m1 m2 m3 m12 _ p1 p2 p3 q1 q2))
  (let ((erased n1) (erased h1)) (zmul w1 w4))
  (let ((erased n2) (erased h2)) (zmul w3 w6))
  (let ((erased n3) (erased h3)) (zmul w5 w2))
  (let ((erased n12) (erased h12)) (zadd n1 n2))
  (let ((erased t) (erased ht)) (zadd n12 n3))
  (values t (MkShoe _ _ _ w1 w2 w3 w4 w5 w6 n1 n2 n3 n12 t h1 h2 h3 h12 ht)
    (qscaled-plus kk n12 n3 t m12 m3 s
      (qscaled-plus kk n1 n2 n12 m1 m2 m12 (qscaled-mul k k kk w1 w4 n1 x1 x4 m1 a1 a4 p1 hk h1) (qscaled-mul k k kk w3 w6 n2 x3 x6 m2 a3 a6 p2 hk h2) q1 h12)
      (qscaled-mul k k kk w5 w2 n3 x5 x2 m3 a5 a2 p3 hk h3) q2 ht)))

(def-fns _ $ (erased shoe-znat : (erased (Nat) ax ay bx by cx cy s) (erased (Z) z1 z2 z3 z4 z5 z6)
    (erased (Shoelace (MkPoint ax ay) (MkPoint bx by) (MkPoint cx cy) s) h)
    (erased (ZView z1 ax (Zero)) v1) (erased (ZView z2 ay (Zero)) v2) (erased (ZView z3 bx (Zero)) v3)
    (erased (ZView z4 by (Zero)) v4) (erased (ZView z5 cx (Zero)) v5) (erased (ZView z6 cy (Zero)) v6) ->
    (erased (Z) t) (erased (Shoe (Z) ZMul ZAdd z1 z2 z3 z4 z5 z6 t) g) (erased (ZView t s (Zero)) v))
  (let-match erased h (MkShoelace _ _ _ _ _ _ m1 m2 m3 m12 _ p1 p2 p3 q1 q2))
  (let ((erased n1) (erased h1)) (zmul z1 z4))
  (let ((erased n2) (erased h2)) (zmul z3 z6))
  (let ((erased n3) (erased h3)) (zmul z5 z2))
  (let ((erased n12) (erased h12)) (zadd n1 n2))
  (let ((erased t) (erased ht)) (zadd n12 n3))
  (let ((erased u1)) (znat-mul z1 z4 n1 ax by m1 v1 v4 h1 p1))
  (let ((erased u2)) (znat-mul z3 z6 n2 bx cy m2 v3 v6 h2 p2))
  (let ((erased u3)) (znat-mul z5 z2 n3 cx ay m3 v5 v2 h3 p3))
  (values t (MkShoe _ _ _ z1 z2 z3 z4 z5 z6 n1 n2 n3 n12 t h1 h2 h3 h12 ht)
    (znat-add n12 n3 t m12 m3 s (znat-add n1 n2 n12 m1 m2 m12 u1 u2 h12 q1) u3 ht q2)))

(comptime-match many (zring-check
    (ZEAdd (zshoe (ZEAdd (zvar 0) (zvar 6)) (ZEAdd (zvar 1) (zvar 6)) (ZEAdd (zvar 2) (zvar 6)) (ZEAdd (zvar 3) (zvar 6)) (ZEAdd (zvar 4) (zvar 6)) (ZEAdd (zvar 5) (zvar 6)))
      (zshoe (zvar 4) (zvar 5) (zvar 2) (zvar 3) (zvar 0) (zvar 1)))
    (ZEAdd (zshoe (ZEAdd (zvar 4) (zvar 6)) (ZEAdd (zvar 5) (zvar 6)) (ZEAdd (zvar 2) (zvar 6)) (ZEAdd (zvar 3) (zvar 6)) (ZEAdd (zvar 0) (zvar 6)) (ZEAdd (zvar 1) (zvar 6)))
      (zshoe (zvar 0) (zvar 1) (zvar 2) (zvar 3) (zvar 4) (zvar 5))))
  (Some _ zr-grid-shoe))

(def-fns _ $ (erased zlt-znat : (erased (Z) a b) (erased (Nat) n m) (erased (ZView a n (Zero)) va) (erased (ZView b m (Zero)) vb) (erased (ZLt a b) h)
    -> (erased (Lt n m) r))
  (let-match erased h (MkZLt _ _ pa qa pb qb l r wa wb hl hr lt))
  (let ((erased e1) (erased e2)) (zview-fn a pa qa n (Zero) wa va))
  (let ((erased e3) (erased e4)) (zview-fn b pb qb m (Zero) wb vb))
  (let-match erased e1 (Refl _ _))
  (let-match erased e2 (Refl _ _))
  (let-match erased e3 (Refl _ _))
  (let-match erased e4 (Refl _ _))
  (let-match erased (add-fn n (Zero) l n hl (add-zero-right n)) (Refl _ _))
  (let-match erased (add-fn m (Zero) r m hr (add-zero-right m)) (Refl _ _))
  lt)

(def-fns _ $ (erased gridat-fn : (erased (Grid) g) (erased (Q) x) (erased (Nat) n m) (erased (GridAt g x n) h1) (erased (GridAt g x m) h2)
    -> (erased (Eq (Nat) n m) e))
  (let-match erased h1 (MkGridAt k _ o w z _ s a v))
  (let-match erased h2 (MkGridAt _ _ _ w2 z2 _ s2 a2 v2))
  (let-match erased s (MkQScaled _ nx _ t d b c))
  (let-match erased s2 (MkQScaled _ _ _ t2 _ b2 c2))
  (let-match erased (zmul-fn _ _ _ _ b b2) (Refl _ _))
  (let-match erased (zmul-reg-r w w2 (Zpos d) t (zpos-is-pos d) c c2) (Refl _ _))
  (let-match erased (zadd-fn _ _ _ _ a a2) (Refl _ _))
  (let ((erased e) (erased _)) (zview-fn z n (Zero) m (Zero) v v2))
  e)

(def-fns _ $ (erased grid-fn : (erased (Grid) g) (erased (QPoint) q) (erased (Point) n m) (erased (OnGrid g q n) h1) (erased (OnGrid g q m) h2)
    -> (erased (Eq (Point) n m) e))
  (let-match erased h1 (MkOnGrid _ x y nx ny gx gy))
  (let-match erased h2 (MkOnGrid _ _ _ mx my fx fy))
  (let-match erased (gridat-fn g x nx mx gx fx) (Refl _ _))
  (let-match erased (gridat-fn g y ny my gy fy) (Refl _ _))
  (Refl _ n))

(def-fns _ $ (erased grid-lt : (erased (Grid) g) (erased (Q) x y) (erased (Nat) n m) (erased (GridAt g x n) h1) (erased (GridAt g y m) h2)
    (erased (QLt x y) lt) -> (erased (Lt n m) r))
  (let-match erased h1 (MkGridAt k _ o w z _ s a v))
  (let-match erased h2 (MkGridAt _ _ _ w2 z2 _ s2 a2 v2))
  (zlt-znat z z2 n m v v2 (zadd-lt-mono-r w w2 o z z2 (qscaled-lt (Zpos k) w w2 x y (zpos-is-pos k) s s2 lt) a a2)))

(def-fns _ $ (erased gridat-apart : (erased (Grid) g) (erased (Q) x y) (erased (Nat) n m) (erased (GridAt g x n) h1) (erased (GridAt g y m) h2)
    (erased (Apart (Q) QLt x y) d) -> (erased (Apart (Nat) Lt n m) r))
  (match erased d _
    ((ApLt _ _ _ _ lt) (ApLt _ _ n m (grid-lt g x y n m h1 h2 lt)))
    ((ApGt _ _ _ _ gt) (ApGt _ _ n m (grid-lt g y x m n h2 h1 gt)))))

(def-fns _ $ (erased grid-apart : (erased (Grid) g) (erased (QPoint) p q) (erased (Point) a b) (erased (OnGrid g p a) ha) (erased (OnGrid g q b) hb)
    (erased (QPointApart p q) d) -> (erased (PointApart a b) r))
  (let-match erased ha (MkOnGrid _ px py ax ay gx gy))
  (let-match erased hb (MkOnGrid _ qx qy bx by fx fy))
  (match erased d _
    ((QApartX _ _ _ _ e) (ApartX ax ay bx by (gridat-apart g px qx ax bx gx fx e)))
    ((QApartY _ _ _ _ e) (ApartY ax ay bx by (gridat-apart g py qy ay by gy fy e)))))

(def-fns _ $ (erased grid-left : (erased (Grid) g) (erased (QPoint) p q r) (erased (Point) a b c)
    (erased (OnGrid g p a) ha) (erased (OnGrid g q b) hb) (erased (OnGrid g r c) hc) (erased (QLeft p q r) l) -> (erased (Left a b c) m))
  (let-match erased ha (MkOnGrid _ x1 x2 ax ay g1 g2))
  (let-match erased hb (MkOnGrid _ x3 x4 bx by g3 g4))
  (let-match erased hc (MkOnGrid _ x5 x6 cx cy g5 g6))
  (let-match erased g1 (MkGridAt k _ o w1 z1 _ s1 e1 v1))
  (let-match erased g2 (MkGridAt _ _ _ w2 z2 _ s2 e2 v2))
  (let-match erased g3 (MkGridAt _ _ _ w3 z3 _ s3 e3 v3))
  (let-match erased g4 (MkGridAt _ _ _ w4 z4 _ s4 e4 v4))
  (let-match erased g5 (MkGridAt _ _ _ w5 z5 _ s5 e5 v5))
  (let-match erased g6 (MkGridAt _ _ _ w6 z6 _ s6 e6 v6))
  (let-match erased l (MkQLeft _ _ _ t1 t2 h1 h2 lt))
  (let-match erased h1 (MkQShoelace _ _ _ _ _ _ _ sh1))
  (let-match erased h2 (MkQShoelace _ _ _ _ _ _ _ sh2))
  (let ((erased kk) (erased hk)) (zpos-mul k k))
  (let ((erased u1) (erased y1) (erased b1)) (qshoe-scaled (Zpos k) (Zpos kk) w1 w2 w3 w4 w5 w6 x1 x2 x3 x4 x5 x6 t1 sh1 hk s1 s2 s3 s4 s5 s6))
  (let ((erased u2) (erased y2) (erased b2)) (qshoe-scaled (Zpos k) (Zpos kk) w5 w6 w3 w4 w1 w2 x5 x6 x3 x4 x1 x2 t2 sh2 hk s5 s6 s3 s4 s1 s2))
  (let ((erased n1) (erased f1)) (shoelace a b c))
  (let ((erased n2) (erased f2)) (shoelace c b a))
  (let ((erased T1) (erased Y1) (erased U1)) (shoe-znat ax ay bx by cx cy n1 z1 z2 z3 z4 z5 z6 f1 v1 v2 v3 v4 v5 v6))
  (let ((erased T2) (erased Y2) (erased U2)) (shoe-znat cx cy bx by ax ay n2 z5 z6 z3 z4 z1 z2 f2 v5 v6 v3 v4 v1 v2))
  (let ((erased env)) (Cons _ w1 $ Cons _ w2 $ Cons _ w3 $ Cons _ w4 $ Cons _ w5 $ Cons _ w6 $ Cons _ o $ Nil (Z)))
  (let-match erased (zring-r (OLt) env _ _ _ _ T1 T2 u2 u1 zr-grid-shoe
      (zshoe-ev env _ _ _ _ _ _ z1 z2 z3 z4 z5 z6 T1 (zev-add (zev-var 0) (zev-var 6) e1) (zev-add (zev-var 1) (zev-var 6) e2)
        (zev-add (zev-var 2) (zev-var 6) e3) (zev-add (zev-var 3) (zev-var 6) e4) (zev-add (zev-var 4) (zev-var 6) e5) (zev-add (zev-var 5) (zev-var 6) e6) Y1)
      (zshoe-ev env _ _ _ _ _ _ z5 z6 z3 z4 z1 z2 T2 (zev-add (zev-var 4) (zev-var 6) e5) (zev-add (zev-var 5) (zev-var 6) e6)
        (zev-add (zev-var 2) (zev-var 6) e3) (zev-add (zev-var 3) (zev-var 6) e4) (zev-add (zev-var 0) (zev-var 6) e1) (zev-add (zev-var 1) (zev-var 6) e2) Y2)
      (zshoe-ev env _ _ _ _ _ _ w5 w6 w3 w4 w1 w2 u2 (zev-var 4) (zev-var 5) (zev-var 2) (zev-var 3) (zev-var 0) (zev-var 1) y2)
      (zshoe-ev env _ _ _ _ _ _ w1 w2 w3 w4 w5 w6 u1 (zev-var 0) (zev-var 1) (zev-var 2) (zev-var 3) (zev-var 4) (zev-var 5) y1)
      (ZRLt _ _ (qscaled-lt (Zpos kk) u2 u1 t2 t1 (zpos-is-pos kk) b2 b1 lt)))
    (ZRLt _ _ ltT))
  (MkLeft a b c n1 n2 f1 f2 (zlt-znat T2 T1 n2 n1 U2 U1 ltT)))

(def-adts $ (ScaledList : ((Z) k) ((List (QPoint)) qs) ((Nat) s) -> Type)
  enum
  (many ScaledNil : (erased (Z) k) -> (ScaledList k (Nil (QPoint)) (Zero)))
  (many ScaledCons : (erased (Z) k) (many (Z) wx wy) (erased (Q) x y) (erased (Nat) px qx py qy a sr s) (erased (List (QPoint)) qs)
      (erased (QScaled k x wx) hx) (erased (QScaled k y wy) hy) (erased (ZView wx px qx) vx) (erased (ZView wy py qy) vy)
      (erased (Add qx qy a) ha) (erased (Add a sr s) hs) (many (ScaledList k qs sr) rest)
      -> (ScaledList k (Cons (QPoint) (MkQPoint x y) qs) s)))

(comptime-match many (zring-check (ZEMul (zvar 0) (ZEMul (zvar 1) (ZEMul (ZEMul (zvar 2) (zvar 3)) (zvar 4))))
    (ZEMul (ZEMul (zvar 0) (ZEMul (zvar 1) (ZEMul (zvar 3) (zvar 4)))) (zvar 2)))
  (Some _ zr-grid-coord))

(def-fns _ $ (many grid-coord : (many (Z) c n) (erased (Nat) d) (many (Nat) d2 pr2) (erased (Nat) e pr) (erased (Z) k)
    (erased (ZMul (Zpos d) (Zpos d2) (Zpos e)) he) (erased (ZMul (Zpos e) (Zpos pr2) (Zpos pr)) hp) (erased (ZMul c (Zpos pr) k) hk) ->
    (many (Z) w) (erased (QScaled k (Qmake n d) w) s))
  (let ((many m) (erased hm)) (zmul (Zpos d2) (Zpos pr2)))
  (let ((many cx) (erased hc)) (zmul c m))
  (let ((many w) (erased hw)) (zmul n cx))
  (let ((erased t) (erased ht)) (zmul w (Zpos d)))
  (let ((erased u) (erased hu)) (zmul n k))
  (let-match erased (zring-sound (Cons _ n $ Cons _ c $ Cons _ (Zpos d) $ Cons _ (Zpos d2) $ Cons _ (Zpos pr2) $ Nil (Z)) _ _ u t zr-grid-coord
    (zev-mul (zev-var 0) (zev-mul (zev-var 1) (zev-mul (zev-mul (zev-var 2) (zev-var 3) he) (zev-var 4) hp) hk) hu)
    (zev-mul (zev-mul (zev-var 0) (zev-mul (zev-var 1) (zev-mul (zev-var 3) (zev-var 4) hm) hc) hw) (zev-var 2) ht)) (Refl _ _))
  (values w (MkQScaled k n w u d hu ht)))

(comptime-match many (zring-check (ZEMul (zvar 0) (ZEMul (zvar 1) (zvar 2))) (ZEMul (ZEMul (zvar 0) (zvar 1)) (zvar 2))) (Some _ zr-grid-assoc))

(def-fns _ $ (many grid-scale : (many (Z) c) (subterm many (List (QPoint)) qs) ->
    (many (Nat) pr) (erased (Z) k) (erased (ZMul c (Zpos pr) k) hk) (many (Nat) s) (many (ScaledList k qs s) h))
  (let-match many qs (Cons _ p rest) ((Nil _) (values (Zero) c (zmul-1-r c) (Zero) (ScaledNil c))))
  (let-match many p (MkQPoint x y))
  (let-match many x (Qmake nx dx))
  (let-match many y (Qmake ny dy))
  (let ((many e) (erased he)) (zpos-mul dx dy))
  (let ((many c2) (erased hc2)) (zmul c (Zpos e)))
  (let ((many pr2) (erased k) (erased hk2) (many s2) (many h2)) (notail $ grid-scale c2 rest))
  (let ((many pr) (erased hp)) (zpos-mul e pr2))
  (let ((erased k3) (erased hk3)) (zmul c (Zpos pr)))
  (let-match erased (zring-sound (Cons _ c $ Cons _ (Zpos e) $ Cons _ (Zpos pr2) $ Nil (Z)) _ _ k3 k zr-grid-assoc
    (zev-mul (zev-var 0) (zev-mul (zev-var 1) (zev-var 2) hp) hk3) (zev-mul (zev-mul (zev-var 0) (zev-var 1) hc2) (zev-var 2) hk2)) (Refl _ _))
  (let ((many wx) (erased sx)) (grid-coord c nx dx dy pr2 e pr k he hp hk3))
  (let ((many wy) (erased sy)) (grid-coord c ny dy dx pr2 e pr k (zmul-comm _ _ _ he) hp hk3))
  (let ((many px) (many qx) (erased vx)) (zview wx))
  (let ((many py) (many qy) (erased vy)) (zview wy))
  (let ((many a) (erased ha)) (add qx qy))
  (let ((many s) (erased hs)) (add a s2))
  (values pr k hk3 s (ScaledCons k wx wy x y px qx py qy a s2 s rest sx sy vx vy ha hs h2)))

(def-fns _ $ (many grid-at : (erased (Nat) k) (many (Nat) o) (erased (Z) zo) (erased (ZView zo o (Zero)) vo) (erased (Q) x) (many (Z) w)
    (erased (Nat) p q) (erased (QScaled (Zpos k) x w) s) (erased (ZView w p q) v) (erased (Lt q (Succ o)) le) ->
    (many (Nat) n) (erased (GridAt (MkGrid k zo) x n) h))
  (let ((many p2) (many q2) (erased v2)) (zview w))
  (let ((erased e1) (erased e2)) (zview-fn w p q p2 q2 v v2))
  (let-match erased e1 (Refl _ _))
  (let-match erased e2 (Refl _ _))
  (let ((many po) (erased hpo)) (add p2 o))
  (let ((many n) (erased hn)) (sub po q2 (lt-le-trans q (Succ o) (Succ po) le (LtS o (Succ po) (add-le-right p o po hpo)))))
  (let ((erased z) (erased hz)) (zadd w zo))
  (let ((erased oz)) (zadd-rep w zo z p q o (Zero) po q hz (zview-of w p q v) (zview-of zo o (Zero) vo) hpo (add-zero-right q)))
  (values n (MkGridAt k n zo w z x s hz
    (zof-nat-view z n (zof-rep z po q n (Zero) oz (MkDiffEq po q n (Zero) po (add-zero-right po) (add-comm q n po hn)))))))

(def-fns _ $ (many grid-place : (erased (Nat) k) (many (Nat) o) (erased (Z) zo) (erased (ZView zo o (Zero)) vo) (erased (List (QPoint)) qs)
    (erased (Nat) s) (subterm many (ScaledList (Zpos k) qs s) h) (erased (Lt s (Succ o)) le) ->
    (many (List (Point)) ns) (erased (GridList (MkGrid k zo) qs ns) r))
  (let-match many h (ScaledCons _ wx wy x y px qx py qy a sr _ qs1 sx sy vx vy ha hs rest) ((ScaledNil _) (values (Nil _) (GridNil _))))
  (let ((erased la)) (lt-le-trans a (Succ s) (Succ o) (add-le-left a sr s hs) (LtS s (Succ o) le)))
  (let ((many nx) (erased gx)) (grid-at k o zo vo x wx px qx sx vx (lt-le-trans qx (Succ a) (Succ o) (add-le-left qx qy a ha) (LtS a (Succ o) la))))
  (let ((many ny) (erased gy)) (grid-at k o zo vo y wy py qy sy vy (lt-le-trans qy (Succ a) (Succ o) (add-le-right qx qy a ha) (LtS a (Succ o) la))))
  (let ((many ns) (erased r))
    (notail $ grid-place k o zo vo qs1 sr rest (lt-le-trans sr (Succ s) (Succ o) (add-le-right a sr s hs) (LtS s (Succ o) le))))
  (values (Cons _ (MkPoint nx ny) ns) (GridCons _ _ _ _ _ (MkOnGrid _ x y nx ny gx gy) r)))

(def-fns _ $ (many grid-of : (many (List (QPoint)) qs) -> (many (Grid) g) (many (List (Point)) ns) (erased (GridList g qs ns) h))
  (let ((many pr) (erased k) (erased hk) (many s) (many h)) (grid-scale (Zpos (Zero)) qs))
  (let-match erased (zmul-fn _ _ _ _ hk (zmul-comm _ _ _ (zmul-1-r (Zpos pr)))) (Refl _ _))
  (let ((many zo) (erased vo)) (znat s))
  (let ((many ns) (erased r)) (grid-place pr s zo vo qs s h (lt-succ s)))
  (values (MkGrid pr zo) ns r))
