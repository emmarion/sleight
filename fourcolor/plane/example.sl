(def-adts $ (ConstSeq : ((Q) q) ((Z) n) ((Q) a) -> Type)
  enum
  (many MkConstSeq : (erased (Q) q) (erased (Z) n) -> (ConstSeq q n q)))

(def-macro (const-at args)
  (qq (MkSeqAt _ _ _ _ _ _ (MkConstSeq _ _))))

(def-fns _ $ (erased const-term : (erased (Q) q a) (erased (Z) scale n) (erased (SeqAt (MkSpec (Q) q ConstSeq scale) n a) h) ->
    (erased (Eq (Q) a q) e))
  (let-match erased h (MkSeqAt _ _ _ _ _ _ r))
  (let-match erased r (MkConstSeq _ _))
  (Refl _ q))

(comptime-match many (zring-check (ZEAdd (ZEMul (zvar 0) (zvar 1)) (ZEMul (ZEOpp (zvar 0)) (zvar 1))) (ZENum (Zero))) (Some _ zr-minus-self))

(def-fns _ $ (erased qminus-self : (erased (Q) x c) (erased (QMinus x x c) h) -> (erased (Nat) d) (erased (Eq (Q) c (Qmake (Z0) d)) e))
  (let-match erased h (MkQMinus _ _ o _ ho hp))
  (let-match erased ho (MkQOpp nx n dx hn))
  (let-match erased hp (MkQPlus _ _ l r m _ _ d hl hr hm hd))
  (let-match erased (zring-sound (Cons _ nx $ Cons _ (Zpos dx) $ Nil (Z)) _ _ m (Z0) zr-minus-self
    (zev-add (zev-mul (zev-var 0) (zev-var 1) hl) (zev-mul (zev-opp (zev-var 0) hn) (zev-var 1) hr) hm) (ZEvNum _ _ _ (ZView0))) (Refl _ _))
  (values d (Refl _ c)))

(def-fns _ $ (erased qle-zeros : (erased (Nat) a b) -> (erased (QLe (Qmake (Z0) a) (Qmake (Z0) b)) h))
  (MkQLe (Z0) (Z0) (Z0) (Z0) a b (zmul-0-l _) (zmul-0-l _) (zle-refl _)))

(def-lvl example-level)

(def-fns _ $ (many const-real : (many (Q) q) (erased (Z) scale) (erased (Q) qa qb) (erased (QAbs q qa) hqa)
    (erased (QPower (Qmake (Zpos (Succ (Zero))) (Zero)) scale qb) hqb) (erased (QLt qa qb) hab) ->
    (many (CReal example-level (MkSpec (Q) q ConstSeq scale)) r))
  (let ((erased s)) (MkSpec (Q) q ConstSeq scale))
  (def-fns example-level
    ((many seq : (many (Z) n) -> (many (Q) a) (erased (SeqAt s n a) h))
      (values q (MkSeqAt (Q) q ConstSeq scale n q (MkConstSeq q n))))
    ((erased functional : (erased (Z) n) (erased (Q) a b) (erased (SeqAt s n a) ha)
        (erased (SeqAt s n b) hb) -> (erased (Eq (Q) a b) e))
      (let-match erased (const-term q a scale n ha) (Refl _ _))
      (let-match erased (const-term q b scale n hb) (Refl _ _))
      (Refl _ q))
    ((erased cauchy : (erased (Z) k p r) (erased (Q) a b) (erased (ZLe p k) hp) (erased (ZLe r k) hr)
        (erased (SeqAt s p a) ha) (erased (SeqAt s r b) hb) ->
        (erased (Q) d e c) (erased (QMinus a b d) hd) (erased (QAbs d e) he)
        (erased (QPower (Qmake (Zpos (Succ (Zero))) (Zero)) k c) hc) (erased (QLt e c) lt))
      (let-match erased (const-term q a scale p ha) (Refl _ _))
      (let-match erased (const-term q b scale r hb) (Refl _ _))
      (let ((erased d) (erased hd)) (qminus q q))
      (let ((erased z) (erased ez)) (qminus-self q d hd))
      (let-match erased ez (Refl _ _))
      (let ((erased c) (erased hc)) (qpower (Qmake (Zpos (Succ (Zero))) (Zero)) k))
      (values d d c hd (MkQAbs (Z0) (Z0) z (ZAbs0)) hc (qle-lt-trans _ _ _ (qle-zeros z (Zero)) (qpower2-pos k c hc))))
    ((erased bound : (erased (Z) k) (erased (Q) a) (erased (SeqAt s k a) ha) ->
        (erased (Q) e2 c2) (erased (QAbs a e2) he2)
        (erased (QPower (Qmake (Zpos (Succ (Zero))) (Zero)) scale c2) hc2) (erased (QLt e2 c2) lt2))
      (let-match erased (const-term q a scale k ha) (Refl _ _))
      (values qa qb hqa hqb hab)))
  (MkCReal example-level s seq functional (MkQCauchySeq example-level s cauchy)
    (MkQBound example-level s scale (MkScaleOf (Q) q ConstSeq scale) bound)))

(def-fns _ $ (erased zsucc-pos : (erased (Nat) k) -> (erased (ZAdd (Zpos k) (Zpos (Zero)) (Zpos (Succ k))) h))
  (MkZAdd _ _ _ _ _ _ _ _ _ _ _ _ (ZViewPos k) (ZViewPos (Zero)) (ZViewPos (Succ k))
    (add-succ-right _ _ _ (add-zero-right _)) (add-zero-right _) (AddZero _) (AddZero _)))

(def-fns _ $ (erased zsucc-neg : (erased (Nat) k) -> (erased (ZAdd (Zneg (Succ k)) (Zpos (Zero)) (Zneg k)) h))
  (MkZAdd _ _ _ _ _ _ _ _ _ _ _ _ (ZViewNeg (Succ k)) (ZViewPos (Zero)) (ZViewNeg k)
    (AddZero _) (AddSucc _ _ _ (AddZero _)) (add-zero-right _) (add-zero-right _)))

(def-fns _ $ (erased zlt-succ : (erased (Nat) k) -> (erased (ZLt (Zpos k) (Zpos (Succ k))) h))
  (zgap-lt _ _ (Zero) (MkZGap _ _ _ _ (ZViewPos (Zero)) (zsucc-pos k))))

(def-fns _ $ (erased qlt-int : (erased (Z) a b) (erased (ZLt a b) h) -> (erased (QLt (Qmake a (Zero)) (Qmake b (Zero))) l))
  (MkQLt a b a b (Zero) (Zero) (zmul-1-r a) (zmul-1-r b) h))

(let ((erased qlt-0-2)) (qlt-int (Z0) (Zpos (Succ (Zero))) (zpos-is-pos _)))

(def-fns _ $ (erased creal-self-eq : (erased (Spec) s) (erased (CReal example-level s) x) -> (erased (CRealEq s s) e))
  (let-match erased x (MkCReal _ _ _ functional _ _))
  (def-fns _ $ (erased not-lt-self : (erased (CRealLt s s) h) -> (erased (False) f))
    (let-match erased h (MkCRealLt _ _ n a b c d e ha hb hc hd he lt))
    (let-match erased (functional n a b ha hb) (Refl _ _))
    (let ((erased z) (erased ez)) (qminus-self a c hc))
    (let-match erased ez (Refl _ _))
    (let-match erased d (Qmake nd dd))
    (let ((erased z2) (erased hz2)) (zpos-mul (Zero) dd))
    (let ((erased pos)) (qmult-lt-compat-r _ _ _ _ _ (qpower2-pos n d hd) qlt-0-2 (MkQMult (Z0) nd (Z0) (Zero) dd z2 (zmul-0-l nd) hz2) he))
    (qle-not-lt _ _ (qle-zeros z z2) (qlt-trans _ _ _ pos lt)))
  (let ((erased le)) (MkCRealLe s s (level-of not-lt-self) not-lt-self))
  (MkCRealEq s s le le))

(def-fns _ $ (erased rpoint-self-eq : (erased (RPoint example-level) p) -> (erased (RPointEq example-level p p) e))
  (let-match erased p (MkRPoint _ sx sy x y))
  (MkRPointEq _ sx sy sx sy x y x y (creal-self-eq sx x) (creal-self-eq sy y)))

(let ((many example-real-0))
  (const-real (Qmake (Z0) (Zero)) (Zpos (Zero)) _ _ (MkQAbs _ _ _ (ZAbs0)) (QPowerZpos _ _ (Zero) (QPowerOne _)) qlt-0-2))

(let ((many example-real-1))
  (const-real (Qmake (Zpos (Zero)) (Zero)) (Zpos (Zero)) _ _ (MkQAbs _ _ _ (ZAbsPos (Zero))) (QPowerZpos _ _ (Zero) (QPowerOne _))
    (qlt-int _ _ (zlt-succ (Zero)))))

(let ((many example-p00)) (MkRPoint example-level _ _ example-real-0 example-real-0))
(let ((many example-p10)) (MkRPoint example-level _ _ example-real-1 example-real-0))
(let ((many example-p01)) (MkRPoint example-level _ _ example-real-0 example-real-1))

(let ((many example-gap) (erased example-gap-h)) (qminus (Qmake (Zpos (Zero)) (Zero)) (Qmake (Z0) (Zero))))
(let ((many example-quarter) (erased example-quarter-h)) (qpower (Qmake (Zpos (Succ (Zero))) (Zero)) (Zneg (Succ (Zero)))))
(let ((many example-half) (erased example-half-h)) (qmult (Qmake (Zpos (Succ (Zero))) (Zero)) example-quarter))
(comptime-match many (qlt-le-dec example-half example-gap) (IsLt _ _ _ _ _ example-half-lt-gap))

(def-fns _ $ (erased creal-lt-0-1 : (erased (Spec) x y) (erased (SeqAt x (Zneg (Succ (Zero))) (Qmake (Z0) (Zero))) ha)
    (erased (SeqAt y (Zneg (Succ (Zero))) (Qmake (Zpos (Zero)) (Zero))) hb) -> (erased (CRealLt x y) l))
  (MkCRealLt x y _ _ _ _ _ _ ha hb example-gap-h example-quarter-h example-half-h example-half-lt-gap))

(let ((erased example-edges)) (Cons (REdge example-level) (MkREdge example-level example-p00 example-p10) (Nil (REdge example-level))))

(let ((erased (RDrawing example-level example-edges) example-edge-drawing))
  (RDrawCons _ _ _ _
    (RApartX _ _ _ _ _ _ _ _ _ (AppartLt _ _ (creal-lt-0-1 _ _ (const-at) (const-at))))
    (RCANil _ _ _) (RDrawNil _)))

(def-macro (int-spec args)
  (qq (MkSpec (Q) (Qmake (~@ args) (Zero)) ConstSeq (Zpos (Zero)))))

(def-adts $ (IntPoint : ((RPoint example-level) p) ((Z) x) ((Z) y) -> Type)
  enum
  (many MkIntPoint : (erased (Z) x y) (erased (CReal example-level (int-spec x)) xr) (erased (CReal example-level (int-spec y)) yr)
      -> (IntPoint (MkRPoint example-level (int-spec x) (int-spec y) xr yr) x y)))

(def-fns _ $ (erased int-mult-at : (erased (Nat) j) (erased (Z) x y m) (erased (ZMul x y m) h) ->
    (erased (SeqAt (MkSpec (SpecPair) (MkSpecPair (int-spec x) (int-spec y)) CRealMultSeq (Zpos (Succ (Zero)))) (Zneg j) (Qmake m (Zero))) t))
  (MkSeqAt _ _ _ _ _ _ (MkCRealMultSeq _ _ _ _ _ _ _ _ _ _ _ _ (MkScaleOf _ _ _ _) (MkScaleOf _ _ _ _)
    (zsucc-neg (Succ j)) (zsucc-neg j) (zsucc-neg (Succ j)) (zsucc-neg j)
    (const-at) (const-at) (MkQMult x y m (Zero) (Zero) (Zero) h (zmul-1-r _)))))

(def-fns _ $ (erased int-plus-at : (erased (Nat) j) (erased (Spec) x y) (erased (Z) sc a b c)
    (erased (SeqAt x (Zneg (Succ j)) (Qmake a (Zero))) ha) (erased (SeqAt y (Zneg (Succ j)) (Qmake b (Zero))) hb) (erased (ZAdd a b c) h) ->
    (erased (SeqAt (MkSpec (SpecPair) (MkSpecPair x y) CRealPlusSeq sc) (Zneg j) (Qmake c (Zero))) t))
  (MkSeqAt _ _ _ _ _ _ (MkCRealPlusSeq _ _ _ _ _ _ _ _ (zsucc-neg j) ha hb
    (MkQPlus a b a b c (Zero) (Zero) (Zero) (zmul-1-r a) (zmul-1-r b) h (zmul-1-r _))
    (MkQRed c c (Z0) (Zpos (Zero)) (Z0) (Zpos (Zero)) (Z0) (Zero) (Zero) (Zero) (zmul-1-r c) (zmul-1-r _) (zmul-0-l c) (zmul-1-r _) (zadd-0-l _)))))

(def-fns _ $ (erased int-shoe : (erased (RPoint example-level) p q r) (erased (Z) ax ay bx by cx cy m1 m2 m3 u w)
    (erased (IntPoint p ax ay) ip) (erased (IntPoint q bx by) iq) (erased (IntPoint r cx cy) ir)
    (erased (ZMul ax by m1) h1) (erased (ZMul bx cy m2) h2) (erased (ZMul cx ay m3) h3) (erased (ZAdd m1 m2 u) hu) (erased (ZAdd u m3 w) hw) ->
    (erased (Spec) s) (erased (RShoelace example-level p q r s) sh) (erased (SeqAt s (Zneg (Succ (Zero))) (Qmake w (Zero))) t))
  (let-match erased ip (MkIntPoint _ _ xa ya))
  (let-match erased iq (MkIntPoint _ _ xb yb))
  (let-match erased ir (MkIntPoint _ _ xc yc))
  (let ((erased s1)) (MkSpec (SpecPair) (MkSpecPair (int-spec ax) (int-spec by)) CRealMultSeq (Zpos (Succ (Zero)))))
  (let ((erased s2)) (MkSpec (SpecPair) (MkSpecPair (int-spec bx) (int-spec cy)) CRealMultSeq (Zpos (Succ (Zero)))))
  (let ((erased s3)) (MkSpec (SpecPair) (MkSpecPair (int-spec cx) (int-spec ay)) CRealMultSeq (Zpos (Succ (Zero)))))
  (let ((erased s12)) (MkSpec (SpecPair) (MkSpecPair s1 s2) CRealPlusSeq (Zpos (Succ (Succ (Zero))))))
  (let ((erased s)) (MkSpec (SpecPair) (MkSpecPair s12 s3) CRealPlusSeq (Zpos (Succ (Succ (Succ (Zero)))))))
  (values s
    (MkRShoelace _ _ _ _ _ _ _ s1 s2 s3 s12 s xa ya xb yb xc yc
      (MkCRealMult _ _ _ _ _ (MkScaleOf _ _ _ _) (MkScaleOf _ _ _ _) (zsucc-pos (Zero)))
      (MkCRealMult _ _ _ _ _ (MkScaleOf _ _ _ _) (MkScaleOf _ _ _ _) (zsucc-pos (Zero)))
      (MkCRealMult _ _ _ _ _ (MkScaleOf _ _ _ _) (MkScaleOf _ _ _ _) (zsucc-pos (Zero)))
      (MkCRealPlus _ _ _ _ _ _ (MkScaleOf _ _ _ _) (MkScaleOf _ _ _ _) (ZMaxLeft _ _ (zle-refl _)) (zsucc-pos (Succ (Zero))))
      (MkCRealPlus _ _ _ _ _ _ (MkScaleOf _ _ _ _) (MkScaleOf _ _ _ _)
        (ZMaxLeft _ _ (zlt-le-incl _ _ (zlt-succ (Succ (Zero))))) (zsucc-pos (Succ (Succ (Zero))))))
    (int-plus-at (Succ (Zero)) s12 s3 _ _ _ _
      (int-plus-at (Succ (Succ (Zero))) s1 s2 _ _ _ _
        (int-mult-at (Succ (Succ (Succ (Zero)))) _ _ _ h1) (int-mult-at (Succ (Succ (Succ (Zero)))) _ _ _ h2) hu)
      (int-mult-at (Succ (Succ (Zero))) _ _ _ h3) hw)))

(def-fns _ $ (erased int-left : (erased (RPoint example-level) p q r) (erased (Z) ax ay bx by cx cy m1 m2 m3 u n1 n2 n3 v)
    (erased (IntPoint p ax ay) ip) (erased (IntPoint q bx by) iq) (erased (IntPoint r cx cy) ir)
    (erased (ZMul ax by m1) f1) (erased (ZMul bx cy m2) f2) (erased (ZMul cx ay m3) f3) (erased (ZAdd m1 m2 u) f4) (erased (ZAdd u m3 (Zpos (Zero))) f5)
    (erased (ZMul cx by n1) g1) (erased (ZMul bx ay n2) g2) (erased (ZMul ax cy n3) g3) (erased (ZAdd n1 n2 v) g4) (erased (ZAdd v n3 (Z0)) g5) ->
    (erased (RLeft example-level p q r) l))
  (let ((erased s1) (erased h1) (erased t1)) (int-shoe p q r ax ay bx by cx cy m1 m2 m3 u (Zpos (Zero)) ip iq ir f1 f2 f3 f4 f5))
  (let ((erased s2) (erased h2) (erased t2)) (int-shoe r q p cx cy bx by ax ay n1 n2 n3 v (Z0) ir iq ip g1 g2 g3 g4 g5))
  (MkRLeft _ p q r s1 s2 h1 h2 (creal-lt-0-1 s2 s1 t2 t1)))

(let ((erased ip00)) (MkIntPoint _ _ example-real-0 example-real-0))
(let ((erased ip10)) (MkIntPoint _ _ example-real-1 example-real-0))
(let ((erased ip01)) (MkIntPoint _ _ example-real-0 example-real-1))

(let ((erased left-00-10-01))
  (int-left example-p00 example-p10 example-p01 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ip00 ip10 ip01
    (zmul-0-l (Z0)) (zmul-1-r (Zpos (Zero))) (zmul-0-l (Z0)) (zadd-0-l (Zpos (Zero))) (zadd-0-r (Zpos (Zero)))
    (zmul-0-l (Z0)) (zmul-0-r (Zpos (Zero))) (zmul-0-l (Zpos (Zero))) (zadd-0-l (Z0)) (zadd-0-l (Z0))))

(let ((erased left-10-01-00))
  (int-left example-p10 example-p01 example-p00 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ip10 ip01 ip00
    (zmul-1-r (Zpos (Zero))) (zmul-0-l (Z0)) (zmul-0-l (Z0)) (zadd-0-r (Zpos (Zero))) (zadd-0-r (Zpos (Zero)))
    (zmul-0-l (Zpos (Zero))) (zmul-0-l (Z0)) (zmul-0-r (Zpos (Zero))) (zadd-0-l (Z0)) (zadd-0-l (Z0))))

(let ((many example-triangle))
  (Cons (REdge example-level) (MkREdge example-level example-p00 example-p10)
    $ Cons (REdge example-level) (MkREdge example-level example-p10 example-p01)
    $ Cons (REdge example-level) (MkREdge example-level example-p01 example-p00) $ Nil (REdge example-level)))

(let ((erased (RDrawing example-level example-triangle) example-triangle-drawing))
  (RDrawCons _ _ _ _ (RApartX _ _ _ _ _ _ _ _ _ (AppartLt _ _ (creal-lt-0-1 _ _ (const-at) (const-at))))
    (RCACons _ _ _ _ _ _ (RShareCB _ _ _ _ _ (rpoint-self-eq example-p10) (ROffLeft _ _ _ _ left-00-10-01))
      (RCACons _ _ _ _ _ _ (RShareDA _ _ _ _ _ (rpoint-self-eq example-p00) (ROffLeft _ _ _ _ left-00-10-01)) (RCANil _ _ _)))
    (RDrawCons _ _ _ _ (RApartX _ _ _ _ _ _ _ _ _ (AppartGt _ _ (creal-lt-0-1 _ _ (const-at) (const-at))))
      (RCACons _ _ _ _ _ _ (RShareCB _ _ _ _ _ (rpoint-self-eq example-p01) (ROffLeft _ _ _ _ left-10-01-00)) (RCANil _ _ _))
      (RDrawCons _ _ _ _ (RApartY _ _ _ _ _ _ _ _ _ (AppartGt _ _ (creal-lt-0-1 _ _ (const-at) (const-at))))
        (RCANil _ _ _) (RDrawNil _)))))
