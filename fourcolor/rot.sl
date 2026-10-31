(def-fns _ $ (erased lapp-exists : (erased Type A) (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (LApp A xs ys zs) p))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values ys (LAppNil _ ys))))
  (let ((erased zs1) (erased p1)) (lapp-exists _ xs1 ys))
  (values (Cons _ x zs1) (LAppCons _ x xs1 ys zs1 p1)))

(def-fns _ $ (erased lapp-fn : (erased Type A) (erased (List A) xs ys zs zs2) (subterm erased (LApp A xs ys zs) p)
    (erased (LApp A xs ys zs2) q) -> (erased (Eq (List A) zs zs2) e))
  (let-match erased p (LAppCons _ _ xs1 _ zs1 p1) ((LAppNil _ _) (let-match erased q (LAppNil _ _)) (Refl _ zs)))
  (let-match erased q (LAppCons _ _ _ _ zs3 q1))
  (let-match erased (lapp-fn _ xs1 ys zs1 zs3 p1 q1) (Refl _ _))
  (Refl _ zs))

(def-fns _ $ (erased lapp-nil : (erased Type A) (subterm erased (List A) xs) -> (erased (LApp A xs (Nil A) xs) p))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (LAppNil _ (Nil _))))
  (LAppCons _ x xs1 (Nil _) xs1 (lapp-nil _ xs1)))

(def-fns _ $ (erased lapp-assoc : (erased Type A) (erased (List A) a b c ab abc) (subterm erased (LApp A a b ab) p)
    (erased (LApp A ab c abc) q) -> (erased (List A) bc) (erased (LApp A b c bc) r) (erased (LApp A a bc abc) s))
  (let-match erased p (LAppCons _ x a1 _ ab1 p1)
    ((LAppNil _ _) (values abc q (LAppNil _ abc))))
  (let-match erased q (LAppCons _ _ _ _ abc1 q1))
  (let ((erased bc) (erased r) (erased s)) (lapp-assoc _ a1 b c ab1 abc1 p1 q1))
  (values bc r (LAppCons _ x a1 bc abc1 s)))

(def-fns _ $ (erased lapp-assoc-back : (erased Type A) (erased (List A) a b c bc abc) (erased (LApp A b c bc) p)
    (subterm erased (LApp A a bc abc) q) -> (erased (List A) ab) (erased (LApp A a b ab) r) (erased (LApp A ab c abc) s))
  (let-match erased q (LAppCons _ x a1 _ abc1 q1)
    ((LAppNil _ _) (values b (LAppNil _ b) p)))
  (let ((erased ab1) (erased r) (erased s)) (lapp-assoc-back _ a1 b c bc abc1 p q1))
  (values (Cons _ x ab1) (LAppCons _ x a1 b ab1 r) (LAppCons _ x ab1 c abc1 s)))

(def-adts $ (Split2 : (Type A) ((List A) u) ((List A) v) ((List A) b) ((List A) a) -> Type)
  enum
  (many SplitLeft : (erased Type A) (erased (List A) u v b a m) (erased (LApp A u m b) p) (erased (LApp A m a v) q)
      -> (Split2 A u v b a))
  (many SplitRight : (erased Type A) (erased (List A) u v b a m) (erased (LApp A b m u) p) (erased (LApp A m v a) q)
      -> (Split2 A u v b a)))

(def-fns _ $ (erased lapp-split : (erased Type A) (erased (List A) u v b a f) (subterm erased (LApp A u v f) p)
    (erased (LApp A b a f) q) -> (erased (Split2 A u v b a) r))
  (let-match erased p (LAppCons _ x u1 _ f1 p1)
    ((LAppNil _ _) (SplitLeft _ (Nil _) v b a b (LAppNil _ b) q)))
  (let-match erased q (LAppCons _ _ b1 _ _ q1)
    ((LAppNil _ _) (SplitRight _ u v (Nil _) a u (LAppNil _ u) p)))
  (match erased (lapp-split _ u1 v b1 a f1 p1 q1) _
    ((SplitLeft _ _ _ _ _ m p2 q2) (SplitLeft _ u v b a m (LAppCons _ x u1 m b1 p2) q2))
    ((SplitRight _ _ _ _ _ m p2 q2) (SplitRight _ u v b a m (LAppCons _ x b1 m u1 p2) q2))))

; f is a rotation of xs.
(def-adts $ (Rot : (Type A) ((List A) f) ((List A) xs) -> Type)
  enum
  (many MkRot : (erased Type A) (erased (List A) f xs a b) (erased (LApp A a b xs) p) (erased (LApp A b a f) q) -> (Rot A f xs)))

(def-fns _ $ (erased rot-refl : (erased Type A) (erased (List A) xs) -> (erased (Rot A xs xs) r))
  (MkRot _ xs xs (Nil _) xs (LAppNil _ xs) (lapp-nil _ xs)))

(def-fns _ $ (erased rot-trans : (erased Type A) (erased (List A) g f xs) (erased (Rot A g f) r1) (erased (Rot A f xs) r2) ->
    (erased (Rot A g xs) r))
  (let-match erased r1 (MkRot _ _ _ u v p1 q1))
  (let-match erased r2 (MkRot _ _ _ a b p2 q2))
  (match erased (lapp-split _ u v b a f p1 q2) _
    ((SplitLeft _ _ _ _ _ m pu pv)
      (let ((erased au) (erased s1) (erased s2)) (lapp-assoc-back _ a u m b xs pu p2))
      (let ((erased au2) (erased s3) (erased s4)) (lapp-assoc _ m a u v g pv q1))
      (let-match erased (lapp-fn _ a u au au2 s1 s3) (Refl _ _))
      (MkRot _ g xs au m s2 s4))
    ((SplitRight _ _ _ _ _ m pu pa)
      (let ((erased vb) (erased s1) (erased s2)) (lapp-assoc _ m v b a xs pa p2))
      (let ((erased vb2) (erased s3) (erased s4)) (lapp-assoc-back _ v b m u g pu q1))
      (let-match erased (lapp-fn _ v b vb vb2 s1 s3) (Refl _ _))
      (MkRot _ g xs m vb s2 s4))))

; fl is the items of gs in order.
(def-adts $ (GFlat : ((List (Group)) gs) ((List (Nat)) fl) -> Type)
  enum
  (many GFlatNil : -> (GFlat (Nil (Group)) (Nil (Nat))))
  (many GFlatCons : (erased (Nat) d) (erased (List (Nat)) xs fl1 fl) (erased (List (Group)) gs)
      (erased (LApp (Nat) xs fl1 fl) p) (erased (GFlat gs fl1) rest) -> (GFlat (Cons (Group) (MkGroup d xs) gs) fl)))

(def-adts $ (AllIs : ((List (Nat)) xs) ((Nat) u) -> Type)
  enum
  (many AllIsNil : (erased (Nat) u) -> (AllIs (Nil (Nat)) u))
  (many AllIsCons : (erased (Nat) u) (erased (List (Nat)) xs) (erased (AllIs xs u) rest) -> (AllIs (Cons (Nat) u xs) u)))

; Each group's items are labelled with its dart's label.
(def-adts $ (GroupLab : ((List (Nat)) pl) ((List (Group)) gs) -> Type)
  enum
  (many GLNil : (erased (List (Nat)) pl) -> (GroupLab pl (Nil (Group))))
  (many GLCons : (erased (List (Nat)) pl xs) (erased (Nat) d u) (erased (List (Group)) gs)
      (erased (Nth (Nat) pl d u) p) (erased (AllIs xs u) a) (erased (GroupLab pl gs) rest)
      -> (GroupLab pl (Cons (Group) (MkGroup d xs) gs))))

(def-fns _ $ (erased flat-snoc : (erased (List (Group)) gs gs2) (erased (Nat) d) (erased (List (Nat)) xs fl fl2)
    (subterm erased (GFlat gs fl) f) (erased (Snoc (Group) gs (MkGroup d xs) gs2) s) (erased (LApp (Nat) fl xs fl2) a)
    -> (erased (GFlat gs2 fl2) r))
  (match erased f _
    ((GFlatNil)
      (let-match erased s (SnocNil _ _))
      (let-match erased a (LAppNil _ _))
      (GFlatCons d xs (Nil _) xs _ (lapp-nil _ xs) (GFlatNil)))
    ((GFlatCons d1 xs1 fl1 _ gs1 p f1)
      (let-match erased s (SnocCons _ _ _ _ gs3 s1))
      (let ((erased fl3) (erased q1) (erased q2)) (lapp-assoc _ xs1 fl1 xs fl fl2 p a))
      (GFlatCons d1 xs1 fl3 fl2 gs3 q2 (flat-snoc gs1 gs3 d xs fl1 fl3 f1 s1 q1)))))

(def-fns _ $ (erased grouplab-snoc : (erased (List (Nat)) pl xs) (erased (List (Group)) gs gs2) (erased (Nat) d u)
    (subterm erased (GroupLab pl gs) gl) (erased (Snoc (Group) gs (MkGroup d xs) gs2) s) (erased (Nth (Nat) pl d u) p)
    (erased (AllIs xs u) a) -> (erased (GroupLab pl gs2) r))
  (match erased gl _
    ((GLNil _) (let-match erased s (SnocNil _ _)) (GLCons pl xs d u _ p a (GLNil pl)))
    ((GLCons _ xs1 d1 u1 gs1 p1 a1 gl1)
      (let-match erased s (SnocCons _ _ _ _ gs3 s1))
      (GLCons pl xs1 d1 u1 gs3 p1 a1 (grouplab-snoc pl xs gs1 gs3 d u gl1 s1 p a)))))

(def-fns _ $ (erased chain-snoc : (erased (List (Nat)) e nd s xs) (erased (List (Group)) gs gs2) (erased (Nat) d0 d1)
    (subterm erased (Chain e nd s gs d0) ch) (erased (Link e nd s d0 d1) k) (erased (Snoc (Group) gs (MkGroup d0 xs) gs2) sn)
    -> (erased (Chain e nd s gs2 d1) r))
  (match erased ch _
    ((ChainOne _ _ _ xs1 d _ k1)
      (let-match erased sn (SnocCons _ _ _ _ _ sn1))
      (let-match erased sn1 (SnocNil _ _))
      (ChainCons e nd s xs1 xs (Nil _) d d0 d1 k1 (ChainOne e nd s xs d0 d1 k)))
    ((ChainCons _ _ _ xs1 ys gs1 d d2 _ k1 rest)
      (let-match erased sn (SnocCons _ _ _ _ gs3 sn1))
      (let-match erased sn1 (SnocCons _ _ _ _ gs4 _))
      (ChainCons e nd s xs1 ys gs4 d d2 d1 k1 (chain-snoc e nd s xs (Cons _ (MkGroup d2 ys) gs1) gs3 d0 d1 rest k sn1)))))

(def-fns _ $ (erased darts-snoc : (erased (List (Group)) gs gs2) (erased (List (Nat)) s s2 xs) (erased (Nat) d)
    (subterm erased (Darts gs s) ds) (erased (Snoc (Group) gs (MkGroup d xs) gs2) sn) (erased (Snoc (Nat) s d s2) ss)
    -> (erased (Darts gs2 s2) r))
  (match erased ds _
    ((DartsNil) (let-match erased sn (SnocNil _ _)) (let-match erased ss (SnocNil _ _)) (DartsCons d xs _ _ (DartsNil)))
    ((DartsCons d1 xs1 s1 gs1 ds1)
      (let-match erased sn (SnocCons _ _ _ _ gs3 sn1))
      (let-match erased ss (SnocCons _ _ _ _ s3 ss1))
      (DartsCons d1 xs1 s3 gs3 (darts-snoc gs1 gs3 s1 s3 xs d ds1 sn1 ss1)))))

(def-fns _ $ (erased notin-snoc : (erased (Nat) x d) (erased (List (Nat)) s s2) (subterm erased (NotIn x s) p)
    (erased (Apart (Nat) Lt x d) ne) (erased (Snoc (Nat) s d s2) sn) -> (erased (NotIn x s2) r))
  (match erased p _
    ((NotInNil _) (let-match erased sn (SnocNil _ _)) (NotInCons x d _ ne (NotInNil x)))
    ((NotInCons _ y s1 n1 p1)
      (let-match erased sn (SnocCons _ _ _ _ s3 sn1))
      (NotInCons x y s3 n1 (notin-snoc x d s1 s3 p1 ne sn1)))))

(def-fns _ $ (erased distinct-snoc : (erased (Nat) d) (erased (List (Nat)) s s2) (subterm erased (Distinct s) dist)
    (erased (NotIn d s) p) (erased (Snoc (Nat) s d s2) sn) -> (erased (Distinct s2) r))
  (match erased dist _
    ((DistNil) (let-match erased sn (SnocNil _ _)) (DistCons d _ (NotInNil d) (DistNil)))
    ((DistCons x s1 nx dist1)
      (let-match erased sn (SnocCons _ _ _ _ s3 sn1))
      (let-match erased p (NotInCons _ _ _ dx p1))
      (DistCons x s3 (notin-snoc x d s1 s3 nx (apart-sym d x dx) sn1) (distinct-snoc d s1 s3 dist1 p1 sn1)))))

; A cyclic run r of xs, seen in its rotation fl: either fl is u ++ r ++ w, with w ++ u the rest of xs read from
; after r, or r = r1 ++ r2 wraps round the end of fl, with both parts non-empty.
(def-adts $ (CycRun : (Type A) ((List A) fl) ((List A) r) ((List A) qp) -> Type)
  enum
  (many CRFlat : (erased Type A) (erased (List A) fl r qp u w rw) (erased (LApp A r w rw) p1) (erased (LApp A u rw fl) p2)
      (erased (LApp A w u qp) p3) -> (CycRun A fl r qp))
  (many CRWrap : (erased Type A) (erased (List A) fl r qp r1 r2 m1 r2m) (erased A x1 x2) (erased (List A) t1 t2)
      (erased (Eq (List A) r1 (Cons A x1 t1)) n1) (erased (Eq (List A) r2 (Cons A x2 t2)) n2) (erased (LApp A r1 r2 r) p1)
      (erased (LApp A r2 qp r2m) p2) (erased (LApp A r2m r1 fl) p3) -> (CycRun A fl r qp)))

(def-fns _ $ (erased cyc-split : (erased Type A) (erased (List A) fl xs p r q pr qp) (erased (Rot A fl xs) ro)
    (erased (LApp A p r pr) a1) (erased (LApp A pr q xs) a2) (erased (LApp A q p qp) a3) -> (erased (CycRun A fl r qp) c))
  (let-match erased ro (MkRot _ _ _ a b pab pba))
  (let ((erased rq) (erased prq) (erased pxs)) (lapp-assoc _ p r q pr xs a1 a2))
  (match erased (lapp-split _ a b p rq xs pab pxs) _
    ((SplitLeft _ _ _ _ _ m am mrq)
      (let ((erased rqa) (erased s1) (erased s2)) (lapp-assoc _ m rq a b fl mrq pba))
      (let ((erased qa) (erased s3) (erased s4)) (lapp-assoc _ r q a rq rqa prq s1))
      (let ((erased x) (erased s5)) (lapp-exists _ qa m))
      (let ((erased am2) (erased s6) (erased s7)) (lapp-assoc _ q a m qa x s3 s5))
      (let-match erased (lapp-fn _ a m am2 p s6 am) (Refl _ _))
      (let-match erased (lapp-fn _ q p x qp s7 a3) (Refl _ _))
      (CRFlat _ fl r qp m qa rqa s4 s2 s5))
    ((SplitRight _ _ _ _ _ m pm mb)
      (match erased (lapp-split _ m b r q rq mb prq) _
        ((SplitLeft _ _ _ _ _ m2 mm2 m2q)
          (match erased m _
            ((Nil _)
              (let-match erased mm2 (LAppNil _ _))
              (let-match erased (lapp-fn _ p (Nil _) a p pm (lapp-nil _ p)) (Refl _ _))
              (let ((erased qp2) (erased s1) (erased s2)) (lapp-assoc _ r q p b fl m2q pba))
              (let-match erased (lapp-fn _ q p qp2 qp s1 a3) (Refl _ _))
              (CRFlat _ fl r qp (Nil _) qp fl s2 (LAppNil _ fl) (lapp-nil _ qp)))
            ((Cons _ x1 t1)
              (match erased m2 _
                ((Nil _)
                  (let-match erased (lapp-fn _ m (Nil _) r m mm2 (lapp-nil _ m)) (Refl _ _))
                  (let-match erased m2q (LAppNil _ _))
                  (let ((erased qp2) (erased s1) (erased s2)) (lapp-assoc-back _ q p r a fl pm pba))
                  (let-match erased (lapp-fn _ q p qp2 qp s1 a3) (Refl _ _))
                  (CRFlat _ fl r qp qp (Nil _) r (lapp-nil _ r) s2 (LAppNil _ qp)))
                ((Cons _ x2 t2)
                  (let ((erased qa) (erased s1) (erased s2)) (lapp-assoc _ m2 q a b fl m2q pba))
                  (let ((erased qp3) (erased s3) (erased s4)) (lapp-assoc-back _ q p m a qa pm s1))
                  (let-match erased (lapp-fn _ q p qp3 qp s3 a3) (Refl _ _))
                  (let ((erased r2m) (erased s5) (erased s6)) (lapp-assoc-back _ m2 qp m qa fl s4 s2))
                  (CRWrap _ fl r qp m m2 qa r2m x1 x2 t1 t2 (Refl _ m) (Refl _ m2) mm2 s5 s6))))))
        ((SplitRight _ _ _ _ _ m2 rm2 m2b)
          (let ((erased bp) (erased s1) (erased s2)) (lapp-assoc-back _ b p m a fl pm pba))
          (let ((erased x) (erased s3)) (lapp-exists _ m2 bp))
          (let ((erased y) (erased s4) (erased s5)) (lapp-assoc-back _ m2 b p bp x s1 s3))
          (let-match erased (lapp-fn _ m2 b y q s4 m2b) (Refl _ _))
          (let-match erased (lapp-fn _ q p x qp s5 a3) (Refl _ _))
          (CRFlat _ fl r qp bp m2 m rm2 s2 s3))))))

; y is non-empty when v is.
(def-adts $ (Lead : ((List (Nat)) v) ((List (Nat)) y) -> Type)
  enum
  (many LeadNil : (erased (List (Nat)) y) -> (Lead (Nil (Nat)) y))
  (many LeadCons : (erased (List (Nat)) v y) (erased (Nat) x) -> (Lead v (Cons (Nat) x y))))

; The cut of fl into u ++ v falls inside the group (d, b ++ y) of gs, after the groups gs1.
(def-adts $ (Cut : ((List (Group)) gs) ((List (Nat)) u) ((List (Nat)) v) -> Type)
  enum
  (many MkCut : (erased (List (Group)) gs gs1 gs2) (erased (List (Nat)) u v b y by f1 f2) (erased (Nat) d)
      (erased (LApp (Group) gs1 (Cons (Group) (MkGroup d by) gs2) gs) pg) (erased (LApp (Nat) b y by) pb)
      (erased (GFlat gs1 f1) g1) (erased (GFlat gs2 f2) g2) (erased (LApp (Nat) f1 b u) pu) (erased (LApp (Nat) y f2 v) pv)
      (erased (Lead v y) ld) -> (Cut gs u v)))

(def-fns _ $ (erased cut-head : (erased (Nat) d0) (erased (List (Nat)) x0 u v m fl1) (erased (List (Group)) gs1)
    (erased (LApp (Nat) u m x0) p1) (erased (LApp (Nat) m fl1 v) p2) (erased (GFlat gs1 fl1) g) (erased (Lead v m) ld)
    -> (erased (Cut (Cons (Group) (MkGroup d0 x0) gs1) u v) c))
  (MkCut _ (Nil _) gs1 u v u m x0 (Nil _) fl1 d0 (LAppNil _ _) p1 (GFlatNil) g (LAppNil _ u) p2 ld))

(def-fns _ $ (erased cut-cons : (erased (Nat) d0) (erased (List (Nat)) x0 u v m) (erased (List (Group)) gs1)
    (erased (LApp (Nat) x0 m u) p) (erased (Cut gs1 m v) c) -> (erased (Cut (Cons (Group) (MkGroup d0 x0) gs1) u v) r))
  (let-match erased c (MkCut _ gs3 gs4 _ _ b y by f3 f4 d pg pb g3 g4 pu pv ld))
  (let ((erased f1) (erased q1) (erased q2)) (lapp-assoc-back _ x0 f3 b m u pu p))
  (MkCut _ (Cons _ (MkGroup d0 x0) gs3) gs4 u v b y by f1 f4 d (LAppCons _ (MkGroup d0 x0) gs3 _ gs1 pg) pb
    (GFlatCons d0 x0 f3 f1 gs3 q1 g3) g4 q2 pv ld))

(def-fns _ $ (erased group-split : (erased (List (Group)) gs1) (erased (Nat) d0) (erased (List (Nat)) x0 u v fl)
    (subterm erased (GFlat (Cons (Group) (MkGroup d0 x0) gs1) fl) gf) (erased (LApp (Nat) u v fl) p)
    -> (erased (Cut (Cons (Group) (MkGroup d0 x0) gs1) u v) c))
  (let-match erased gf (GFlatCons _ _ fl1 _ _ px gf1))
  (match erased (lapp-split _ u v x0 fl1 fl p px) _
    ((SplitLeft _ _ _ _ _ m um mv)
      (let-match erased m (Nil _) ((Cons _ y ys) (cut-head d0 x0 u v m fl1 gs1 um mv gf1 (LeadCons v ys y))))
      (let-match erased mv (LAppNil _ _))
      (let-match erased v (Cons _ _ _) ((Nil _) (cut-head d0 x0 u v m fl1 gs1 um mv gf1 (LeadNil m))))
      (let-match erased gf1 (GFlatCons d1 x1 _ _ gs2 _ _))
      (let-match erased (lapp-fn _ u (Nil _) x0 u um (lapp-nil _ u)) (Refl _ _))
      (cut-cons d0 x0 u v (Nil _) gs1 (lapp-nil _ u) (group-split gs2 d1 x1 (Nil _) v fl1 gf1 (LAppNil _ v))))
    ((SplitRight _ _ _ _ _ m xm mv)
      (let-match erased gf1 (GFlatCons d1 x1 _ _ gs2 _ _)
        ((GFlatNil)
          (let-match erased mv (LAppNil _ _))
          (let-match erased (lapp-fn _ x0 (Nil _) u x0 xm (lapp-nil _ x0)) (Refl _ _))
          (cut-head d0 x0 u v (Nil _) fl1 gs1 (lapp-nil _ u) (LAppNil _ fl1) gf1 (LeadNil (Nil _)))))
      (cut-cons d0 x0 u v m gs1 xm (group-split gs2 d1 x1 m v fl1 gf1 mv)))))

(def-fns _ $ (erased app-snoc : (erased Type A) (erased (List A) a b c c2) (erased A h) (subterm erased (LApp A a b c) p)
    (erased (Snoc A c h c2) s) -> (erased (List A) b2) (erased (Snoc A b h b2) s2) (erased (LApp A a b2 c2) p2))
  (let-match erased p (LAppCons _ x a1 _ c1 p1) ((LAppNil _ _) (values c2 s (LAppNil _ c2))))
  (let-match erased s (SnocCons _ _ _ _ c3 s1))
  (let ((erased b2) (erased s2) (erased p2)) (app-snoc _ a1 b c1 c3 h p1 s1))
  (values b2 s2 (LAppCons _ x a1 b2 c3 p2)))

(def-fns _ $ (erased snoc-app : (erased Type A) (erased (List A) a ah b c) (erased A h) (subterm erased (Snoc A a h ah) s)
    (erased (LApp A ah b c) p) -> (erased (LApp A a (Cons A h b) c) r))
  (match erased s _
    ((SnocNil _ _) (let-match erased p (LAppCons _ _ _ _ _ p1)) (let-match erased p1 (LAppNil _ _)) (LAppNil _ c))
    ((SnocCons _ x _ a1 ah1 s1)
      (let-match erased p (LAppCons _ _ _ _ c1 p1))
      (LAppCons _ x a1 (Cons _ h b) c1 (snoc-app _ a1 ah1 b c1 h s1 p1)))))


(def-fns _ $ (erased flat-fn : (erased (List (Group)) gs) (erased (List (Nat)) f g) (subterm erased (GFlat gs f) p) (erased (GFlat gs g) q) ->
    (erased (Eq (List (Nat)) f g) e))
  (let-match erased p (GFlatCons _ xs f1 _ gs1 a p1) ((GFlatNil) (let-match erased q (GFlatNil)) (Refl _ f)))
  (let-match erased q (GFlatCons _ _ g1 _ _ b q1))
  (let-match erased (flat-fn gs1 f1 g1 p1 q1) (Refl _ _))
  (lapp-fn _ xs f1 f g a b))

(def-fns _ $ (erased flat-app : (erased (List (Group)) gs1 gs2 gs3) (erased (List (Nat)) f1 f2) (subterm erased (GFlat gs1 f1) p)
    (erased (GFlat gs2 f2) q) (erased (LApp (Group) gs1 gs2 gs3) a) -> (erased (List (Nat)) f3) (erased (LApp (Nat) f1 f2 f3) b)
    (erased (GFlat gs3 f3) r))
  (let-match erased p (GFlatCons d xs f4 _ gs4 c p1)
    ((GFlatNil) (let-match erased a (LAppNil _ _)) (values f2 (LAppNil _ f2) q)))
  (let-match erased a (LAppCons _ _ _ _ gs5 a1))
  (let ((erased f5) (erased b1) (erased r1)) (flat-app gs4 gs2 gs5 f4 f2 p1 q a1))
  (let ((erased f3) (erased b)) (lapp-exists _ f1 f2))
  (let ((erased f6) (erased c1) (erased c2)) (lapp-assoc _ xs f4 f2 f1 f3 c b))
  (let-match erased (lapp-fn _ f4 f2 f6 f5 c1 b1) (Refl _ _))
  (values f3 b (GFlatCons d xs f5 f3 gs5 c2 r1)))

(def-fns _ $ (erased allis-app : (erased (List (Nat)) a b c) (erased (Nat) u) (subterm erased (LApp (Nat) a b c) p) (erased (AllIs c u) q) ->
    (erased (AllIs a u) qa) (erased (AllIs b u) qb))
  (let-match erased p (LAppCons _ _ a1 _ c1 p1) ((LAppNil _ _) (values (AllIsNil u) q)))
  (let-match erased q (AllIsCons _ _ q1))
  (let ((erased qa) (erased qb)) (allis-app a1 b c1 u p1 q1))
  (values (AllIsCons u a1 qa) qb))

(def-fns _ $ (erased in-app-r : (erased (Nat) x) (erased (List (Nat)) a b c) (subterm erased (LApp (Nat) a b c) p) (erased (In x b) q) ->
    (erased (In x c) r))
  (let-match erased p (LAppCons _ y a1 _ c1 p1) ((LAppNil _ _) q))
  (InThere x y c1 (in-app-r x a1 b c1 p1 q)))

(def-fns _ $ (erased notin-app-r : (erased (Nat) x) (erased (List (Nat)) a b c) (subterm erased (LApp (Nat) a b c) p) (erased (NotIn x c) q) ->
    (erased (NotIn x b) r))
  (let-match erased p (LAppCons _ _ a1 _ c1 p1) ((LAppNil _ _) q))
  (let-match erased q (NotInCons _ _ _ _ q1))
  (notin-app-r x a1 b c1 p1 q1))

(def-fns _ $ (erased absurd distinct-app : (erased (Nat) x) (erased (List (Nat)) a b c) (subterm erased (LApp (Nat) a b c) p)
    (erased (Distinct c) d) (erased (In x a) qa) (erased (In x b) qb) -> (erased (False) f))
  (let-match erased p (LAppCons _ _ a1 _ c1 p1) (absurd (LAppNil _ _) qa))
  (let-match erased d (DistCons _ _ ny d1))
  (match erased qa _
    (absurd (InHere _ _) (apart-irrefl x (notin-in x x b (notin-app-r x a1 b c1 p1 ny) qb)))
    (absurd (InThere _ _ _ qa1) (distinct-app x a1 b c1 p1 d1 qa1 qb))))
