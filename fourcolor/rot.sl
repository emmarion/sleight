(def-fns _ $ (erased lapp-exists : (erased Type A) (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (LApp A xs ys zs) p))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values ys (LAppNil _ ys))))
  (let ((erased zs1) (erased p1)) (lapp-exists _ xs1 ys))
  (values (Cons _ x zs1) (LAppCons _ x xs1 ys zs1 p1)))

(def-fns _ $ (erased lapp-fn : (erased Type A) (erased (List A) xs ys zs zs2) (subterm erased (LApp A xs ys zs) p)
    (erased (LApp A xs ys zs2) q) -> (erased (Eq (List A) zs zs2) e))
  (let-match erased p (LAppCons _ x xs1 _ zs1 p1) ((LAppNil _ _) (let-match erased q (LAppNil _ _)) (Refl _ zs)))
  (let-match erased q (LAppCons _ _ _ _ zs3 q1))
  (let-match erased (lapp-fn _ xs1 ys zs1 zs3 p1 q1) (Refl _ _))
  (Refl _ zs))

(def-fns _ $ (erased lapp-nil : (erased Type A) (subterm erased (List A) xs) -> (erased (LApp A xs (Nil A) xs) p))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (LAppNil _ (Nil _))))
  (LAppCons _ x xs1 (Nil _) xs1 (lapp-nil _ xs1)))

; (a ++ b) ++ c is a ++ (b ++ c).
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

; Two splits of one list: one cut is before the other.
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

; A rotation of a rotation is a rotation.
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
      (let-match erased sn1 (SnocCons _ _ _ _ gs4 sn2))
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

(def-fns _ $ (erased in-snoc : (erased (Nat) x d) (erased (List (Nat)) s s2) (subterm erased (In x s) p) (erased (Snoc (Nat) s d s2) sn)
    -> (erased (In x s2) r))
  (let-match erased sn (SnocCons _ y _ s1 s3 sn1) (absurd (SnocNil _ _) p))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) (InHere x s3)))
  (InThere x y s3 (in-snoc x d s1 s3 p1 sn1)))

(def-fns _ $ (erased in-snoc-new : (erased (Nat) d) (erased (List (Nat)) s s2) (subterm erased (Snoc (Nat) s d s2) sn) -> (erased (In d s2) r))
  (match erased sn _
    ((SnocNil _ _) (InHere d _))
    ((SnocCons _ y _ s1 s3 sn1) (InThere d y s3 (in-snoc-new d s1 s3 sn1)))))

; Everything in d :: s is in s with d appended.
(def-fns _ $ (erased sub-rot : (erased (Nat) d) (erased (List (Nat)) s s2 m) (subterm erased (Sub m s) sb) (erased (Snoc (Nat) s d s2) sn)
    -> (erased (Sub m s2) r))
  (let-match erased sb (SubCons x m1 _ p sb1) ((SubNil _) (SubNil s2)))
  (SubCons x m1 s2 (in-snoc x d s s2 p sn) (sub-rot d s s2 m1 sb1 sn)))

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
