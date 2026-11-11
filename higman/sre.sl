; A mask g has one entry per letter; the letters of the block alphabet are those where it is BTrue.
(def-adts $ (Cnt : ((List (Bool)) g) ((Nat) s) -> Type)
  enum
  (many CntNil : -> (Cnt (Nil (Bool)) (Zero)))
  (many CntT : (erased (List (Bool)) g) (erased (Nat) s) (erased (Cnt g s) c) -> (Cnt (Cons (Bool) (BTrue) g) (Succ s)))
  (many CntF : (erased (List (Bool)) g) (erased (Nat) s) (erased (Cnt g s) c) -> (Cnt (Cons (Bool) (BFalse) g) s)))

(def-adts $ (AllIn : ((List (Bool)) g) ((List (Nat)) w) -> Type)
  enum
  (many InNil : (erased (List (Bool)) g) -> (AllIn g (Nil (Nat))))
  (many InCons : (erased (List (Bool)) g) (erased (Nat) a) (erased (List (Nat)) w) (erased (Nth (Bool) g a (BTrue)) n)
     (erased (AllIn g w) r) -> (AllIn g (Cons (Nat) a w))))

(def-adts $ (WCat : ((List (Nat)) a) ((List (Nat)) b) ((List (Nat)) c) -> Type)
  enum
  (many WCNil : (erased (List (Nat)) b) -> (WCat (Nil (Nat)) b b))
  (many WCCons : (erased (Nat) x) (erased (List (Nat)) a b c) (erased (WCat a b c) p) -> (WCat (Cons (Nat) x a) b (Cons (Nat) x c))))

(def-fns _ $ (many wcat : (subterm many (List (Nat)) a) (many (List (Nat)) b) -> (many (List (Nat)) c) (erased (WCat a b c) p))
  (let-match many a (Cons _ x a1) ((Nil _) (values b (WCNil b))))
  (let ((many c1) (erased p1)) (notail $ wcat a1 b))
  (values (Cons (Nat) x c1) (WCCons x a1 b c1 p1)))

(def-fns _ $ (erased wcat-nil : (subterm erased (List (Nat)) a) -> (erased (WCat a (Nil (Nat)) a) p))
  (let-match erased a (Cons _ x a1) ((Nil _) (WCNil (Nil (Nat)))))
  (WCCons x a1 (Nil (Nat)) a1 (wcat-nil a1)))

(def-fns _ $ (erased wcat-fn : (erased (List (Nat)) a b c d) (subterm erased (WCat a b c) p) (erased (WCat a b d) q)
    -> (erased (Eq (List (Nat)) c d) e))
  (let-match erased p (WCCons x a1 _ c1 p1) ((WCNil _) (let-match erased q (WCNil _)) (Refl (List (Nat)) c)))
  (let-match erased q (WCCons _ _ _ d1 q1))
  (let-match erased (wcat-fn a1 b c1 d1 p1 q1) (Refl _ _))
  (Refl (List (Nat)) c))

(def-fns _ $ (erased wcat-assoc : (erased (List (Nat)) s v1 v t w w1) (erased (Nat) a)
    (subterm erased (WCat s (Cons (Nat) a v1) v) p) (erased (WCat v t w) q) (erased (WCat v1 t w1) r)
    -> (erased (WCat s (Cons (Nat) a w1) w) o))
  (match erased p _
    ((WCNil _)
      (let-match erased q (WCCons _ _ _ w2 q1))
      (let-match erased (wcat-fn v1 t w2 w1 q1 r) (Refl _ _))
      (WCNil (Cons (Nat) a w1)))
    ((WCCons x s1 _ v2 p1)
      (let-match erased q (WCCons _ _ _ w2 q1))
      (WCCons x s1 (Cons (Nat) a w1) w2 (wcat-assoc s1 v1 v2 t w2 w1 a p1 q1 r)))))

(def-fns _ $ (erased emb-skip-cat : (erased (List (Nat)) s t v u) (subterm erased (WCat s t v) p) (erased (EmbN u t) e)
    -> (erased (EmbN u v) e2))
  (let-match erased p (WCCons x s1 _ v1 p1) ((WCNil _) e))
  (ENSkip x u v1 (emb-skip-cat s1 t v1 u p1 e)))

(def-fns _ $ (erased emb-cat : (erased (List (Nat)) u v a b x y) (subterm erased (EmbN u v) e) (erased (EmbN a b) f)
    (erased (WCat u a x) p) (erased (WCat v b y) q) -> (erased (EmbN x y) g))
  (match erased e _
    ((ENNil _) (let-match erased p (WCNil _)) (emb-skip-cat v b y a q f))
    ((ENSkip c _ v1 e1)
      (let-match erased q (WCCons _ _ _ y1 q1))
      (ENSkip c x y1 (emb-cat u v1 a b x y1 e1 f p q1)))
    ((ENKeep c u1 v1 e1)
      (let-match erased p (WCCons _ _ _ x1 p1))
      (let-match erased q (WCCons _ _ _ y1 q1))
      (ENKeep c x1 y1 (emb-cat u1 v1 a b x1 y1 e1 f p1 q1)))))

(def-fns _ $ (many mask-clear : (many (List (Bool)) g) (subterm many (Nat) a) (erased (Nth (Bool) g a (BTrue)) n)
    -> (many (List (Bool)) h) (erased (SetNth (Bool) g a (BFalse) h) p))
  (let-match many g (Cons _ x g1) (absurd (Nil _) n))
  (let-match many a (Succ a1) ((Zero) (values (Cons (Bool) (BFalse) g1) (SetHere (Bool) x (BFalse) g1))))
  (let-match erased n (NthThere _ _ _ _ _ n1))
  (let ((many h1) (erased p1)) (notail $ mask-clear g1 a1 n1))
  (values (Cons (Bool) x h1) (SetThere (Bool) x g1 a1 (BFalse) h1 p1)))

(def-fns _ $ (erased cnt-clear : (erased (List (Bool)) g h) (erased (Nat) a s) (subterm erased (SetNth (Bool) g a (BFalse) h) p)
    (erased (Nth (Bool) g a (BTrue)) n) (erased (Cnt g s) c) -> (erased (Nat) s1) (erased (Eq (Nat) s (Succ s1)) e) (erased (Cnt h s1) d))
  (match erased p _
    ((SetHere _ _ _ g1)
      (let-match erased n (NthHere _ _ _))
      (let-match erased c (CntT _ s1 c1))
      (values s1 (Refl (Nat) s) (CntF g1 s1 c1)))
    ((SetThere _ x g1 a1 _ h1 p1)
      (let-match erased n (NthThere _ _ _ _ _ n1))
      (match erased c _
        ((CntT _ s2 c1)
          (let ((erased s1) (erased e) (erased d)) (cnt-clear g1 h1 a1 s2 p1 n1 c1))
          (let-match erased e (Refl _ _))
          (values (Succ s1) (Refl (Nat) s) (CntT h1 s1 d)))
        ((CntF _ _ c1)
          (let ((erased s1) (erased e) (erased d)) (cnt-clear g1 h1 a1 s p1 n1 c1))
          (values s1 e (CntF h1 s1 d)))))))

(def-adts $ (ScanN : ((List (Bool)) g h) ((Nat) a) ((List (Nat)) v) -> Type)
  enum
  (many SHit : (erased (List (Bool)) g h) (erased (Nat) a) (erased (List (Nat)) v) (many (List (Nat)) s v1)
     (erased (AllIn h s) iws) (erased (AllIn g v1) inv) (erased (WCat s (Cons (Nat) a v1) v) p) -> (ScanN g h a v))
  (many SEnd : (erased (List (Bool)) g h) (erased (Nat) a) (erased (List (Nat)) v) (erased (AllIn h v) inv) -> (ScanN g h a v)))

(def-fns _ $ (many scan-n : (erased (List (Bool)) g h) (many (Nat) a) (erased (SetNth (Bool) g a (BFalse) h) sp)
    (subterm many (List (Nat)) v) (erased (AllIn g v) inv) -> (many (ScanN g h a v) r))
  (let-match many v (Cons _ b v1) ((Nil _) (SEnd g h a v (InNil h))))
  (let-match erased inv (InCons _ _ _ nb inv1))
  (let-match many (nat-eq b a) (Unequal _ _ _ _ ap)
    ((Equal _ _ _) (SHit g h a v (Nil (Nat)) v1 (InNil h) inv1 (WCNil v))))
  (let ((erased nh))
    (match erased ap (((Nth (Bool) h b (BTrue)) q))
      ((ApLt _ _ _ _ l) (setnth-nth-lt (Bool) g a b (BFalse) (BTrue) h sp nb l))
      ((ApGt _ _ _ _ l) (setnth-nth-gt (Bool) g a b (BFalse) (BTrue) h sp nb l))))
  (match many (notail $ scan-n g h a sp v1 inv1) _
    ((SHit _ _ _ _ s v2 iws inv2 p) (SHit g h a v (Cons (Nat) b s) v2 (InCons h b s nh iws) inv2 (WCCons b s (Cons (Nat) a v2) v1 p)))
    ((SEnd _ _ _ _ iws) (SEnd g h a v (InCons h b v1 nh iws)))))

(def-adts $ (LCat : (Type A) ((List A) a) ((List A) b) ((List A) c) -> Type)
  enum
  (many LCNil : (erased Type A) (erased (List A) b) -> (LCat A (Nil A) b b))
  (many LCCons : (erased Type A) (erased A x) (erased (List A) a b c) (erased (LCat A a b c) p) -> (LCat A (Cons A x a) b (Cons A x c))))

(def-adts $ (ConsAll : (Type A) (A k) ((List (List A)) a) ((List (List A)) b) -> Type)
  enum
  (many CANil : (erased Type A) (erased A k) -> (ConsAll A k (Nil (List A)) (Nil (List A))))
  (many CACons : (erased Type A) (erased A k) (erased (List A) x) (erased (List (List A)) a b) (erased (ConsAll A k a b) p)
     -> (ConsAll A k (Cons (List A) x a) (Cons (List A) (Cons A k x) b))))

(def-fns _ $ (many lcat : (erased Type A) (subterm many (List A) a) (many (List A) b) -> (many (List A) c) (erased (LCat A a b c) p))
  (let-match many a (Cons _ x a1) ((Nil _) (values b (LCNil A b))))
  (let ((many c1) (erased p1)) (notail $ lcat A a1 b))
  (values (Cons A x c1) (LCCons A x a1 b c1 p1)))

(def-fns _ $ (many cons-all : (erased Type A) (many A k) (subterm many (List (List A)) a) ->
    (many (List (List A)) b) (erased (ConsAll A k a b) p))
  (let-match many a (Cons _ x a1) ((Nil _) (values (Nil (List A)) (CANil A k))))
  (let ((many b1) (erased p1)) (notail $ cons-all A k a1))
  (values (Cons (List A) (Cons A k x) b1) (CACons A k x a1 b1 p1)))

(def-fns _ $ (erased nth-lcat-left : (erased Type A) (erased (List A) a b c) (subterm erased (LCat A a b c) ap)
    (erased (Nat) r) (erased A q) (erased (Nth A a r q) n) -> (erased (Nth A c r q) m))
  (let-match erased ap (LCCons _ x a1 _ c1 ap1) (absurd (LCNil _ _) n))
  (let-match erased n (NthThere _ _ _ r1 _ n1) ((NthHere _ _ _) (NthHere A q c1)))
  (NthThere A x c1 r1 q (nth-lcat-left A a1 b c1 ap1 r1 q n1)))

(def-fns _ $ (erased nth-lcat-right : (erased Type A) (erased (List A) a b c) (subterm erased (LCat A a b c) ap)
    (erased (Nat) k r s) (erased (Length A a k) la) (erased (Add k r s) ad) (erased A q) (erased (Nth A b r q) n)
    -> (erased (Nth A c s q) m))
  (let-match erased ap (LCCons _ x a1 _ c1 ap1)
    ((LCNil _ _) (let-match erased la (LengthNil _)) (let-match erased ad (AddZero _)) n))
  (let-match erased la (LengthCons _ _ _ k1 la1))
  (let-match erased ad (AddSucc _ _ s1 ad1))
  (NthThere A x c1 s1 q (nth-lcat-right A a1 b c1 ap1 k1 r s1 la1 ad1 q n)))

(def-fns _ $ (erased nth-consall : (erased Type A) (erased A k) (erased (List (List A)) a b) (subterm erased (ConsAll A k a b) p)
    (erased (Nat) r) (erased (List A) q) (erased (Nth (List A) a r q) n) -> (erased (Nth (List A) b r (Cons A k q)) m))
  (let-match erased p (CACons _ _ x a1 b1 p1) (absurd (CANil _ _) n))
  (let-match erased n (NthThere _ _ _ r1 _ n1) ((NthHere _ _ _) (NthHere (List A) (Cons A k q) b1)))
  (NthThere (List A) (Cons A k x) b1 r1 (Cons A k q) (nth-consall A k a1 b1 p1 r1 q n1)))

(def-fns _ $ (erased consall-length : (erased Type A) (erased A k) (erased (List (List A)) a b) (erased (Nat) n)
    (subterm erased (ConsAll A k a b) p) (erased (Length (List A) a n) l) -> (erased (Length (List A) b n) l2))
  (let-match erased p (CACons _ _ x a1 b1 p1) ((CANil _ _) (let-match erased l (LengthNil _)) (LengthNil (List A))))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (LengthCons (List A) (Cons A k x) b1 n1 (consall-length A k a1 b1 n1 p1 l1)))

(def-adts $ (Item : -> Type)
  enum
  (many IStar : (many (List (Bool)) g) -> (Item))
  (many ILit : (many (Nat) c) -> (Item)))

; ps holds one word per IStar of b; w is the word they spell with b's letters.
(def-adts $ (Fits : ((List (Item)) b) ((List (List (Nat))) ps) ((List (Nat)) w) -> Type)
  enum
  (many FitNil : -> (Fits (Nil (Item)) (Nil (List (Nat))) (Nil (Nat))))
  (many FitStar : (erased (List (Bool)) g) (erased (List (Nat)) s) (erased (List (List (Nat))) ps) (erased (List (Item)) b)
     (erased (List (Nat)) w w2) (erased (AllIn g s) i) (erased (Fits b ps w) f) (erased (WCat s w w2) c)
     -> (Fits (Cons (Item) (IStar g) b) (Cons (List (Nat)) s ps) w2))
  (many FitLit : (erased (Nat) c) (erased (List (List (Nat))) ps) (erased (List (Item)) b) (erased (List (Nat)) w)
     (erased (Fits b ps w) f) -> (Fits (Cons (Item) (ILit c) b) ps (Cons (Nat) c w))))

; Ss : the boxes that replace the block g of IStar g :: b by the words of g* avoiding u, one per length of a matched prefix of u.
(def-adts $ (Shapes : ((List (Bool)) g) ((List (Nat)) u) ((List (Item)) b) ((List (List (Item))) ss) -> Type)
  enum
  (many ShNil : (erased (List (Bool)) g) (erased (List (Item)) b) -> (Shapes g (Nil (Nat)) b (Nil (List (Item)))))
  (many ShCons : (erased (List (Bool)) g h) (erased (Nat) a) (erased (List (Nat)) u) (erased (List (Item)) b)
     (erased (List (List (Item))) ss ts rs) (erased (SetNth (Bool) g a (BFalse) h) sp) (erased (Shapes g u b ss) sh)
     (erased (ConsAll (Item) (ILit a) ss ts) c1) (erased (ConsAll (Item) (IStar h) ts rs) c2)
     -> (Shapes g (Cons (Nat) a u) b (Cons (List (Item)) (Cons (Item) (IStar h) b) rs))))

(def-fns _ $ (many shapes : (many (List (Bool)) g) (subterm many (List (Nat)) u) (many (List (Item)) b) (erased (AllIn g u) inu)
    -> (many (List (List (Item))) ss) (erased (Shapes g u b ss) sh))
  (let-match many u (Cons _ a u1) ((Nil _) (values (Nil (List (Item))) (ShNil g b))))
  (let-match erased inu (InCons _ _ _ na inu1))
  (let ((many h) (erased sp)) (mask-clear g a na))
  (let ((many ss) (erased sh)) (notail $ shapes g u1 b inu1))
  (let ((many ts) (erased c1)) (cons-all (Item) (ILit a) ss))
  (let ((many rs) (erased c2)) (cons-all (Item) (IStar h) ts))
  (values (Cons (List (Item)) (Cons (Item) (IStar h) b) rs) (ShCons g h a u1 b ss ts rs sp sh c1 c2)))

(def-fns _ $ (erased shapes-length : (erased (List (Bool)) g) (erased (List (Nat)) u) (erased (List (Item)) b)
    (erased (List (List (Item))) ss) (erased (Nat) n) (subterm erased (Shapes g u b ss) sh) (erased (Length (Nat) u n) l)
    -> (erased (Length (List (Item)) ss n) l2))
  (let-match erased sh (ShCons _ h a u1 _ ss1 ts rs sp sh1 c1 c2) ((ShNil _ _) (let-match erased l (LengthNil _)) (LengthNil (List (Item)))))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (LengthCons (List (Item)) (Cons (Item) (IStar h) b) rs n1
    (consall-length (Item) (IStar h) ts rs n1 c2 (consall-length (Item) (ILit a) ss1 ts n1 c1 (shapes-length g u1 b ss1 n1 sh1 l1)))))

(def-fns _ $ (erased wcat-exists : (subterm erased (List (Nat)) a) (erased (List (Nat)) b) -> (erased (List (Nat)) c) (erased (WCat a b c) p))
  (let-match erased a (Cons _ x a1) ((Nil _) (values b (WCNil b))))
  (let ((erased c1) (erased p1)) (wcat-exists a1 b))
  (values (Cons (Nat) x c1) (WCCons x a1 b c1 p1)))

; w : the block word v followed by the rest of the word; ss : the boxes the block may be replaced by.
(def-adts $ (DecR : ((List (Nat)) u v) ((List (List (Item))) ss) ((List (Nat)) w) -> Type)
  enum
  (many DREmb : (erased (List (Nat)) u v) (erased (List (List (Item))) ss) (erased (List (Nat)) w) (erased (EmbN u v) e)
     -> (DecR u v ss w))
  (many DRIn : (erased (List (Nat)) u v) (erased (List (List (Item))) ss) (erased (List (Nat)) w) (many (Nat) j)
     (erased (List (Item)) q) (erased (Nth (List (Item)) ss j q) n) (many (List (List (Nat))) ps) (erased (Fits q ps w) f)
     -> (DecR u v ss w)))

(def-fns _ $ (many dec : (erased (List (Bool)) g) (many (List (Nat)) u v) (erased (AllIn g v) inv)
    (erased (List (Item)) b) (many (List (List (Nat))) xp) (erased (List (Nat)) t w) (erased (Fits b xp t) ft) (erased (WCat v t w) vt)
    (erased (List (List (Item))) ss) (subterm erased (Shapes g u b ss) sh) -> (many (DecR u v ss w) r))
  (let-match many u (Cons _ ar u2) ((Nil _) (DREmb u v ss w (ENNil v))))
  (let-match erased sh (ShCons _ h a u1 _ ss1 ts rs sp sh1 c1 c2))
  (let-match many (scan-n g h ar sp v inv) (SHit _ _ _ _ s v1 iws inv1 p)
    ((SEnd _ _ _ _ inh)
      (DRIn u v ss w (Zero) (Cons (Item) (IStar h) b) (NthHere (List (Item)) _ rs) (Cons (List (Nat)) v xp)
        (FitStar h v xp b t w inh ft vt))))
  (let ((erased w1) (erased vt1)) (wcat-exists v1 t))
  (let-match many (notail $ dec g u2 v1 inv1 b xp t w1 ft vt1 ss1 sh1) (DRIn _ _ _ _ j q n ps f)
    ((DREmb _ _ _ _ e) (DREmb u v ss w (emb-skip-cat s (Cons (Nat) a v1) v u p (ENKeep a u2 v1 e)))))
  (DRIn u v ss w (Succ j) (Cons (Item) (IStar h) (Cons (Item) (ILit a) q))
    (NthThere (List (Item)) _ rs j _ (nth-consall (Item) (IStar h) ts rs c2 j _ (nth-consall (Item) (ILit a) ss1 ts c1 j q n)))
    (Cons (List (Nat)) s ps)
    (FitStar h s ps (Cons (Item) (ILit a) q) (Cons (Nat) a w1) w iws (FitLit a ps q w1 f) (wcat-assoc s v1 v t w w1 a p vt vt1))))

; ps : the boxes covering the points of b not above the point with parse pp.
(def-adts $ (Pcs : ((List (Item)) b) ((List (List (Nat))) pp) ((List (List (Item))) ps) -> Type)
  enum
  (many PcNil : -> (Pcs (Nil (Item)) (Nil (List (Nat))) (Nil (List (Item)))))
  (many PcLit : (erased (Nat) c) (erased (List (Item)) b) (erased (List (List (Nat))) pp) (erased (List (List (Item))) ps rs)
     (erased (Pcs b pp ps) pc) (erased (ConsAll (Item) (ILit c) ps rs) ca) -> (Pcs (Cons (Item) (ILit c) b) pp rs))
  (many PcStar : (erased (List (Bool)) g) (erased (List (Nat)) u) (erased (List (Item)) b) (erased (List (List (Nat))) pp)
     (erased (List (List (Item))) ss ps rs out) (erased (Shapes g u b ss) sh) (erased (Pcs b pp ps) pc)
     (erased (ConsAll (Item) (IStar g) ps rs) ca) (erased (LCat (List (Item)) ss rs out) ap)
     -> (Pcs (Cons (Item) (IStar g) b) (Cons (List (Nat)) u pp) out)))

(def-fns _ $ (many pieces : (subterm many (List (Item)) b) (many (List (List (Nat))) pp) (erased (List (Nat)) w) (erased (Fits b pp w) f)
    -> (many (List (List (Item))) ps) (erased (Pcs b pp ps) pc))
  (let-match many b (Cons _ it b1) ((Nil _) (let-match erased f (FitNil)) (values (Nil (List (Item))) (PcNil))))
  (match many it _
    ((IStar g)
      (let-match erased f (FitStar _ _ pp0 _ w1 _ inu f1 _))
      (let-match many pp (Cons _ u pp1))
      (let ((many ss) (erased sh)) (shapes g u b1 inu))
      (let ((many ps) (erased pc)) (notail $ pieces b1 pp1 w1 f1))
      (let ((many rs) (erased ca)) (cons-all (Item) (IStar g) ps))
      (let ((many out) (erased ap)) (lcat (List (Item)) ss rs))
      (values out (PcStar g u b1 pp1 ss ps rs out sh pc ca ap)))
    ((ILit c)
      (let-match erased f (FitLit _ _ _ w1 f1))
      (let ((many ps) (erased pc)) (notail $ pieces b1 pp w1 f1))
      (let ((many rs) (erased ca)) (cons-all (Item) (ILit c) ps))
      (values rs (PcLit c b1 pp ps rs pc ca)))))

(def-adts $ (ClsK : ((List (Nat)) wp wx) ((List (List (Item))) ps) -> Type)
  enum
  (many CKLe : (erased (List (Nat)) wp wx) (erased (List (List (Item))) ps) (erased (EmbN wp wx) e) -> (ClsK wp wx ps))
  (many CKIn : (erased (List (Nat)) wp wx) (erased (List (List (Item))) ps) (many (Nat) r) (erased (List (Item)) q)
     (erased (Nth (List (Item)) ps r q) n) (many (List (List (Nat))) xq) (erased (Fits q xq wx) f) -> (ClsK wp wx ps)))

(def-fns _ $ (many classify-k : (many (List (Item)) b) (many (List (List (Nat))) pp xp)
    (erased (List (Nat)) wp wx) (erased (Fits b pp wp) fp) (erased (Fits b xp wx) fx)
    (erased (List (List (Item))) ps) (subterm erased (Pcs b pp ps) pc) -> (many (ClsK wp wx ps) r))
  (let-match many b (Cons _ it b1)
    ((Nil _) (let-match erased fp (FitNil)) (let-match erased fx (FitNil)) (CKLe wp wx ps (ENNil wx))))
  (match many it _
    ((ILit c)
      (let-match erased pc (PcLit _ _ _ ps1 _ pc1 ca))
      (let-match erased fp (FitLit _ _ _ wp1 fp1))
      (let-match erased fx (FitLit _ _ _ wx1 fx1))
      (let-match many (notail $ classify-k b1 pp xp wp1 wx1 fp1 fx1 ps1 pc1) (CKIn _ _ _ r q n xq f)
        ((CKLe _ _ _ e) (CKLe wp wx ps (ENKeep c wp1 wx1 e))))
      (CKIn wp wx ps r (Cons (Item) (ILit c) q) (nth-consall (Item) (ILit c) ps1 ps ca r q n) xq (FitLit c xq q wx1 f)))
    ((IStar g)
      (let-match erased pc (PcStar _ u0 _ pp0 ss ps1 rs _ sh pc1 ca ap))
      (let-match erased fp (FitStar _ _ _ _ wp1 _ inu fp1 cu))
      (let-match erased fx (FitStar _ v0 xp0 _ wx1 _ inv fx1 cv))
      (let-match many pp (Cons _ u pp1))
      (let-match many xp (Cons _ v xp1))
      (let-match many (dec g u v inv b1 xp1 wx1 wx fx1 cv ss sh) (DREmb _ _ _ _ e)
        ((DRIn _ _ _ _ j q n xq f) (CKIn wp wx ps j q (nth-lcat-left (List (Item)) ss rs ps ap j q n) xq f)))
      (let-match many (notail $ classify-k b1 pp1 xp1 wp1 wx1 fp1 fx1 ps1 pc1) (CKIn _ _ _ r q n xq f)
        ((CKLe _ _ _ e1) (CKLe wp wx ps (emb-cat u v wp1 wx1 wp wx e e1 cu cv))))
      (let ((many lu) (erased llu)) (list-len (Nat) u))
      (let ((many s) (erased ad)) (add lu r))
      (CKIn wp wx ps s (Cons (Item) (IStar g) q)
        (nth-lcat-right (List (Item)) ss rs ps ap lu r s (shapes-length g u b1 ss lu sh llu) ad _
          (nth-consall (Item) (IStar g) ps1 rs ca r q n))
        (Cons (List (Nat)) v xq) (FitStar g v xq q wx1 wx inv f cv)))))
