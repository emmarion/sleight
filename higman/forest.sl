(def-adts $ (AllDeg : ((List (List (Coord))) qs) ((Nat) j) -> Type)
  enum
  (many ADNil : (erased (Nat) j) -> (AllDeg (Nil (List (Coord))) j))
  (many ADCons : (erased (List (Coord)) q) (erased (List (List (Coord))) qs) (erased (Nat) j) (erased (NAny q j) d)
     (erased (AllDeg qs (Succ j)) a) -> (AllDeg (Cons (List (Coord)) q qs) (Succ j))))

(def-fns _ $ (erased fr-deg : (erased (List (Coord)) b) (erased (Nat) y j) (erased (List (List (Coord))) fs)
    (subterm erased (FixRange b y fs) fr) (erased (NAny b j) d) -> (erased (AllDeg fs (Succ j)) a))
  (let-match erased fr (FRS _ y1 fs1 fr1) ((FRZ _) (ADNil (Succ j))))
  (ADCons (Cons (Coord) (CFix y1) b) fs1 j (NAnyFix y1 b j d) (fr-deg b y1 j fs1 fr1 d)))

(def-fns _ $ (erased mc-any-deg : (erased (List (List (Coord))) qs rs) (erased (Nat) j)
    (subterm erased (MapCons (CAny) qs rs) mc) (erased (AllDeg qs j) a) -> (erased (AllDeg rs (Succ j)) a2))
  (let-match erased mc (MCCons _ q qs1 rs1 mc1) ((MCNil _) (ADNil (Succ j))))
  (let-match erased a (ADCons _ _ j1 d a1))
  (ADCons (Cons (Coord) (CAny) q) rs1 j (NAnyAny q j1 d) (mc-any-deg qs1 rs1 j mc1 a1)))

(def-fns _ $ (erased mc-fix-deg : (erased (Nat) t) (erased (List (List (Coord))) qs rs) (erased (Nat) j)
    (subterm erased (MapCons (CFix t) qs rs) mc) (erased (AllDeg qs j) a) -> (erased (AllDeg rs j) a2))
  (let-match erased mc (MCCons _ q qs1 rs1 mc1) ((MCNil _) (ADNil j)))
  (let-match erased a (ADCons _ _ j1 d a1))
  (ADCons (Cons (Coord) (CFix t) q) rs1 j1 (NAnyFix t q j1 d) (mc-fix-deg t qs1 rs1 j mc1 a1)))

(def-fns _ $ (erased cat-deg : (erased (List (List (Coord))) a b c) (erased (Nat) j) (subterm erased (Cat a b c) ap)
    (erased (AllDeg a j) da) (erased (AllDeg b j) db) -> (erased (AllDeg c j) dc))
  (let-match erased ap (CatCons x a1 _ c1 ap1) ((CatNil _) db))
  (let-match erased da (ADCons _ _ j1 d da1))
  (ADCons x c1 j1 d (cat-deg a1 b c1 j ap1 da1 db)))

(def-fns _ $ (erased pieces-deg : (erased (List (Coord)) b) (erased (List (Nat)) p) (erased (List (List (Coord))) qs)
    (erased (Nat) j) (subterm erased (Pieces b p qs) pc) (erased (NAny b j) d) -> (erased (AllDeg qs j) a))
  (match erased pc _
    ((PcNil) (ADNil j))
    ((PcAny b1 y p1 fs qs1 rs out fr pc1 mc ap)
      (let-match erased d (NAnyAny _ j1 d1))
      (cat-deg fs rs out j ap (fr-deg b1 y j1 fs fr d1) (mc-any-deg qs1 rs j1 mc (pieces-deg b1 p1 qs1 j1 pc1 d1))))
    ((PcFix t b1 p1 qs1 rs pc1 mc)
      (let-match erased d (NAnyFix _ _ _ d1))
      (mc-fix-deg t qs1 rs j mc (pieces-deg b1 p1 qs1 j pc1 d1)))))

(def-adts $ (LeafOK : ((List (List (Coord))) qs) ((Nat) m) ((Nat) k) -> Type)
  enum
  (many LONil : (erased (Nat) m k) -> (LeafOK (Nil (List (Coord))) m k))
  (many LOCons : (erased (List (Coord)) q) (erased (List (List (Coord))) qs) (erased (Nat) m k j p) (erased (NAny q j) d)
     (erased (Add p j m) ad) (erased (Lt k (Succ p)) l) (erased (LeafOK qs m k) o) -> (LeafOK (Cons (List (Coord)) q qs) m k)))

(def-fns _ $ (erased alldeg-ok : (erased (List (List (Coord))) qs) (erased (Nat) j p m) (subterm erased (AllDeg qs j) a)
    (erased (Add p j m) ad) -> (erased (LeafOK qs m (Succ p)) o))
  (let-match erased a (ADCons q qs1 j1 d a1) ((ADNil _) (LONil m (Succ p))))
  (let ((erased c1) (erased e) (erased ad1)) (add-succ-right-inv p j1 m ad))
  (let-match erased e (Refl _ _))
  (LOCons q qs1 m (Succ p) j1 (Succ p) d (AddSucc p j1 c1 ad1) (lt-succ (Succ p)) (alldeg-ok qs1 j p m a1 ad)))

; I : the items the user attaches to points; P n it x : what an item it at sequence index n says about its point x.
(def-adts
  ((Forest : (Type I) ((TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) ((List (List (Coord))) bs) -> Type)
    enum
    (many FNil : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) -> (Forest I P (Nil (List (Coord)))))
    (many FCons : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P)
       (erased (List (Coord)) b) (erased (List (List (Coord))) bs) (many (Node I P b) node) (many (Forest I P bs) rest)
       -> (Forest I P (Cons (List (Coord)) b bs))))
  ((Node : (Type I) ((TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) ((List (Coord)) b) -> Type)
    enum
    (many NLeaf : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (List (Coord)) b)
       -> (Node I P b))
    (many NSplit : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (List (Coord)) b)
       (many (Nat) n) (many I it) (many (List (Nat)) p) (erased (P n it p) pp) (erased (InBox b p) ib)
       (many (List (List (Coord))) qs) (erased (Pieces b p qs) pc) (many (Forest I P qs) kids) -> (Node I P b))))

; m : the measure has m+1 entries; N : every item in the forest has index below N.
(def-adts
  ((MF : (Type I) ((TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) ((Nat) m) ((Nat) N)
       ((List (List (Coord))) bs) ((Forest I P bs) f) ((List (Nat)) u) -> Type)
    enum
    (many MFNil : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N)
       (erased (List (Nat)) z) (erased (Repeat (Nat) (Succ m) (Zero) z) r)
       -> (MF I P m N (Nil (List (Coord))) (FNil I P) z))
    (many MFCons : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N)
       (erased (List (Coord)) b) (erased (List (List (Coord))) bs) (erased (Node I P b) node) (erased (Forest I P bs) rest)
       (erased (List (Nat)) e w s) (erased (MN I P m N b node e) mn) (erased (MF I P m N bs rest w) mf) (erased (VAdd e w s) va)
       -> (MF I P m N (Cons (List (Coord)) b bs) (FCons I P b bs node rest) s)))
  ((MN : (Type I) ((TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) ((Nat) m) ((Nat) N)
       ((List (Coord)) b) ((Node I P b) nd) ((List (Nat)) u) -> Type)
    enum
    (many MNLeaf : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N)
       (erased (List (Coord)) b) (erased (Nat) j p) (erased (List (Nat)) e) (erased (NAny b j) d) (erased (Add p j m) ad)
       (erased (UnitP p j e) up) -> (MN I P m N b (NLeaf I P b) e))
    (many MNSplit : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N)
       (erased (List (Coord)) b) (erased (Nat) n) (erased I it) (erased (List (Nat)) pt) (erased (P n it pt) pp)
       (erased (InBox b pt) ib) (erased (List (List (Coord))) qs) (erased (Pieces b pt qs) pc) (erased (Forest I P qs) kids)
       (erased (List (Nat)) k) (erased (Lt n N) l) (erased (MF I P m N qs kids k) mf)
       -> (MN I P m N b (NSplit I P b n it pt pp ib qs pc kids) k))))

(def-fns _
  ((erased mf-length : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N)
      (erased (List (List (Coord))) bs) (erased (Forest I P bs) f) (erased (List (Nat)) u)
      (subterm erased (MF I P m N bs f u) mf) -> (erased (Length (Nat) u (Succ m)) l))
    (match erased mf _
      ((MFNil _ _ _ _ z r) (repeat-length (Nat) (Succ m) (Zero) z r))
      ((MFCons _ _ _ _ b bs1 node rest e w _ mn mf1 va)
        (vadd-length (Succ m) e w u va (mn-length I P m N b node e mn)))))
  ((erased mn-length : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N)
      (erased (List (Coord)) b) (erased (Node I P b) nd) (erased (List (Nat)) u)
      (subterm erased (MN I P m N b nd u) mn) -> (erased (Length (Nat) u (Succ m)) l))
    (match erased mn _
      ((MNLeaf _ _ _ _ _ j p _ _ ad up) (unit-length p j m u up ad))
      ((MNSplit _ _ _ _ _ _ _ _ _ _ qs _ kids _ _ mf) (mf-length I P m N qs kids u mf)))))

(def-fns _
  ((erased mf-weaken : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N Nb)
      (erased (Lt N (Succ Nb)) le) (erased (List (List (Coord))) bs) (erased (Forest I P bs) f) (erased (List (Nat)) u)
      (subterm erased (MF I P m N bs f u) mf) -> (erased (MF I P m Nb bs f u) mf2))
    (match erased mf _
      ((MFNil _ _ _ _ z r) (MFNil I P m Nb z r))
      ((MFCons _ _ _ _ b bs1 node rest e w _ mn mf1 va)
        (MFCons I P m Nb b bs1 node rest e w u (mn-weaken I P m N Nb le b node e mn) (mf-weaken I P m N Nb le bs1 rest w mf1) va))))
  ((erased mn-weaken : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N Nb)
      (erased (Lt N (Succ Nb)) le) (erased (List (Coord)) b) (erased (Node I P b) nd) (erased (List (Nat)) u)
      (subterm erased (MN I P m N b nd u) mn) -> (erased (MN I P m Nb b nd u) mn2))
    (match erased mn _
      ((MNLeaf _ _ _ _ _ j p _ d ad up) (MNLeaf I P m Nb b j p u d ad up))
      ((MNSplit _ _ _ _ _ n it pt pp ib qs pc kids _ l mf)
        (MNSplit I P m Nb b n it pt pp ib qs pc kids u (lt-le-trans n N Nb l le) (mf-weaken I P m N Nb le qs kids u mf))))))

(def-fns _ $ (many nany : (subterm many (List (Coord)) b) -> (many (Nat) j) (erased (NAny b j) d))
  (let-match many b (Cons _ c b1) ((Nil _) (values (Zero) (NAnyNil))))
  (let ((many j1) (erased d1)) (notail $ nany b1))
  (match many c _
    ((CAny) (values (Succ j1) (NAnyAny b1 j1 d1)))
    ((CFix t) (values j1 (NAnyFix t b1 j1 d1)))))

(def-fns _ $ (erased nany-fn : (erased (List (Coord)) b) (erased (Nat) i j) (subterm erased (NAny b i) d) (erased (NAny b j) e)
    -> (erased (Eq (Nat) i j) q))
  (match erased d _
    ((NAnyNil) (let-match erased e (NAnyNil)) (Refl (Nat) i))
    ((NAnyAny b1 i1 d1)
      (let-match erased e (NAnyAny _ j1 e1))
      (let-match erased (nany-fn b1 i1 j1 d1 e1) (Refl _ _))
      (Refl (Nat) i))
    ((NAnyFix t b1 _ d1)
      (let-match erased e (NAnyFix _ _ _ e1))
      (nany-fn b1 i j d1 e1))))

(def-fns _ $ (many mk-leaves : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P)
    (erased (Nat) m N k) (erased (Lt k (Succ (Succ m))) kl) (subterm many (List (List (Coord))) qs) (erased (LeafOK qs m k) ok) ->
    (many (Forest I P qs) f) (erased (List (Nat)) w) (erased (MF I P m N qs f w) mf) (erased (ZP k w) zp))
  (let-match many qs (Cons _ q qs1)
    ((Nil _)
      (let ((erased z) (erased r)) (repeat-exists (Nat) (Succ m) (Zero)))
      (values (FNil I P) z (MFNil I P m N z r) (zp-repeat k (Succ m) z r kl))))
  (let-match erased ok (LOCons _ _ _ _ j p d ad l ok1))
  (let ((many f1) (erased w1) (erased mf1) (erased zp1)) (notail $ mk-leaves I P m N k kl qs1 ok1))
  (let ((erased e) (erased up)) (unit-exists p j))
  (let ((erased s) (erased va) (erased _))
    (vadd-exists (Succ m) e w1 (unit-length p j m e up ad) (mf-length I P m N qs1 f1 w1 mf1)))
  (values (FCons I P q qs1 (NLeaf I P q) f1) s
    (MFCons I P m N q qs1 (NLeaf I P q) f1 e w1 s (MNLeaf I P m N q j p e d ad up) mf1 va)
    (zp-vadd k e w1 s (zp-unit k p j e up l) zp1 va)))

(def-adts $ (Ins : (Type I) ((TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) ((Nat) m) ((Nat) N) ((Nat) nn)
    ((List (Nat)) x) ((List (List (Coord))) bs) ((List (Nat)) u) -> Type)
  enum
  (many Found : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N nn)
     (erased (List (Nat)) x) (erased (List (List (Coord))) bs) (erased (List (Nat)) u)
     (many (Nat) n) (many I it) (many (List (Nat)) p) (erased (P n it p) pp) (erased (Lt n N) l) (erased (PLe p x) le)
     -> (Ins I P m N nn x bs u))
  (many Inserted : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased (Nat) m N nn)
     (erased (List (Nat)) x) (erased (List (List (Coord))) bs) (erased (List (Nat)) u)
     (many (Forest I P bs) f2) (erased (List (Nat)) u2) (erased (MF I P m (Succ nn) bs f2 u2) mf2)
     (many (Nat) pos) (erased (LexPos (Succ m) pos u2 u) lp) -> (Ins I P m N nn x bs u)))

(def-fns _ $ (many put-head : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P)
    (erased (Nat) m N nn) (erased (Lt N (Succ nn)) le) (erased (List (Nat)) x) (erased (List (Coord)) b)
    (erased (List (List (Coord))) bs) (many (Forest I P bs) rest) (erased (List (Nat)) e w s)
    (erased (MF I P m N bs rest w) mf) (erased (VAdd e w s) va)
    (many (Node I P b) node2) (erased (List (Nat)) e2) (erased (MN I P m (Succ nn) b node2 e2) mn2)
    (many (Nat) pos) (erased (LexPos (Succ m) pos e2 e) lp) -> (many (Ins I P m N nn x (Cons (List (Coord)) b bs) s) res))
  (let ((erased s2) (erased va2) (erased _))
    (vadd-exists (Succ m) e2 w (mn-length I P m (Succ nn) b node2 e2 mn2) (mf-length I P m N bs rest w mf)))
  (Inserted I P m N nn x (Cons (List (Coord)) b bs) s (FCons I P b bs node2 rest) s2
    (MFCons I P m (Succ nn) b bs node2 rest e2 w s2 mn2 (mf-weaken I P m N (Succ nn) (lt-weaken N (Succ nn) le) bs rest w mf) va2)
    pos (lexpos-add (Succ m) pos e2 e w s2 s lp va2 va)))

(def-fns _ $ (many insert : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P)
    (many (Nat) m) (erased (Nat) N) (many (Nat) nn) (erased (Lt N (Succ nn)) le)
    (many I it) (many (List (Nat)) x) (erased (P nn it x) px)
    (many (List (List (Coord))) bs) (subterm many (Forest I P bs) f) (many (Nat) r) (erased (List (Coord)) b)
    (erased (Nth (List (Coord)) bs r b) nb) (erased (InBox b x) ibx) (erased (List (Nat)) u) (erased (MF I P m N bs f u) mf)
    -> (many (Ins I P m N nn x bs u) res))
  (let-match many f (FCons _ _ b0 bs1 node rest) (absurd (FNil _ _) nb))
  (let-match many bs (Cons _ bh bs2))
  (let-match erased mf (MFCons _ _ _ _ _ _ _ _ e w _ mn mfr va))
  (match many r _
    ((Succ r1)
      (let-match erased nb (NthThere _ _ _ _ _ nb1))
      (let-match many (notail $ insert I P m N nn le it x px bs2 rest r1 b nb1 ibx w mfr)
        (Inserted _ _ _ _ _ _ _ _ rest2 w2 mfr2 pos lp)
        ((Found _ _ _ _ _ _ _ _ n2 it2 p2 pp2 l2 le2) (Found I P m N nn x bs u n2 it2 p2 pp2 l2 le2)))
      (let ((erased s2) (erased va2) (erased _))
        (vadd-exists (Succ m) w2 e (mf-length I P m (Succ nn) bs2 rest2 w2 mfr2) (mn-length I P m N b0 node e mn)))
      (Inserted I P m N nn x bs u (FCons I P b0 bs2 node rest2) s2
        (MFCons I P m (Succ nn) b0 bs2 node rest2 e w2 s2 (mn-weaken I P m N (Succ nn) (lt-weaken N (Succ nn) le) b0 node e mn)
          mfr2 (vadd-comm w2 e s2 va2))
        pos (lexpos-add (Succ m) pos w2 w e s2 u lp va2 (vadd-comm e w u va))))
    ((Zero)
      (let-match erased nb (NthHere _ _ _))
      (match many node _
        ((NLeaf _ _ _)
          (let-match erased mn (MNLeaf _ _ _ _ _ j p _ d ad up))
          (let ((many qs) (erased pc)) (pieces bh x ibx))
          (let ((many j1) (erased d1)) (nany bh))
          (let-match erased (nany-fn b0 j1 j d1 d) (Refl _ _))
          (let ((many pos) (erased ad1)) (sub m j1 (add-le-right p j m ad)))
          (let-match erased (add-cancel j pos p m ad1 (add-comm p j m ad)) (Refl _ _))
          (let ((many kids) (erased k) (erased mfk) (erased zpk))
            (mk-leaves I P m (Succ nn) (Succ p) (LtS p (Succ m) (add-le-left p j m ad)) qs
              (alldeg-ok qs j p m (pieces-deg b0 x qs j pc d) ad)))
          (put-head I P m N nn le x b0 bs2 rest e w u mfr va
            (NSplit I P b0 nn it x px ibx qs pc kids) k
            (MNSplit I P m (Succ nn) b0 nn it x px ibx qs pc kids k (lt-succ nn) mfk)
            pos (lexpos-unit p j m k e up zpk ad)))
        ((NSplit _ _ _ n0 it0 pt pp ib qs pc kids)
          (let-match erased mn (MNSplit _ _ _ _ _ _ _ _ _ _ _ _ _ _ l mfk))
          (let-match many (classify bh pt x qs pc ibx) (ClsIn _ _ _ r2 q nq ibq)
            ((ClsLe _ _ _ le2) (Found I P m N nn x bs u n0 it0 pt pp l le2)))
          (let-match many (notail $ insert I P m N nn le it x px qs kids r2 q nq ibq e mfk)
            (Inserted _ _ _ _ _ _ _ _ kids2 k2 mfk2 pos lp)
            ((Found _ _ _ _ _ _ _ _ n2 it2 p2 pp2 l2 le2) (Found I P m N nn x bs u n2 it2 p2 pp2 l2 le2)))
          (put-head I P m N nn le x b0 bs2 rest e w u mfr va
            (NSplit I P b0 n0 it0 pt pp ib qs pc kids2) k2
            (MNSplit I P m (Succ nn) b0 n0 it0 pt pp ib qs pc kids2 k2 (lt-trans n0 N (Succ nn) l le) mfk2)
            pos lp))))))
