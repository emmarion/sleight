(def-adts $ (Coord : -> Type)
  enum
  (many CAny : -> (Coord))
  (many CFix : (many (Nat) t) -> (Coord)))

(def-adts $ (InBox : ((List (Coord)) b) ((List (Nat)) x) -> Type)
  enum
  (many IBNil : -> (InBox (Nil (Coord)) (Nil (Nat))))
  (many IBAny : (erased (List (Coord)) b) (erased (Nat) y) (erased (List (Nat)) x) (erased (InBox b x) i)
     -> (InBox (Cons (Coord) (CAny) b) (Cons (Nat) y x)))
  (many IBFix : (erased (Nat) t) (erased (List (Coord)) b) (erased (List (Nat)) x) (erased (InBox b x) i)
     -> (InBox (Cons (Coord) (CFix t) b) (Cons (Nat) t x))))

(def-adts $ (PLe : ((List (Nat)) a) ((List (Nat)) b) -> Type)
  enum
  (many PLeNil : -> (PLe (Nil (Nat)) (Nil (Nat))))
  (many PLeCons : (erased (Nat) x y) (erased (Lt x (Succ y)) l) (erased (List (Nat)) a b) (erased (PLe a b) p)
     -> (PLe (Cons (Nat) x a) (Cons (Nat) y b))))

(def-adts $ (NAny : ((List (Coord)) b) ((Nat) j) -> Type)
  enum
  (many NAnyNil : -> (NAny (Nil (Coord)) (Zero)))
  (many NAnyAny : (erased (List (Coord)) b) (erased (Nat) j) (erased (NAny b j) d) -> (NAny (Cons (Coord) (CAny) b) (Succ j)))
  (many NAnyFix : (erased (Nat) t) (erased (List (Coord)) b) (erased (Nat) j) (erased (NAny b j) d)
     -> (NAny (Cons (Coord) (CFix t) b) j)))

(def-adts $ (Cat : ((List (List (Coord))) a) ((List (List (Coord))) b) ((List (List (Coord))) c) -> Type)
  enum
  (many CatNil : (erased (List (List (Coord))) b) -> (Cat (Nil (List (Coord))) b b))
  (many CatCons : (erased (List (Coord)) x) (erased (List (List (Coord))) a b c) (erased (Cat a b c) p)
     -> (Cat (Cons (List (Coord)) x a) b (Cons (List (Coord)) x c))))

(def-adts $ (MapCons : ((Coord) k) ((List (List (Coord))) a) ((List (List (Coord))) b) -> Type)
  enum
  (many MCNil : (erased (Coord) k) -> (MapCons k (Nil (List (Coord))) (Nil (List (Coord)))))
  (many MCCons : (erased (Coord) k) (erased (List (Coord)) x) (erased (List (List (Coord))) a b) (erased (MapCons k a b) p)
     -> (MapCons k (Cons (List (Coord)) x a) (Cons (List (Coord)) (Cons (Coord) k x) b))))

; fs : the boxes b with its first coordinate fixed to each value below y, largest first.
(def-adts $ (FixRange : ((List (Coord)) b) ((Nat) y) ((List (List (Coord))) fs) -> Type)
  enum
  (many FRZ : (erased (List (Coord)) b) -> (FixRange b (Zero) (Nil (List (Coord)))))
  (many FRS : (erased (List (Coord)) b) (erased (Nat) y) (erased (List (List (Coord))) fs) (erased (FixRange b y fs) p)
     -> (FixRange b (Succ y) (Cons (List (Coord)) (Cons (Coord) (CFix y) b) fs))))

; qs : boxes whose union is the points of b not above p.
(def-adts $ (Pieces : ((List (Coord)) b) ((List (Nat)) p) ((List (List (Coord))) qs) -> Type)
  enum
  (many PcNil : -> (Pieces (Nil (Coord)) (Nil (Nat)) (Nil (List (Coord)))))
  (many PcAny : (erased (List (Coord)) b) (erased (Nat) y) (erased (List (Nat)) p)
     (erased (List (List (Coord))) fs qs rs out) (erased (FixRange b y fs) fr) (erased (Pieces b p qs) pc)
     (erased (MapCons (CAny) qs rs) mc) (erased (Cat fs rs out) ap)
     -> (Pieces (Cons (Coord) (CAny) b) (Cons (Nat) y p) out))
  (many PcFix : (erased (Nat) t) (erased (List (Coord)) b) (erased (List (Nat)) p)
     (erased (List (List (Coord))) qs rs) (erased (Pieces b p qs) pc) (erased (MapCons (CFix t) qs rs) mc)
     -> (Pieces (Cons (Coord) (CFix t) b) (Cons (Nat) t p) rs)))

(def-fns _ $ (many fix-range : (many (List (Coord)) b) (subterm many (Nat) y) ->
    (many (List (List (Coord))) fs) (erased (FixRange b y fs) fr))
  (let-match many y (Succ y1) ((Zero) (values (Nil (List (Coord))) (FRZ b))))
  (let ((many fs1) (erased fr1)) (notail $ fix-range b y1))
  (values (Cons (List (Coord)) (Cons (Coord) (CFix y1) b) fs1) (FRS b y1 fs1 fr1)))

(def-fns _ $ (many map-cons : (many (Coord) k) (subterm many (List (List (Coord))) a) ->
    (many (List (List (Coord))) b) (erased (MapCons k a b) mc))
  (let-match many a (Cons _ x a1) ((Nil _) (values (Nil (List (Coord))) (MCNil k))))
  (let ((many b1) (erased mc1)) (notail $ map-cons k a1))
  (values (Cons (List (Coord)) (Cons (Coord) k x) b1) (MCCons k x a1 b1 mc1)))

(def-fns _ $ (many cat : (subterm many (List (List (Coord))) a) (many (List (List (Coord))) b) ->
    (many (List (List (Coord))) c) (erased (Cat a b c) ap))
  (let-match many a (Cons _ x a1) ((Nil _) (values b (CatNil b))))
  (let ((many c1) (erased ap1)) (notail $ cat a1 b))
  (values (Cons (List (Coord)) x c1) (CatCons x a1 b c1 ap1)))

(def-fns _ $ (many pieces : (subterm many (List (Coord)) b) (many (List (Nat)) p) (erased (InBox b p) ib) ->
    (many (List (List (Coord))) qs) (erased (Pieces b p qs) pc))
  (match many b _
    ((Nil _)
      (let-match erased ib (IBNil))
      (values (Nil (List (Coord))) (PcNil)))
    ((Cons _ c b1)
      (match many c _
        ((CAny)
          (let-match erased ib (IBAny _ y0 p0 ib1))
          (let-match many p (Cons _ y p1))
          (let ((many fs) (erased fr)) (fix-range b1 y))
          (let ((many qs) (erased pc)) (notail $ pieces b1 p1 ib1))
          (let ((many rs) (erased mc)) (map-cons (CAny) qs))
          (let ((many out) (erased ap)) (cat fs rs))
          (values out (PcAny b1 y p1 fs qs rs out fr pc mc ap)))
        ((CFix t)
          (let-match erased ib (IBFix _ _ p0 ib1))
          (let-match many p (Cons _ _ p1))
          (let ((many qs) (erased pc)) (notail $ pieces b1 p1 ib1))
          (let ((many rs) (erased mc)) (map-cons (CFix t) qs))
          (values rs (PcFix t b1 p1 qs rs pc mc)))))))

(def-fns _ $ (many fr-find : (erased (List (Coord)) b) (subterm many (Nat) y) (many (Nat) z) (erased (List (List (Coord))) fs)
    (erased (FixRange b y fs) fr) (erased (Lt z y) l) -> (many (Nat) r) (erased (Nth (List (Coord)) fs r (Cons (Coord) (CFix z) b)) nr))
  (let-match erased fr (FRS _ y0 fs1 fr1) (absurd (FRZ _) l))
  (let-match many y (Succ y1))
  (let-match many (nat-cmp z y1) (CLt _ _ _ _ l1)
    ((CEq _ _ _) (values (Zero) (NthHere (List (Coord)) (Cons (Coord) (CFix z) b) fs1)))
    (absurd (CGt _ _ _ _ l1) (lt-asym y1 z l1 l)))
  (let ((many r) (erased nr)) (notail $ fr-find b y1 z fs1 fr1 l1))
  (values (Succ r) (NthThere (List (Coord)) (Cons (Coord) (CFix y1) b) fs1 r _ nr)))

(def-fns _ $ (erased fr-length : (erased (List (Coord)) b) (erased (Nat) y) (erased (List (List (Coord))) fs)
    (subterm erased (FixRange b y fs) fr) -> (erased (Length (List (Coord)) fs y) l))
  (let-match erased fr (FRS _ y1 fs1 fr1) ((FRZ _) (LengthNil (List (Coord)))))
  (LengthCons (List (Coord)) _ fs1 y1 (fr-length b y1 fs1 fr1)))

(def-fns _ $ (erased nth-cat-left : (erased (List (List (Coord))) a b c) (subterm erased (Cat a b c) ap)
    (erased (Nat) r) (erased (List (Coord)) q) (erased (Nth (List (Coord)) a r q) n) -> (erased (Nth (List (Coord)) c r q) m))
  (let-match erased ap (CatCons x a1 _ c1 ap1) (absurd (CatNil _) n))
  (match erased n _
    ((NthHere _ _ _) (NthHere (List (Coord)) q c1))
    ((NthThere _ _ _ r1 _ n1) (NthThere (List (Coord)) x c1 r1 q (nth-cat-left a1 b c1 ap1 r1 q n1)))))

(def-fns _ $ (erased nth-cat-right : (erased (List (List (Coord))) a b c) (subterm erased (Cat a b c) ap)
    (erased (Nat) k r s) (erased (Length (List (Coord)) a k) la) (erased (Add k r s) ad)
    (erased (List (Coord)) q) (erased (Nth (List (Coord)) b r q) n) -> (erased (Nth (List (Coord)) c s q) m))
  (let-match erased ap (CatCons x a1 _ c1 ap1)
    ((CatNil _) (let-match erased la (LengthNil _)) (let-match erased ad (AddZero _)) n))
  (let-match erased la (LengthCons _ _ _ k1 la1))
  (let-match erased ad (AddSucc _ _ s1 ad1))
  (NthThere (List (Coord)) x c1 s1 q (nth-cat-right a1 b c1 ap1 k1 r s1 la1 ad1 q n)))

(def-fns _ $ (erased nth-mapcons : (erased (Coord) k) (erased (List (List (Coord))) a b) (subterm erased (MapCons k a b) mc)
    (erased (Nat) r) (erased (List (Coord)) q) (erased (Nth (List (Coord)) a r q) n)
    -> (erased (Nth (List (Coord)) b r (Cons (Coord) k q)) m))
  (let-match erased mc (MCCons _ x a1 b1 mc1) (absurd (MCNil _) n))
  (match erased n _
    ((NthHere _ _ _) (NthHere (List (Coord)) (Cons (Coord) k q) b1))
    ((NthThere _ _ _ r1 _ n1)
      (NthThere (List (Coord)) (Cons (Coord) k x) b1 r1 (Cons (Coord) k q) (nth-mapcons k a1 b1 mc1 r1 q n1)))))

(def-adts $ (Cls : ((List (Nat)) p) ((List (Nat)) x) ((List (List (Coord))) qs) -> Type)
  enum
  (many ClsLe : (erased (List (Nat)) p x) (erased (List (List (Coord))) qs) (erased (PLe p x) le) -> (Cls p x qs))
  (many ClsIn : (erased (List (Nat)) p x) (erased (List (List (Coord))) qs) (many (Nat) r) (erased (List (Coord)) q)
     (erased (Nth (List (Coord)) qs r q) n) (erased (InBox q x) ib) -> (Cls p x qs)))

(def-fns _ $ (many classify : (many (List (Coord)) b) (many (List (Nat)) p x) (erased (List (List (Coord))) qs)
    (subterm erased (Pieces b p qs) pc) (erased (InBox b x) ibx) -> (many (Cls p x qs) c))
  (match many b _
    ((Nil _)
      (let-match erased pc (PcNil))
      (let-match erased ibx (IBNil))
      (ClsLe p x qs (PLeNil)))
    ((Cons _ c b1)
      (match many c _
        ((CAny)
          (let-match erased pc (PcAny _ y0 p0 fs qs1 rs _ fr pc1 mc ap))
          (let-match erased ibx (IBAny _ z0 x0 ibx1))
          (let-match many p (Cons _ y p1))
          (let-match many x (Cons _ z x1))
          (let-match many (lt-dec z y) (No _ _ _ _ le)
            ((Yes _ _ _ _ l)
              (let ((many r) (erased nr)) (fr-find b1 y z fs fr l))
              (ClsIn p x qs r (Cons (Coord) (CFix z) b1) (nth-cat-left fs rs qs ap r _ nr) (IBFix z b1 x1 ibx1))))
          (let-match many (notail $ classify b1 p1 x1 qs1 pc1 ibx1) (ClsIn _ _ _ r q n ib)
            ((ClsLe _ _ _ le1) (ClsLe p x qs (PLeCons y z (le-lt-succ y z le) p1 x1 le1))))
          (let ((many s) (erased ad)) (add y r))
          (ClsIn p x qs s (Cons (Coord) (CAny) q)
            (nth-cat-right fs rs qs ap y r s (fr-length b1 y fs fr) ad _ (nth-mapcons (CAny) qs1 rs mc r q n))
            (IBAny q z x1 ib)))
        ((CFix t)
          (let-match erased pc (PcFix _ _ p0 qs1 rs pc1 mc))
          (let-match erased ibx (IBFix _ _ x0 ibx1))
          (let-match many p (Cons _ _ p1))
          (let-match many x (Cons _ _ x1))
          (let-match many (notail $ classify b1 p1 x1 qs1 pc1 ibx1) (ClsIn _ _ _ r q n ib)
            ((ClsLe _ _ _ le1) (ClsLe p x qs (PLeCons t t (lt-succ t) p1 x1 le1))))
          (ClsIn p x qs r (Cons (Coord) (CFix t) q) (nth-mapcons (CFix t) qs1 rs mc r q n) (IBFix t q x1 ib)))))))
