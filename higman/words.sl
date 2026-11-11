(def-adts $ (Other : ((Bool) c) ((Bool) d) -> Type)
  enum
  (many OtherTF : -> (Other (BTrue) (BFalse)))
  (many OtherFT : -> (Other (BFalse) (BTrue))))

; v : x copies of d, then t.
(def-adts $ (RepPre : ((Bool) d) ((Nat) x) ((List (Bool)) t) ((List (Bool)) v) -> Type)
  enum
  (many RPZ : (erased (Bool) d) (erased (List (Bool)) t) -> (RepPre d (Zero) t t))
  (many RPS : (erased (Bool) d) (erased (Nat) x) (erased (List (Bool)) t v) (erased (RepPre d x t v) r)
     -> (RepPre d (Succ x) t (Cons (Bool) d v))))

; v does not embed w = c1 ... cm; e = (e1 ... ek+1) with v = d1^e1 c1 ... dk^ek ck dk+1^ek+1, di the other letter than ci.
(def-adts $ (Av : ((List (Bool)) w) ((List (Nat)) e) ((List (Bool)) v) -> Type)
  enum
  (many AvEnd : (erased (Bool) c d) (erased (List (Bool)) w) (erased (Other c d) o) (erased (Nat) x) (erased (List (Bool)) v)
     (erased (RepPre d x (Nil (Bool)) v) r) -> (Av (Cons (Bool) c w) (Cons (Nat) x (Nil (Nat))) v))
  (many AvStep : (erased (Bool) c d) (erased (List (Bool)) w) (erased (Other c d) o) (erased (Nat) x) (erased (List (Nat)) e)
     (erased (List (Bool)) v1 v) (erased (Av w e v1) a) (erased (RepPre d x (Cons (Bool) c v1) v) r)
     -> (Av (Cons (Bool) c w) (Cons (Nat) x e) v)))

(def-adts $ (Scan : ((Bool) c) ((Bool) d) ((List (Bool)) v) -> Type)
  enum
  (many ScanHit : (erased (Bool) c d) (erased (List (Bool)) v) (many (Nat) x) (many (List (Bool)) v1)
     (erased (RepPre d x (Cons (Bool) c v1) v) r) -> (Scan c d v))
  (many ScanEnd : (erased (Bool) c d) (erased (List (Bool)) v) (many (Nat) x) (erased (RepPre d x (Nil (Bool)) v) r)
     -> (Scan c d v)))

(def-adts $ (Which : ((Bool) c) ((Bool) d) ((Bool) b) -> Type)
  enum
  (many IsC : (erased (Bool) c d) -> (Which c d c))
  (many IsD : (erased (Bool) c d) -> (Which c d d)))

(def-fns _ $ (many which : (many (Bool) c) (erased (Bool) d) (erased (Other c d) o) (many (Bool) b) -> (many (Which c d b) w))
  (match many c _
    ((BTrue) (let-match erased o (OtherTF)) (match many b _ ((BTrue) (IsC c d)) ((BFalse) (IsD c d))))
    ((BFalse) (let-match erased o (OtherFT)) (match many b _ ((BTrue) (IsD c d)) ((BFalse) (IsC c d))))))

(def-fns _ $ (many scan : (many (Bool) c) (erased (Bool) d) (erased (Other c d) o) (subterm many (List (Bool)) v) ->
    (many (Scan c d v) s))
  (let-match many v (Cons _ b v1) ((Nil _) (ScanEnd c d v (Zero) (RPZ d v))))
  (let-match many (which c d o b) (IsD _ _) ((IsC _ _) (ScanHit c d v (Zero) v1 (RPZ d v))))
  (match many (notail $ scan c d o v1) _
    ((ScanHit _ _ _ x v2 r) (ScanHit c d v (Succ x) v2 (RPS d x (Cons (Bool) c v2) v1 r)))
    ((ScanEnd _ _ _ x r) (ScanEnd c d v (Succ x) (RPS d x (Nil (Bool)) v1 r)))))

(def-adts $ (Dec2 : ((List (Bool)) w) ((List (Bool)) v) -> Type)
  enum
  (many DEmb : (erased (List (Bool)) w v) (erased (Emb w v) e) -> (Dec2 w v))
  (many DAv : (erased (List (Bool)) w v) (many (List (Nat)) e) (erased (Av w e v) a) -> (Dec2 w v)))

(def-fns _ $ (many other : (many (Bool) c) -> (many (Bool) d) (erased (Other c d) o))
  (match many c _ ((BTrue) (values (BFalse) (OtherTF))) ((BFalse) (values (BTrue) (OtherFT)))))

(def-fns _ $ (erased emb-skip-pre : (erased (Bool) d) (erased (Nat) x) (erased (List (Bool)) u t v)
    (subterm erased (RepPre d x t v) r) (erased (Emb u t) e) -> (erased (Emb u v) e2))
  (let-match erased r (RPS _ x1 _ v1 r1) ((RPZ _ _) e))
  (EmbSkip d u v1 (emb-skip-pre d x1 u t v1 r1 e)))

(def-fns _ $ (many decompose : (subterm many (List (Bool)) w) (many (List (Bool)) v) -> (many (Dec2 w v) r))
  (let-match many w (Cons _ c w1) ((Nil _) (DEmb w v (EmbNil v))))
  (let ((many d) (erased o)) (other c))
  (let-match many (scan c d o v) (ScanHit _ _ _ x v1 r)
    ((ScanEnd _ _ _ x r) (DAv w v (Cons (Nat) x (Nil (Nat))) (AvEnd c d w1 o x v r))))
  (match many (notail $ decompose w1 v1) _
    ((DEmb _ _ e) (DEmb w v (emb-skip-pre d x w (Cons (Bool) c v1) v r (EmbKeep c w1 v1 e))))
    ((DAv _ _ e a) (DAv w v (Cons (Nat) x e) (AvStep c d w1 o x e v1 v a r)))))

(def-fns _ $ (erased rep-mono : (erased (Bool) d) (erased (Nat) x x2) (erased (List (Bool)) t t2 v v2)
    (erased (RepPre d x t v) r) (subterm erased (RepPre d x2 t2 v2) r2) (erased (Lt x (Succ x2)) l) (erased (Emb t t2) e)
    -> (erased (Emb v v2) e2))
  (let-match erased r2 (RPS _ x3 _ v3 r3)
    ((RPZ _ _)
      (let-match erased l (LtZ _) (absurd (LtS _ _ l1) l1))
      (let-match erased r (RPZ _ _))
      e))
  (let-match erased r (RPS _ x1 _ v1 r1) ((RPZ _ _) (EmbSkip d v v3 (rep-mono d (Zero) x3 t t2 v v3 r r3 (LtZ x3) e))))
  (let-match erased l (LtS _ _ l1))
  (EmbKeep d v1 v3 (rep-mono d x1 x3 t t2 v1 v3 r1 r3 l1 e)))

(def-fns _ $ (erased other-fn : (erased (Bool) c d d2) (erased (Other c d) o) (erased (Other c d2) o2) -> (erased (Eq (Bool) d d2) q))
  (match erased o _
    ((OtherTF) (let-match erased o2 (OtherTF)) (Refl (Bool) d))
    ((OtherFT) (let-match erased o2 (OtherFT)) (Refl (Bool) d))))

(def-fns _ $ (erased av-mono : (erased (List (Bool)) w v v2) (erased (List (Nat)) e e2) (subterm erased (Av w e v) a)
    (erased (Av w e2 v2) a2) (erased (PLe e e2) le) -> (erased (Emb v v2) em))
  (match erased a _
    ((AvEnd c d w1 o x _ r)
      (let-match erased le (PLeCons _ x2 l _ e3 le1))
      (let-match erased le1 (PLeNil))
      (let-match erased a2 (AvEnd _ d2 _ o2 _ _ r2) (absurd (AvStep _ _ _ _ _ _ _ _ a3 _) a3))
      (let-match erased (other-fn c d d2 o o2) (Refl _ _))
      (rep-mono d x x2 (Nil (Bool)) (Nil (Bool)) v v2 r r2 l (EmbNil (Nil (Bool)))))
    ((AvStep c d w1 o x e1 v1 _ a1 r)
      (let-match erased le (PLeCons _ x2 l _ e3 le1))
      (let-match erased a2 (AvStep _ d2 _ o2 _ _ v3 _ a3 r2)
        (absurd (AvEnd _ _ _ _ _ _ _) (let-match erased le1 (PLeNil)) (match erased a1 _)))
      (let-match erased (other-fn c d d2 o o2) (Refl _ _))
      (rep-mono d x x2 (Cons (Bool) c v1) (Cons (Bool) c v3) v v2 r r2 l
        (EmbKeep c v1 v3 (av-mono w1 v1 v3 e1 e3 a1 a3 le1))))))

(def-fns _ $ (erased av-length : (erased (List (Bool)) w v) (erased (List (Nat)) e) (erased (Nat) m)
    (subterm erased (Av w e v) a) (erased (Length (Bool) w m) lw) -> (erased (Nat) n) (erased (Length (Nat) e n) le) (erased (Lt n (Succ m)) l))
  (let-match erased lw (LengthCons _ _ w1 m1 lw1) (absurd (LengthNil _) (match erased a _)))
  (let-match erased a (AvStep _ _ _ _ x e1 v1 _ a1 _)
    ((AvEnd _ _ _ _ x _ _)
      (values (Succ (Zero)) (LengthCons (Nat) x (Nil (Nat)) (Zero) (LengthNil (Nat))) (LtS (Zero) (Succ m1) (LtZ m1)))))
  (let ((erased n1) (erased le1) (erased l1)) (av-length w1 v1 e1 m1 a1 lw1))
  (values (Succ n1) (LengthCons (Nat) x e1 n1 le1) (LtS n1 (Succ m1) l1)))

(def-fns _ $ (many all-any : (subterm many (Nat) k) -> (many (List (Coord)) b) (erased (Repeat (Coord) k (CAny) b) r))
  (let-match many k (Succ k1) ((Zero) (values (Nil (Coord)) (RepeatNil (Coord) (CAny)))))
  (let ((many b1) (erased r1)) (notail $ all-any k1))
  (values (Cons (Coord) (CAny) b1) (RepeatCons (Coord) k1 (CAny) b1 r1)))

(def-fns _ $ (erased all-any-nany : (erased (Nat) k) (erased (List (Coord)) b) (subterm erased (Repeat (Coord) k (CAny) b) r)
    -> (erased (NAny b k) d))
  (let-match erased r (RepeatCons _ k1 _ b1 r1) ((RepeatNil _ _) (NAnyNil)))
  (NAnyAny b1 k1 (all-any-nany k1 b1 r1)))

(def-fns _ $ (erased all-any-inbox : (erased (Nat) k) (erased (List (Coord)) b) (erased (List (Nat)) x)
    (subterm erased (Repeat (Coord) k (CAny) b) r) (erased (Length (Nat) x k) l) -> (erased (InBox b x) ib))
  (let-match erased r (RepeatCons _ k1 _ b1 r1) ((RepeatNil _ _) (let-match erased l (LengthNil _)) (IBNil)))
  (let-match erased l (LengthCons _ y x1 _ l1))
  (IBAny b1 y x1 (all-any-inbox k1 b1 x1 r1 l1)))

; bs : the boxes of every point of length k, k+1, ..., k+d, in that order.
(def-adts $ (Roots : ((Nat) k) ((Nat) d) ((List (List (Coord))) bs) -> Type)
  enum
  (many RootsZ : (erased (Nat) k) (erased (List (Coord)) b) (erased (Repeat (Coord) k (CAny) b) r)
     -> (Roots k (Zero) (Cons (List (Coord)) b (Nil (List (Coord))))))
  (many RootsS : (erased (Nat) k d) (erased (List (Coord)) b) (erased (List (List (Coord))) bs)
     (erased (Repeat (Coord) k (CAny) b) r) (erased (Roots (Succ k) d bs) rs) -> (Roots k (Succ d) (Cons (List (Coord)) b bs))))

(def-fns _ $ (many roots : (many (Nat) k) (subterm many (Nat) d) -> (many (List (List (Coord))) bs) (erased (Roots k d bs) rs))
  (let ((many b) (erased r)) (all-any k))
  (let-match many d (Succ d1) ((Zero) (values (Cons (List (Coord)) b (Nil (List (Coord)))) (RootsZ k b r))))
  (let ((many bs1) (erased rs1)) (notail $ roots (Succ k) d1))
  (values (Cons (List (Coord)) b bs1) (RootsS k d1 b bs1 r rs1)))

(def-fns _ $ (erased roots-nth : (erased (Nat) k d i n) (erased (List (List (Coord))) bs) (subterm erased (Roots k d bs) rs)
    (erased (Add i k n) ad) (erased (Lt i (Succ d)) l) ->
    (erased (List (Coord)) b) (erased (Nth (List (Coord)) bs i b) nb) (erased (Repeat (Coord) n (CAny) b) r))
  (let-match erased ad (AddSucc i1 _ n1 ad1)
    ((AddZero _)
      (match erased rs _
        ((RootsZ _ b r) (values b (NthHere (List (Coord)) b (Nil (List (Coord)))) r))
        ((RootsS _ _ b bs1 r _) (values b (NthHere (List (Coord)) b bs1) r)))))
  (let-match erased rs (RootsS _ d1 b0 bs1 _ rs1) (absurd (RootsZ _ _ _) (let-match erased l (LtS _ _ l1)) l1))
  (let-match erased l (LtS _ _ l1))
  (let ((erased b) (erased nb) (erased r)) (roots-nth (Succ k) d1 i1 n bs1 rs1 (add-succ-right i1 k n1 ad1) l1))
  (values b (NthThere (List (Coord)) b0 bs1 i1 b nb) r))

(def-fns _ $ (erased roots-ok : (erased (Nat) k d m) (erased (List (List (Coord))) bs) (subterm erased (Roots k d bs) rs)
    (erased (Add k d m) ad) -> (erased (LeafOK bs m (Zero)) ok))
  (let-match erased rs (RootsS _ d1 b bs1 r rs1)
    ((RootsZ _ b r)
      (LOCons b (Nil (List (Coord))) m (Zero) k (Zero) (all-any-nany k b r) (add-comm k (Zero) m ad) (LtZ (Zero))
        (LONil m (Zero)))))
  (let ((erased c) (erased e) (erased ad1)) (add-succ-right-inv k d1 m ad))
  (let-match erased e (Refl _ _))
  (LOCons b bs1 m (Zero) k d (all-any-nany k b r) (add-comm k d m ad) (LtZ d)
    (roots-ok (Succ k) d1 m bs1 rs1 (AddSucc k d1 c ad1))))
