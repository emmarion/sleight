; The uses of minimality in birkhoff.v and coloring.v, with minimality as data: each step that Coq proves by colouring
; smaller maps gives here a Reduces (induct.sl) to the smaller maps it names. Load after birkfit.sl.

(def-fns _ $ (erased mp-app : (subterm erased (List (Mp)) xs) (erased (List (Mp)) ys) -> (erased (List (Mp)) zs) (erased (App (Mp) xs ys zs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values ys (CatNil _ ys))))
  (let ((erased zs1) (erased r1)) (mp-app xs1 ys))
  (values (Cons _ x zs1) (CatCons _ x xs1 ys zs1 r1)))

(def-fns _ $ (erased mpcols-split : (erased (List (Mp)) xs ys zs) (subterm erased (App (Mp) xs ys zs) ap) (erased (MpCols zs) c)
    -> (erased (MpCols xs) cx) (erased (MpCols ys) cy))
  (let-match erased ap (CatCons _ x xs1 _ zs1 ap1) ((CatNil _ _) (values (MpcNil) c)))
  (let-match erased c (MpcCons d e n f ks _ cl c1))
  (let ((erased cx) (erased cy)) (mpcols-split xs1 ys zs1 ap1 c1))
  (values (MpcCons d e n f ks xs1 cl cx) cy))

(def-fns _ $ (erased smaller-app : (erased (Nat) d) (erased (List (Mp)) xs ys zs) (subterm erased (App (Mp) xs ys zs) ap) (erased (Smaller d xs) sx)
    (erased (Smaller d ys) sy) -> (erased (Smaller d zs) r))
  (let-match erased ap (CatCons _ x xs1 _ zs1 ap1) ((CatNil _ _) sy))
  (let-match erased sx (SmallerCons _ d2 e2 n2 f2 _ pb lt2 sx1))
  (SmallerCons d d2 e2 n2 f2 zs1 pb lt2 (smaller-app d xs1 ys zs1 ap1 sx1 sy)))

; What birkhoff-ring needs, besides the colourings of the maps ms the check names for a ring of h + 2 darts nontrivial for m.
(def-adts $ (BirkW : ((Nat) d) ((List (Nat)) e n f) ((List (Mp)) ms) -> Type)
  enum
  (many MkBirkW : (erased (Nat) d x0 h m n0 dd1 dd2) (erased (List (Nat)) e n f p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2) (erased (List (Ctree)) ts)
      (erased (List (Mp)) ms1 ms2 ms) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (Hypermap d e n f) hm) (erased (Genus d e n f (Zero)) gen)
      (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu) (erased (Connected d e n f) cn)
      (erased (NoColoring e f) nc) (erased (Length (Nat) (Cons (Nat) x0 p) (Succ (Succ h))) lr)
      (erased (CEv ctu (ESStart)) ce) (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge)
      (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc) (erased (BK h ts ctu gtu n0 ctu gtu) bk)
      (erased (BRing d e n f x0 p dd1 dd2 ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2) br) (erased (BNeed d dd1 h m ed1 nd1 fd1 bd1 ts ms1) n1)
      (erased (BNeed d dd2 h m ed2 nd2 fd2 bd2 ts ms2) n2) (erased (App (Mp) ms1 ms2 ms) ap) -> (BirkW d e n f ms)))

(def-fns _ $ (erased birk-glue : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (BirkW d e n f ms) w)
    (erased (MpCols ms) cs) -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) c))
  (let-match erased w (MkBirkW _ x0 h m n0 dd1 dd2 _ _ _ p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 ts ms1 ms2 _ ctu gtu hm gen pl cu cn nc lr ce ge gc bk br n1 n2 ap))
  (let-match erased nc (MkNoColoring d2 _ _ nce lf2))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f hm))
  (let-match erased (length-fn (Nat) f d2 d lf2 lf) (Refl _ _))
  (let ((erased c1) (erased c2)) (mpcols-split ms1 ms2 ms ap cs))
  (match erased (birkhoff-ring d x0 h m n0 dd1 dd2 e n f p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 ts ms1 ms2 ctu gtu hm gen pl cu cn nce lr ce ge gc bk br n1 n2 c1 c2)
    (((List (Nat)) ks) ((FourColoring e f ks) c))))

(def-fns _ $ (erased lt-succ-of : (erased (Nat) a b) (erased (Lt a b) p) -> (erased (Nat) b1) (erased (Eq (Nat) b (Succ b1)) e))
  (match erased p _ ((LtZ b1) (values b1 (Refl _ b))) ((LtS _ b1 _) (values b1 (Refl _ b)))))

(def-fns _ $ (erased lt-ls : (erased (Nat) a c b) (subterm erased (Lt a c) p) (erased (Lt c (Succ b)) q) -> (erased (Lt a b) r))
  (match erased p _
    ((LtZ c1)
      (let-match erased q (LtS _ _ q1))
      (let ((erased b1) (erased eb)) (lt-succ-of c1 b q1))
      (let-match erased eb (Refl _ _))
      (LtZ b1))
    ((LtS a1 c1 p1)
      (let-match erased q (LtS _ _ q1))
      (let ((erased b1) (erased eb)) (lt-succ-of c1 b q1))
      (let-match erased eb (Refl _ _))
      (LtS a1 b1 (lt-ls a1 c1 b1 p1 q1)))))

(def-fns _ $ (erased lt-tr : (erased (Nat) a c b) (erased (Lt a c) p) (erased (Lt c b) q) -> (erased (Lt a b) r))
  (let ((erased b1) (erased eb)) (lt-succ-of c b q))
  (let-match erased eb (Refl _ _))
  (lt-succ-left a b (LtS a b1 (lt-ls a c b1 p q))))

(def-fns _ $ (erased bkmode-fn : (erased (Nat) k m1 m2) (erased (BkMode k m1) b1) (erased (BkMode k m2) b2) -> (erased (Eq (Nat) m1 m2) r))
  (match erased b1 _
    ((BMLow _ l1) (match erased b2 _ ((BMLow _ _) (Refl _ m1)) (absurd (BMFive) (lt-irrefl k l1))))
    ((BMFive) (match erased b2 _ (absurd (BMLow _ l2) (lt-irrefl k l2)) ((BMFive) (Refl _ m1))))))

; The theorem Birkhoff of birkhoff.v, with minimality as data: in a planar bridgeless plain cubic connected map that the search
; finds uncolourable, a ring of k darts, k below 6, nontrivial for the m of BkMode k m, gives a reduction. The induction on
; the ring size follows birkhoff-maps' Shorter rings until birkhoff-maps names the maps of the check, so the one Reduces
; names every map needed.
(def-fns _ $ (erased birkhoff-go : (erased (Level) B) (erased (Predates (Level) (level-of birk-glue) B) pb) (erased (Nat) d x0 k m)
    (erased (List (Nat)) e n f p) (subterm erased (Nat) b) (erased (Lt k b) lb)
    (erased (BirkhoffChecks) bks) (erased (Hypermap d e n f) hm) (erased (Genus d e n f (Zero)) gen) (erased (Bridgeless d e n f) bl)
    (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu) (erased (Connected d e n f) cn)
    (erased (NoColoring e f) nc) (erased (Ring e f x0 p) rg) (erased (Length (Nat) (Cons (Nat) x0 p) k) lr) (erased (Lt k 6) l6) (erased (BkMode k m) md)
    (erased (NonTrivial d e n f (Cons (Nat) x0 p) m) nt) -> (erased (Reduces B d e n f) r))
  (unary 6)
  (let ((erased h) (erased m2) (erased eq) (erased bc) (erased md2)) (birkhoff-check-at k bks (ring-two d x0 k e n f p hm bl rg lr) l6))
  (let-match erased eq (Refl _ _))
  (let-match erased (bkmode-fn k m m2 md md2) (Refl _ _))
  (let-match erased bc (MkBirkhoffCheck _ _ n0 cps ts ctu gtu ce ge gc bb bk))
  (match erased (birkhoff-maps d h m x0 e n f p cps ts hm gen bl pl cu cn rg lr nt bb) _
    ((BKShort _ _ _ _ _ _ _ _ _ sh)
      (let-match erased sh (MkShorter _ _ y0 k2 _ _ _ Q rq nq lq lt))
      (let-match erased lb (LtS _ b1 lb1))
      (birkhoff-go B pb d y0 k2 (Zero) e n f Q b1 (lt-ls k2 k b1 lt lb) bks hm gen bl pl cu cn nc rq lq (lt-tr k2 k 6 lt l6)
        (BMLow k2 (lt-ls k2 k (Succ (Succ (Succ (Succ (Succ (Zero)))))) lt l6)) nq))
    ((BKMaps _ _ _ _ dd1 dd2 _ _ _ _ ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 _ ms1 ms2 br n1 n2)
      (let ((erased ms) (erased ap)) (mp-app ms1 ms2))
      (MkReduces B d e n f ms (smaller-app d ms1 ms2 ms ap (bneed-smaller d dd1 h m ed1 nd1 fd1 bd1 ts ms1 n1) (bneed-smaller d dd2 h m ed2 nd2 fd2 bd2 ts ms2 n2))
        (MkColorFrom B (level-of birk-glue) d e n f ms BirkW
          (MkBirkW d x0 h m n0 dd1 dd2 e n f p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 ts ms1 ms2 ms ctu gtu hm gen pl cu cn nc lr ce ge gc bk br n1 n2 ap)
          pb birk-glue)))))

(def-fns _ $ (erased birkhoff-reduces : (erased (Level) B) (erased (Predates (Level) (level-of birk-glue) B) pb) (erased (Nat) d x0 k m)
    (erased (List (Nat)) e n f p) (erased (BirkhoffChecks) bks) (erased (Hypermap d e n f) hm)
    (erased (Genus d e n f (Zero)) gen) (erased (Bridgeless d e n f) bl) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu) (erased (Connected d e n f) cn) (erased (NoColoring e f) nc) (erased (Ring e f x0 p) rg)
    (erased (Length (Nat) (Cons (Nat) x0 p) k) lr) (erased (Lt k 6) l6) (erased (BkMode k m) md) (erased (NonTrivial d e n f (Cons (Nat) x0 p) m) nt)
    -> (erased (Reduces B d e n f) r))
  (birkhoff-go B pb d x0 k m e n f p 6 l6 bks hm gen bl pl cu cn nc rg lr l6 md nt))
