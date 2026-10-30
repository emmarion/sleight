; The sector lists of fit.sl read off a hypermap of hypermap.sl, after fitp of part.v: the sector of a dart y has the
; arity of the spoke edge y, of the hat edge (face^2 (edge y)) and of the fans edge (face^(3+k) (edge y)) for k below the
; spoke arity minus 5; the sector list of y has one sector per dart of its face, from y on. ks is an OrderList of the face
; permutation. Load after faces.sl, the unav files and fit.sl, dbound.sl, hubcapc.sl.

(def-adts $ (Geo : ((Nat) d) ((List (Nat)) e n f ks) -> Type)
  enum
  (many MkGeo : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h) (erased (AllOrder d e (Succ (Succ (Zero)))) pe)
      (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cn) (erased (OrderList d f ks) ol) (erased (Above ks 4) pa) -> (Geo d e n f ks)))

(def-adts $ (FansAt : ((List (Nat)) e f ks) ((Nat) z m) ((List (Nat)) fs) -> Type)
  enum
  (many FAZ : (erased (List (Nat)) e f ks) (erased (Nat) z) -> (FansAt e f ks z (Zero) (Nil (Nat))))
  (many FAS : (erased (List (Nat)) e f ks) (erased (Nat) z u a z1 m) (erased (List (Nat)) fs) (erased (Nth (Nat) e z u) pu) (erased (Nth (Nat) ks u a) pa)
      (erased (Nth (Nat) f z z1) pz) (erased (FansAt e f ks z1 m fs) rest) -> (FansAt e f ks z (Succ m) (Cons (Nat) a fs))))

(def-adts $ (SecAt : ((List (Nat)) e f ks) ((Nat) y) ((Sec) o) -> Type)
  enum
  (many MkSecAt : (erased (List (Nat)) e f ks) (erased (Nat) y z a w u h z3 m) (erased (List (Nat)) fs) (erased (Nth (Nat) e y z) pz)
      (erased (Nth (Nat) ks z a) pa) (erased (Iter f 2 z w) pw) (erased (Nth (Nat) e w u) pu) (erased (Nth (Nat) ks u h) ph) (erased (Iter f 3 z z3) p3)
      (erased (Monus a 5 m) mo) (erased (FansAt e f ks z3 m fs) pfs) -> (SecAt e f ks y (MkSec a h fs))))

(def-adts $ (ObsAt : ((List (Nat)) e f ks) ((Nat) y n) ((List (Sec)) os) -> Type)
  enum
  (many OANil : (erased (List (Nat)) e f ks) (erased (Nat) y) -> (ObsAt e f ks y (Zero) (Nil (Sec))))
  (many OACons : (erased (List (Nat)) e f ks) (erased (Nat) y y1 n) (erased (Sec) o) (erased (List (Sec)) os) (erased (SecAt e f ks y o) so)
      (erased (Nth (Nat) f y y1) py) (erased (ObsAt e f ks y1 n os) rest) -> (ObsAt e f ks y (Succ n) (Cons (Sec) o os))))

; y fits p exactly (exact_fitp of part.v): p has one subpart per dart of the face of y, and the sectors fit them.
(def-adts $ (ExactAt : ((List (Nat)) e f ks) ((Nat) y) ((List (Sub)) p) -> Type)
  enum
  (many MkExactAt : (erased (List (Nat)) e f ks) (erased (Nat) y n) (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (Nth (Nat) ks y n) pn)
      (erased (ObsAt e f ks y n os) ob) (erased (Exact os p) x) -> (ExactAt e f ks y p)))

(def-fns _ $ (erased above-nth : (erased (List (Nat)) ks) (erased (Nat) b i k) (erased (Above ks b) ab) (subterm erased (Nth (Nat) ks i k) p)
    -> (erased (Lt b k) r))
  (let-match erased ab (AboveCons ks1 k0 _ l ab1) (absurd (AboveNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) l))
  (above-nth ks1 b i1 k ab1 p1))

(def-fns _ $ (erased fans-ok : (erased (List (Nat)) e f ks fs) (erased (Nat) z m) (erased (Above ks 4) ab) (subterm erased (FansAt e f ks z m fs) fa)
    -> (erased (All (Nat) Pent fs) r) (erased (Length (Nat) fs m) l))
  (let-match erased fa (FAS _ _ _ _ u a z1 m1 fs1 pu pa pz fa1) ((FAZ _ _ _ _) (values (AllNil _ Pent) (LengthNil _))))
  (let ((erased r1) (erased l1)) (fans-ok e f ks fs1 z1 m1 ab fa1))
  (values (AllCons _ Pent a fs1 (MkPent a (above-nth ks 4 u a ab pa)) r1) (LengthCons _ a fs1 m1 l1)))

(def-fns _ $ (erased sec-ok : (erased (List (Nat)) e f ks) (erased (Nat) y) (erased (Sec) o) (erased (Above ks 4) ab) (erased (SecAt e f ks y o) so)
    -> (erased (SecOk o) r))
  (let-match erased so (MkSecAt _ _ _ _ z a w u h z3 m fs pz pa pw pu ph p3 mo pfs))
  (let ((erased la)) (above-nth ks 4 z a ab pa))
  (let-match erased mo (MoAdd _ _ _ am) (absurd (MoNeg _ _ l) (lt-le-absurd 4 a la l)))
  (let ((erased r1) (erased l1)) (fans-ok e f ks fs z3 m ab pfs))
  (MkSecOk a h m fs la (above-nth ks 4 u h ab ph) r1 l1 am))

(def-fns _ $ (erased obs-ok : (erased (List (Nat)) e f ks) (erased (Nat) y n) (erased (List (Sec)) os) (erased (Above ks 4) ab)
    (subterm erased (ObsAt e f ks y n os) ob) -> (erased (All (Sec) SecOk os) r))
  (let-match erased ob (OACons _ _ _ _ y1 n1 o os1 so py ob1) ((OANil _ _ _ _) (AllNil _ SecOk)))
  (AllCons _ SecOk o os1 (sec-ok e f ks y o ab so) (obs-ok e f ks y1 n1 os1 ab ob1)))

(def-fns _ $ (erased obs-cut : (erased (List (Nat)) e f ks) (erased (Nat) y n k) (erased (List (Sec)) os pre post) (subterm erased (ObsAt e f ks y n os) ob)
    (erased (CutAt (Sec) k os pre post) c) (erased (Lt k (Succ n)) lk)
    -> (erased (Nat) z m) (erased (Iter f k y z) it) (erased (ObsAt e f ks y k pre) o1) (erased (ObsAt e f ks z m post) o2) (erased (Add k m n) a))
  (match erased c _
    ((CutAtZ _ _) (values y n (ItZ f y) (OANil e f ks y) ob (AddZero n)))
    (absurd (CutAtNil _ k1) (let-match erased ob (OANil _ _ _ _)) (let-match erased lk (LtS _ _ l0)) l0)
    ((CutAtS _ k1 o os1 pre1 _ c1)
      (let-match erased ob (OACons _ _ _ _ y1 n1 _ _ so py ob1))
      (let-match erased lk (LtS _ _ lk1))
      (let ((erased z) (erased m) (erased it) (erased o1) (erased o2) (erased a)) (obs-cut e f ks y1 n1 k1 os1 pre1 post ob1 c1 lk1))
      (values z m (ItS f k1 y y1 z py it) (OACons e f ks y y1 k1 o pre1 so py o1) o2 (AddSucc k1 m n1 a)))))

(def-fns _ $ (erased obs-app : (erased (List (Nat)) e f ks) (erased (Nat) y z a b c) (erased (List (Sec)) os1 os2 os) (subterm erased (ObsAt e f ks y a os1) o1)
    (erased (Iter f a y z) it) (erased (ObsAt e f ks z b os2) o2) (erased (LApp (Sec) os1 os2 os) ap) (erased (Add a b c) ab) -> (erased (ObsAt e f ks y c os) r))
  (let-match erased o1 (OACons _ _ _ _ y1 a1 o os3 so py o3)
    ((OANil _ _ _ _) (let-match erased it (ItZ _ _)) (let-match erased ap (LAppNil _ _)) (let-match erased ab (AddZero _)) o2))
  (let-match erased it (ItS _ _ _ y2 _ py2 it1))
  (let-match erased (nth-fn _ f y y1 y2 py py2) (Refl _ _))
  (let-match erased ap (LAppCons _ _ _ _ os4 ap1))
  (let-match erased ab (AddSucc _ _ c1 ab1))
  (OACons e f ks y y1 c1 o os4 so py (obs-app e f ks y1 z a1 b c1 os3 os2 os4 o3 it1 o2 ap1 ab1)))

(def-fns _ $ (erased obs-rot : (erased (List (Nat)) e f ks) (erased (Nat) y n k) (erased (List (Sec)) os os2) (erased (ObsAt e f ks y n os) ob)
    (erased (Iter f n y y) cy) (erased (Rot (Sec) k os os2) ro) (erased (Lt k (Succ n)) lk) -> (erased (Nat) z) (erased (Iter f k y z) it)
    (erased (ObsAt e f ks z n os2) r))
  (let-match erased ro (MkRot _ _ _ _ pre post c ap))
  (let ((erased z) (erased m) (erased it) (erased o1) (erased o2) (erased a)) (obs-cut e f ks y n k os pre post ob c lk))
  (let ((erased z2) (erased it2) (erased it3)) (iter-split f k m n y y a cy))
  (let-match erased (iter-fn f k y z z2 it it2) (Refl _ _))
  (values z it (obs-app e f ks z y m k n post pre os2 o2 it3 o1 ap (add-comm k m n a))))

; exact_fitp is kept by rotating the part and stepping along the face (fitp_rot of part.v).
(def-fns _ $ (erased exact-rot-at : (erased (Nat) d y a k) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p p2) (erased (Geo d e n f ks) g)
    (erased (Lt y d) ly) (erased (Nth (Nat) ks y a) pa) (erased (Lt k (Succ a)) lk) (erased (ExactAt e f ks y p) x) (erased (Rot (Sub) k p p2) rp)
    -> (erased (Nat) z) (erased (Iter f k y z) it) (erased (Lt z d) lz) (erased (ExactAt e f ks z p2) r))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ ol ab))
  (let-match erased x (MkExactAt _ _ _ _ a2 os _ pa2 ob ex))
  (let-match erased (nth-fn _ ks y a a2 pa pa2) (Refl _ _))
  (let ((erased os2) (erased ro)) (rot-c _ k os))
  (let ((erased z) (erased it) (erased ob2)) (obs-rot e f ks y a k os os2 ob (face-cycle d y a f ks ol ly pa) ro lk))
  (let ((erased z2) (erased it2) (erased lz) (erased pz)) (face-walk d y a e n f ks h ol k ly pa))
  (let-match erased (iter-fn f k y z2 z it2 it) (Refl _ _))
  (values z it lz (MkExactAt e f ks z a os2 p2 pz ob2 (exact-rot os os2 p p2 k ex ro rp))))

(def-fns _ $ (erased split-len : (erased (Nat) k m) (erased (List (Sub)) p ql qh) (subterm erased (PartSplit k p ql qh) w) (erased (Length (Sub) p m) l)
    -> (erased (Length (Sub) ql m) rl) (erased (Length (Sub) qh m) rh))
  (match erased w _
    ((PSKeep _ _) (values l l))
    ((PSHere _ x zl zh p1 _) (let-match erased l (LengthCons _ _ _ m1 l1)) (values (LengthCons _ zl p1 m1 l1) (LengthCons _ zh p1 m1 l1)))
    ((PSThere _ x p1 ql1 qh1 w1)
      (let-match erased l (LengthCons _ _ _ m1 l1))
      (let ((erased r1) (erased r2)) (split-len k m1 p1 ql1 qh1 w1 l1))
      (values (LengthCons _ x ql1 m1 r1) (LengthCons _ x qh1 m1 r2)))))

; A dart that fits p exactly fits one of the two halves of a split of p (fitp_split of part.v, read as a cover).
(def-fns _ $ (erased exact-split-at : (erased (Nat) d y k) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p ql qh) (erased (Geo d e n f ks) g)
    (erased (ExactAt e f ks y p) x) (erased (PartSplit k p ql qh) w) -> (erased (Or (ExactAt e f ks y ql) (ExactAt e f ks y qh)) r))
  (let-match erased g (MkGeo _ _ _ _ _ _ _ _ _ ab))
  (let-match erased x (MkExactAt _ _ _ _ a os _ pa ob ex))
  (let-match erased ex (MkExact _ _ m fo lo lp))
  (let ((erased rl) (erased rh)) (split-len k m p ql qh w lp))
  (match erased (split-cover k os p ql qh fo (obs-ok e f ks y a os ab ob) w) _
    ((OrL _ _ q) (OrL _ _ (MkExactAt e f ks y a os ql pa ob (MkExact os ql m q lo rl))))
    ((OrR _ _ q) (OrR _ _ (MkExactAt e f ks y a os qh pa ob (MkExact os qh m q lo rh))))))
