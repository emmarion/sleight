; Certified rule counting and the dbound checks of discharge.v and hubcap.v, over the sector lists of fit.sl. In place
; of calling redp, a check returns the parts it would have handed to redp (its obligations); its evidence then gives
; either the bound or an obligation that fits the hub exactly.

(def-adts $ (IfT : ((Bool) b) (Type P) -> Type)
  enum
  (many IfY : (erased Type P) (erased P p) -> (IfT (BTrue) P))
  (many IfF : (erased Type P) -> (IfT (BFalse) P)))

(def-adts $ (LtT : ((Nat) a b) -> Type)
  enum
  (many LtYes : (erased (Nat) a b) (erased (Lt a b) p) -> (LtT a b))
  (many LtNo : (erased (Nat) a b) -> (LtT a b)))

(def-fns _ $ (many lt-test : (many (Nat) a b) -> (many (LtT a b) t))
  (match many (nat-cmp a b) _ ((CLt _ _ _ _ p) (LtYes a b p)) (else (LtNo a b))))

(def-fns _ $ (erased add-shift : (erased (Nat) a b c) (subterm erased (Add a (Succ b) c) p) -> (erased (Add (Succ a) b c) q))
  (let-match erased p (AddSucc a1 _ c1 p1) ((AddZero _) (AddSucc (Zero) b b (AddZero b))))
  (AddSucc (Succ a1) b c1 (add-shift a1 b c1 p1)))

(def-fns _ $ (erased plus-assoc : (erased (Nat) a b c ab abc) (subterm erased (Add a b ab) p) (erased (Add ab c abc) q) ->
    (erased (Nat) bc) (erased (Add b c bc) r) (erased (Add a bc abc) s))
  (let-match erased p (AddSucc a1 _ ab1 p1) ((AddZero _) (values abc q (AddZero abc))))
  (let-match erased q (AddSucc _ _ abc1 q1))
  (let ((erased bc) (erased r) (erased s)) (plus-assoc a1 b c ab1 abc1 p1 q1))
  (values bc r (AddSucc a1 bc abc1 s)))

(def-fns _ $ (erased plus-assoc-r : (erased (Nat) a b c bc abc) (subterm erased (Add a bc abc) p) (erased (Add b c bc) q) ->
    (erased (Nat) ab) (erased (Add a b ab) r) (erased (Add ab c abc) s))
  (let-match erased p (AddSucc a1 _ abc1 p1) ((AddZero _) (values b (AddZero b) q)))
  (let ((erased ab) (erased r) (erased s)) (plus-assoc-r a1 b c bc abc1 p1 q))
  (values (Succ ab) (AddSucc a1 b ab r) (AddSucc ab c abc1 s)))

(def-fns _ $ (erased plus-lcomm : (erased (Nat) a b c x y) (erased (Add b c x) p) (erased (Add a x y) q) ->
    (erased (Nat) z) (erased (Add a c z) r) (erased (Add b z y) s))
  (let ((erased ab) (erased r1) (erased s1)) (plus-assoc-r a b c x y q p))
  (plus-assoc b a c ab y (add-comm a b ab r1) s1))

(def-fns _ $ (erased add-lt-r : (erased (Nat) a b c d e) (subterm erased (Add a b c) p) (erased (Add a d e) q) (erased (Lt b d) l) -> (erased (Lt c e) r))
  (let-match erased p (AddSucc a1 _ c1 p1) ((AddZero _) (let-match erased q (AddZero _)) l))
  (let-match erased q (AddSucc _ _ e1 q1))
  (LtS c1 e1 (add-lt-r a1 b c1 d e1 p1 q1 l)))

(def-fns _ $ (erased add-le-r : (erased (Nat) a b c d e) (subterm erased (Add a b c) p) (erased (Add a d e) q) (erased (Lt b (Succ d)) l)
    -> (erased (Lt c (Succ e)) r))
  (add-lt-r a b c (Succ d) (Succ e) p (add-succ-right a d e q) l))

(def-fns _ $ (erased le-sum : (erased (Nat) a b c d x y) (erased (Lt a (Succ b)) l) (erased (Lt c (Succ d)) k) (erased (Add a c x) p)
    (erased (Add b d y) q) -> (erased (Lt x (Succ y)) r))
  (let ((erased z) (erased pz)) (add a d))
  (le-trans x z y (add-le-r a c x d z p pz k) (add-le-r d a z b y (add-comm a d z pz) (add-comm b d y q) l)))

(def-fns _ $ (erased add-eq : (erased (Nat) a b c d) (erased (Add a b c) p) (erased (Add a b d) q) -> (erased (Eq (Nat) c d) e))
  (add-fn a b c d p q))

; Deciding a fit.
(def-fns _ $ (erased rg-dec : (erased (Nat) a) (erased (Rg) r) -> (erased (Or (InRg a r) (OutRg a r)) o))
  (let-match erased r (MkRg lo hi))
  (let ((erased m) (erased c)) (clamp-exists a))
  (let-match erased (le-dec lo m) (LeY _ _ p) ((LeN _ _ p) (OrR _ _ (OutLo a m lo hi c p))))
  (match erased (le-dec m hi) _
    ((LeY _ _ q) (OrL _ _ (MkInRg a m lo hi c p q)))
    ((LeN _ _ q) (OrR _ _ (OutHi a m lo hi c q)))))

(def-fns _ $ (erased fans-dec : (erased (List (Nat)) as) (subterm erased (List (Rg)) fs)
    -> (erased (Or (Pw (Nat) (Rg) InRg as fs) (Bad (Nat) (Rg) OutRg as fs)) o))
  (let-match erased fs (Cons _ r fs1) ((Nil _) (OrL _ _ (PwNil _ _ InRg as))))
  (let-match erased as (Cons _ a as1) ((Nil _) (OrR _ _ (BadShort _ _ OutRg r fs1))))
  (let-match erased (rg-dec a r) (OrL _ _ i) ((OrR _ _ o) (OrR _ _ (BadHere _ _ OutRg a r as1 fs1 o))))
  (match erased (fans-dec as1 fs1) _
    ((OrL _ _ f) (OrL _ _ (PwCons _ _ InRg a r as1 fs1 i f)))
    ((OrR _ _ b) (OrR _ _ (BadThere _ _ OutRg a r as1 fs1 b)))))

(def-fns _ $ (erased sec-dec : (erased (Sec) o) (erased (Sub) x) -> (erased (Or (FitSec o x) (OutSec o x)) r))
  (let-match erased o (MkSec a h as))
  (let-match erased x (MkSub s hr fs))
  (let-match erased (rg-dec a s) (OrL _ _ i1) ((OrR _ _ q) (OrR _ _ (OSSpoke a h as s hr fs q))))
  (let-match erased (rg-dec h hr) (OrL _ _ i2) ((OrR _ _ q) (OrR _ _ (OSHat a h as s hr fs q))))
  (match erased (fans-dec as fs) _
    ((OrL _ _ f) (OrL _ _ (MkFitSec a h as s hr fs i1 i2 f)))
    ((OrR _ _ b) (OrR _ _ (OSFan a h as s hr fs b)))))

(def-fns _ $ (erased fit-dec : (erased (List (Sec)) os) (subterm erased (List (Sub)) p)
    -> (erased (Or (Pw (Sec) (Sub) FitSec os p) (Bad (Sec) (Sub) OutSec os p)) r))
  (let-match erased p (Cons _ x p1) ((Nil _) (OrL _ _ (PwNil _ _ FitSec os))))
  (let-match erased os (Cons _ o os1) ((Nil _) (OrR _ _ (BadShort _ _ OutSec x p1))))
  (let-match erased (sec-dec o x) (OrL _ _ i) ((OrR _ _ q) (OrR _ _ (BadHere _ _ OutSec o x os1 p1 q))))
  (match erased (fit-dec os1 p1) _
    ((OrL _ _ f) (OrL _ _ (PwCons _ _ FitSec o x os1 p1 i f)))
    ((OrR _ _ b) (OrR _ _ (BadThere _ _ OutSec o x os1 p1 b)))))

; c of the parts rs fit the sector list os.
(def-adts $ (Count : ((List (Sec)) os) ((List (List (Sub))) rs) ((Nat) c) -> Type)
  enum
  (many CNil : (erased (List (Sec)) os) -> (Count os (Nil (List (Sub))) (Zero)))
  (many CYes : (erased (List (Sec)) os) (erased (List (Sub)) r) (erased (List (List (Sub))) rs) (erased (Nat) c)
      (erased (Pw (Sec) (Sub) FitSec os r) f) (erased (Count os rs c) rest) -> (Count os (Cons (List (Sub)) r rs) (Succ c)))
  (many CNo : (erased (List (Sec)) os) (erased (List (Sub)) r) (erased (List (List (Sub))) rs) (erased (Nat) c)
      (erased (Bad (Sec) (Sub) OutSec os r) f) (erased (Count os rs c) rest) -> (Count os (Cons (List (Sub)) r rs) c)))

(def-fns _ $ (erased count-exists : (erased (List (Sec)) os) (subterm erased (List (List (Sub))) rs) -> (erased (Nat) c) (erased (Count os rs c) k))
  (let-match erased rs (Cons _ r rs1) ((Nil _) (values (Zero) (CNil os))))
  (let ((erased c) (erased k)) (count-exists os rs1))
  (match erased (fit-dec os r) _
    ((OrL _ _ f) (values (Succ c) (CYes os r rs1 c f k)))
    ((OrR _ _ b) (values c (CNo os r rs1 c b k)))))

(def-fns _ $ (erased count-le : (erased (List (Sec)) os) (erased (List (List (Sub))) rs) (erased (Nat) c l) (subterm erased (Count os rs c) k)
    (erased (Length (List (Sub)) rs l) pl) -> (erased (Lt c (Succ l)) r))
  (let-match erased pl (LengthCons _ _ rs1 l1 pl1) ((LengthNil _) (let-match erased k (CNil _)) (LtZ (Zero))))
  (match erased k _
    ((CYes _ _ _ c1 _ k1) (LtS c1 (Succ l1) (count-le os rs1 c1 l1 k1 pl1)))
    ((CNo _ _ _ _ _ k1) (lt-weaken c (Succ l1) (count-le os rs1 c l1 k1 pl1)))))

; sort_drules from the accumulators n and acc: m is n plus the rules of rs that p implies, and out is acc with the
; rules of rs that straddle p consed on in order.
(def-adts $ (Sr : ((List (Sub)) p) ((Nat) n) ((List (List (Sub))) acc rs) ((Nat) m) ((List (List (Sub))) out) -> Type)
  enum
  (many SrNil : (erased (List (Sub)) p) (erased (Nat) n) (erased (List (List (Sub))) acc) -> (Sr p n acc (Nil (List (Sub))) n acc))
  (many SrSub : (erased (List (Sub)) p r) (erased (Nat) n m) (erased (List (List (Sub))) acc rs out) (erased (Pw (Sub) (Sub) SubSub p r) s)
      (erased (Sr p (Succ n) acc rs m out) rest) -> (Sr p n acc (Cons (List (Sub)) r rs) m out))
  (many SrStr : (erased (List (Sub)) p r) (erased (Nat) n m) (erased (List (List (Sub))) acc rs out)
      (erased (Sr p n (Cons (List (Sub)) r acc) rs m out) rest) -> (Sr p n acc (Cons (List (Sub)) r rs) m out))
  (many SrDis : (erased (List (Sub)) p r) (erased (Nat) n m) (erased (List (List (Sub))) acc rs out) (erased (Ex (Sub) (Sub) SubDis p r) d)
      (erased (Sr p n acc rs m out) rest) -> (Sr p n acc (Cons (List (Sub)) r rs) m out)))

(def-fns _ $ (many sort-rec : (many (List (Sub)) p) (many (Nat) n) (many (List (List (Sub))) acc) (subterm many (List (List (Sub))) rs)
    -> (many (Nat) m) (many (List (List (Sub))) out) (erased (Sr p n acc rs m out) w))
  (let-match many rs (Cons _ r rest) ((Nil _) (values n acc (SrNil p n acc))))
  (let ((many k) (erased a)) (part-cmp p r))
  (match many k _
    ((PSub)
      (let-match erased a (AnsSub _ _ s))
      (let ((many m) (many out) (erased w)) (tail $ sort-rec p (Succ n) acc rest))
      (values m out (SrSub p r n m acc rest out s w)))
    ((PStr)
      (let ((many m) (many out) (erased w)) (tail $ sort-rec p n (Cons _ r acc) rest))
      (values m out (SrStr p r n m acc rest out w)))
    ((PDis)
      (let-match erased a (AnsDis _ _ d))
      (let ((many m) (many out) (erased w)) (tail $ sort-rec p n acc rest))
      (values m out (SrDis p r n m acc rest out d w)))))

(def-fns _ $ (many sort-drules-c : (many (List (Sub)) p) (many (List (List (Sub))) rs)
    -> (many (Nat) m) (many (List (List (Sub))) out) (erased (Sr p (Zero) (Nil (List (Sub))) rs m out) w))
  (sort-rec p (Zero) (Nil _) rs))

(def-fns _ $ (erased sr-count : (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (Nat) n m ca c s1 s)
    (erased (List (List (Sub))) acc rs out) (erased (Pw (Sec) (Sub) FitSec os p) f) (subterm erased (Sr p n acc rs m out) w)
    (erased (Count os acc ca) ka) (erased (Count os rs c) kr) (erased (Add n ca s1) e1) (erased (Add s1 c s) e2)
    -> (erased (Nat) co) (erased (Count os out co) ko) (erased (Add m co s) e))
  (match erased w _
    ((SrNil _ _ _)
      (let-match erased kr (CNil _))
      (let-match erased (add-eq s1 (Zero) s s1 e2 (add-zero-right s1)) (Refl _ _))
      (values ca ka e1))
    ((SrSub _ r _ _ _ rs1 _ sb w1)
      (let-match erased kr (CYes _ _ _ c1 _ kr1) (absurd (CNo _ _ _ _ b _) (fit-bad os r (fit-sub os p r f sb) b)))
      (sr-count os p (Succ n) m ca c1 (Succ s1) s acc rs1 out f w1 ka kr1 (AddSucc n ca s1 e1) (add-shift s1 c1 s e2)))
    ((SrStr _ r _ _ _ rs1 _ w1)
      (match erased kr _
        ((CYes _ _ _ c1 fr kr1)
          (sr-count os p n m (Succ ca) c1 (Succ s1) s (Cons _ r acc) rs1 out f w1 (CYes os r acc ca fr ka) kr1
            (add-succ-right n ca s1 e1) (add-shift s1 c1 s e2)))
        ((CNo _ _ _ _ b kr1) (sr-count os p n m ca c s1 s (Cons _ r acc) rs1 out f w1 (CNo os r acc ca b ka) kr1 e1 e2))))
    ((SrDis _ r _ _ _ rs1 _ d w1)
      (let-match erased kr (CNo _ _ _ _ _ kr1) (absurd (CYes _ _ _ _ fr _) (fit-bad os r fr (fit-dis os p r f d))))
      (sr-count os p n m ca c s1 s acc rs1 out f w1 ka kr1 e1 e2))))

; Some rule of ru is implied by p.
(def-adts $ (Implied : ((List (Sub)) p) ((List (List (Sub))) ru) -> Type)
  enum
  (many ImHere : (erased (List (Sub)) p r) (erased (List (List (Sub))) ru) (erased (Pw (Sub) (Sub) SubSub p r) s) -> (Implied p (Cons (List (Sub)) r ru)))
  (many ImThere : (erased (List (Sub)) p r) (erased (List (List (Sub))) ru) (erased (Implied p ru) rest) -> (Implied p (Cons (List (Sub)) r ru))))

(def-fns _ $ (many check-unfit-c : (many (List (Sub)) p) (subterm many (List (List (Sub))) ru) -> (many (Bool) b) (erased (IfT b (Implied p ru)) w))
  (let-match many ru (Cons _ r rest) ((Nil _) (values (BFalse) (IfF _))))
  (let ((many k) (erased a)) (part-cmp p r))
  (let-match many k (PSub) (else
    (let ((many b) (erased w)) (tail $ check-unfit-c p rest))
    (values b (match erased w _ ((IfY _ i) (IfY _ (ImThere p r rest i))) ((IfF _) (IfF _))))))
  (let-match erased a (AnsSub _ _ s))
  (values (BTrue) (IfY _ (ImHere p r rest s))))

(def-fns _ $ (erased absurd unfit-sound : (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (List (List (Sub))) ru)
    (subterm erased (Implied p ru) i) (erased (Pw (Sec) (Sub) FitSec os p) f) (erased (Count os ru (Zero)) k) -> (erased (False) r))
  (match erased i _
    (absurd (ImHere _ r _ s) (let-match erased k (CNo _ _ _ _ b _)) (fit-bad os r (fit-sub os p r f s) b))
    (absurd (ImThere _ _ ru1 i1) (let-match erased k (CNo _ _ _ _ _ k1)) (unfit-sound os p ru1 i1 f k1))))

; An exact fit, and an obligation that fits exactly.
(def-adts $ (Exact : ((List (Sec)) os) ((List (Sub)) p) -> Type)
  enum
  (many MkExact : (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (Nat) n) (erased (Pw (Sec) (Sub) FitSec os p) f)
      (erased (Length (Sec) os n) lo) (erased (Length (Sub) p n) lp) -> (Exact os p)))

(def-adts $ (Hit : ((List (Sec)) os) ((List (List (Sub))) obl) -> Type)
  enum
  (many HitHere : (erased (List (Sec)) os) (erased (List (Sub)) q) (erased (List (List (Sub))) obl) (erased (Exact os q) x)
      -> (Hit os (Cons (List (Sub)) q obl)))
  (many HitThere : (erased (List (Sec)) os) (erased (List (Sub)) q) (erased (List (List (Sub))) obl) (erased (Hit os obl) h)
      -> (Hit os (Cons (List (Sub)) q obl))))

(def-adts $ (Ext : ((List (List (Sub))) acc out) -> Type)
  enum
  (many ExtRefl : (erased (List (List (Sub))) acc) -> (Ext acc acc))
  (many ExtCons : (erased (List (List (Sub))) acc out) (erased (List (Sub)) q) (erased (Ext acc out) e) -> (Ext acc (Cons (List (Sub)) q out))))

(def-fns _ $ (erased hit-ext : (erased (List (Sec)) os) (erased (List (List (Sub))) acc out) (erased (Hit os acc) h) (subterm erased (Ext acc out) e)
    -> (erased (Hit os out) r))
  (let-match erased e (ExtCons _ out1 q e1) ((ExtRefl _) h))
  (HitThere os q out1 (hit-ext os acc out1 h e1)))

(def-fns _ $ (erased ext-trans : (erased (List (List (Sub))) a b c) (erased (Ext a b) e) (subterm erased (Ext b c) e2) -> (erased (Ext a c) r))
  (let-match erased e2 (ExtCons _ c1 q e3) ((ExtRefl _) e))
  (ExtCons a c1 q (ext-trans a b c1 e e3)))

(def-fns _ $ (erased meet-len : (erased (List (Sub)) p q m) (erased (Nat) n) (subterm erased (PartMeet p q m) w) (erased (Length (Sub) p n) l)
    -> (erased (Length (Sub) m n) r))
  (let-match erased w (PMCons _ _ z p1 q1 m1 _ w1) ((PMKeep _ _) l))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (LengthCons _ z m1 n1 (meet-len p1 q1 m1 n1 w1 l1)))

(def-fns _ $ (erased exact-meet : (erased (List (Sec)) os) (erased (List (Sub)) p r m) (erased (Exact os p) x)
    (erased (Pw (Sec) (Sub) FitSec os r) fr) (erased (PartMeet p r m) w) -> (erased (Exact os m) y))
  (let-match erased x (MkExact _ _ n f lo lp))
  (MkExact os m n (fit-meet os p r m f fr w) lo (meet-len p r m n w lp)))

; A successful check_dbound1_rec from obligations acc to out.
(def-adts
  ((Db1 : ((List (Sub)) p) ((List (List (Sub))) rs) ((Nat) ns) ((List (List (Sub))) acc out) -> Type)
    enum
    (many D1Nil : (erased (List (Sub)) p) (erased (Nat) ns) (erased (List (List (Sub))) acc) -> (Db1 p (Nil (List (Sub))) ns acc acc))
    (many D1Small : (erased (List (Sub)) p r) (erased (List (List (Sub))) rs) (erased (Nat) ns l) (erased (List (List (Sub))) acc)
        (erased (Length (List (Sub)) rs l) pl) (erased (Lt l ns) lt) -> (Db1 p (Cons (List (Sub)) r rs) ns acc acc))
    (many D1Step : (erased (List (Sub)) p p1 r) (erased (List (List (Sub))) rs rs2) (erased (Nat) ns dns) (erased (List (List (Sub))) acc acc1 out)
        (erased (PartMeet p r p1) wm) (erased (Sr p1 (Zero) (Nil (List (Sub))) rs dns rs2) ws) (erased (Db1In p1 rs2 ns dns acc acc1) di)
        (erased (Db1 p rs ns acc1 out) dt) -> (Db1 p (Cons (List (Sub)) r rs) ns acc out)))
  ((Db1In : ((List (Sub)) p1) ((List (List (Sub))) rs2) ((Nat) ns dns) ((List (List (Sub))) acc acc1) -> Type)
    enum
    (many I1Rec : (erased (List (Sub)) p1) (erased (List (List (Sub))) rs2) (erased (Nat) ns dns ns1) (erased (List (List (Sub))) acc acc1)
        (erased (Monus ns dns (Succ ns1)) mo) (erased (Db1 p1 rs2 ns1 acc acc1) d) -> (Db1In p1 rs2 ns dns acc acc1))
    (many I1Red : (erased (List (Sub)) p1) (erased (List (List (Sub))) rs2) (erased (Nat) ns dns) (erased (List (List (Sub))) acc)
        (erased (Monus ns dns (Zero)) mo) -> (Db1In p1 rs2 ns dns acc (Cons (List (Sub)) p1 acc)))))

(def-fns _ $ (many cdb1-c : (many (List (Sub)) p) (many (List (List (Sub))) rs) (many (Nat) ns) (many (List (List (Sub))) acc) (subterm many (Nat) m)
    -> (many (Bool) ok) (many (List (List (Sub))) out) (erased (IfT ok (Db1 p rs ns acc out)) w))
  (let-match many m (Succ m1) ((Zero) (values (BFalse) acc (IfF _))))
  (let-match many rs (Cons _ r rs1) ((Nil _) (values (BTrue) acc (IfY _ (D1Nil p ns acc)))))
  (let ((many l) (erased pl)) (list-count _ rs1))
  (let-match many (lt-test l ns) (LtNo _ _) ((LtYes _ _ lt) (values (BTrue) acc (IfY _ (D1Small p r rs1 ns l acc pl lt)))))
  (let ((many p1) (erased wm)) (part-meet p r))
  (let ((many dns) (many rs2) (erased ws)) (sort-drules-c p1 rs1))
  (let ((many k) (erased mo)) (monus-c ns dns))
  (let ((many ok1) (many acc1) (erased w1))
    (match many k (((Bool) ok1) ((List (List (Sub))) acc1) ((IfT ok1 (Db1In p1 rs2 ns dns acc acc1)) w1))
      ((Succ ns1)
        (let ((many ok2) (many acc2) (erased w2)) (notail $ cdb1-c p1 rs2 ns1 acc m1))
        (values ok2 acc2 (match erased w2 _ ((IfY _ d) (IfY _ (I1Rec p1 rs2 ns dns ns1 acc acc2 mo d))) ((IfF _) (IfF _)))))
      ((Zero) (values (BTrue) (Cons _ p1 acc) (IfY _ (I1Red p1 rs2 ns dns acc mo))))))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) acc1 (IfF _))))
  (let-match erased w1 (IfY _ di))
  (let ((many ok) (many out) (erased w)) (tail $ cdb1-c p rs1 ns acc1 m1))
  (values ok out (match erased w _ ((IfY _ dt) (IfY _ (D1Step p p1 r rs1 rs2 ns dns acc acc1 out wm ws di dt))) ((IfF _) (IfF _)))))

(def-fns _ $ (erased db1-ext : (erased (List (Sub)) p) (erased (List (List (Sub))) rs) (erased (Nat) ns) (erased (List (List (Sub))) acc out)
    (subterm erased (Db1 p rs ns acc out) d) -> (erased (Ext acc out) e))
  (let-match erased d (D1Step _ p1 _ rs1 rs2 _ dns _ acc1 _ _ _ di dt) ((D1Nil _ _ _) (ExtRefl acc)) ((D1Small _ _ _ _ _ _ _ _) (ExtRefl acc)))
  (let ((erased (Ext acc acc1) e1))
    (match erased di _
      ((I1Rec _ _ _ _ ns1 _ _ _ d1) (db1-ext p1 rs2 ns1 acc acc1 d1))
      ((I1Red _ _ _ _ _ _) (ExtCons acc acc p1 (ExtRefl acc)))))
  (ext-trans acc acc1 out e1 (db1-ext p rs1 ns acc1 out dt)))

(def-fns _ $ (erased db1-sound : (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (List (List (Sub))) rs) (erased (Nat) ns c)
    (erased (List (List (Sub))) acc out) (erased (Exact os p) x) (subterm erased (Db1 p rs ns acc out) d) (erased (Count os rs c) k)
    -> (erased (Or (Lt c (Succ ns)) (Hit os out)) r))
  (let-match erased d (D1Step _ p1 r rs1 rs2 _ dns _ acc1 _ wm ws di dt)
    ((D1Nil _ _ _) (let-match erased k (CNil _)) (OrL _ _ (LtZ ns)))
    ((D1Small _ r rs1 _ l _ pl lt)
      (OrL _ _ (le-trans c (Succ l) ns (count-le os rs c (Succ l) k (LengthCons _ r rs1 l pl)) (LtS l ns lt)))))
  (let-match erased k (CYes _ _ _ c1 fr k1) ((CNo _ _ _ _ _ k1) (db1-sound os p rs1 ns c acc1 out x dt k1)))
  (let ((erased x1)) (exact-meet os p r p1 x fr wm))
  (let-match erased x1 (MkExact _ _ _ f1 _ _))
  (let ((erased c2) (erased k2) (erased e))
    (sr-count os p1 (Zero) dns (Zero) c1 (Zero) c1 (Nil _) rs1 rs2 f1 ws (CNil os) k1 (AddZero (Zero)) (AddZero c1)))
  (let ((erased et)) (db1-ext p rs1 ns acc1 out dt))
  (let-match erased di (I1Rec _ _ _ _ ns1 _ _ mo d1) ((I1Red _ _ _ _ _ _) (OrR _ _ (hit-ext os acc1 out (HitHere os p1 acc x1) et))))
  (let-match erased mo (MoAdd _ _ _ ad))
  (match erased (db1-sound os p1 rs2 ns1 c2 acc acc1 x1 d1 k2) _
    ((OrL _ _ le) (OrL _ _ (LtS c1 ns (add-lt-r dns c2 c1 (Succ ns1) ns e ad le))))
    ((OrR _ _ h) (OrR _ _ (hit-ext os acc1 out h et)))))

(def-fns _ $ (many check-dbound1-c : (many (List (Sub)) p) (many (List (List (Sub))) rs) (many (Nat) ns) (many (List (List (Sub))) acc)
    -> (many (Bool) ok) (many (List (List (Sub))) out) (erased (IfT ok (Db1 p rs ns acc out)) w))
  (let ((many l) (erased _)) (list-count _ rs))
  (cdb1-c p rs ns acc (Succ l)))

; A successful check_dbound2_rec from obligations acc to out.
(def-adts
  ((Db2 : ((List (Sub)) p) ((List (List (Sub))) rt rs ru) ((Nat) nt) ((List (List (Sub))) acc out) -> Type)
    enum
    (many D2Nil : (erased (List (Sub)) p) (erased (List (List (Sub))) rs ru) (erased (Nat) nt) (erased (List (List (Sub))) acc)
        -> (Db2 p (Nil (List (Sub))) rs ru nt acc acc))
    (many D2Small : (erased (List (Sub)) p r) (erased (List (List (Sub))) rt rs ru) (erased (Nat) nt l) (erased (List (List (Sub))) acc)
        (erased (Length (List (Sub)) rt l) pl) (erased (Lt l nt) lt) -> (Db2 p (Cons (List (Sub)) r rt) rs ru nt acc acc))
    (many D2Step : (erased (List (Sub)) p p1 r) (erased (List (List (Sub))) rt rs ru) (erased (Nat) nt) (erased (List (List (Sub))) acc acc1 out)
        (erased (PartMeet p r p1) wm) (erased (Db2In p1 rt rs ru nt acc acc1) di) (erased (Db2 p rt rs (Cons (List (Sub)) r ru) nt acc1 out) dt)
        -> (Db2 p (Cons (List (Sub)) r rt) rs ru nt acc out)))
  ((Db2In : ((List (Sub)) p1) ((List (List (Sub))) rt rs ru) ((Nat) nt) ((List (List (Sub))) acc acc1) -> Type)
    enum
    (many I2Unfit : (erased (List (Sub)) p1) (erased (List (List (Sub))) rt rs ru) (erased (Nat) nt) (erased (List (List (Sub))) acc)
        (erased (Implied p1 ru) im) -> (Db2In p1 rt rs ru nt acc acc))
    (many I2Rec : (erased (List (Sub)) p1) (erased (List (List (Sub))) rt rs ru rt2 rs2) (erased (Nat) nt dnt dns u nt1)
        (erased (List (List (Sub))) acc acc1) (erased (Sr p1 (Zero) (Nil (List (Sub))) rt dnt rt2) wt) (erased (Sr p1 (Zero) (Nil (List (Sub))) rs dns rs2) ws)
        (erased (Add dns nt u) au) (erased (Monus u dnt (Succ nt1)) mo) (erased (Db2 p1 rt2 rs2 ru nt1 acc acc1) d) -> (Db2In p1 rt rs ru nt acc acc1))
    (many I2Red : (erased (List (Sub)) p1) (erased (List (List (Sub))) rt rs ru rt2 rs2) (erased (Nat) nt dnt dns u) (erased (List (List (Sub))) acc)
        (erased (Sr p1 (Zero) (Nil (List (Sub))) rt dnt rt2) wt) (erased (Sr p1 (Zero) (Nil (List (Sub))) rs dns rs2) ws)
        (erased (Add dns nt u) au) (erased (Monus u dnt (Zero)) mo) -> (Db2In p1 rt rs ru nt acc (Cons (List (Sub)) p1 acc)))))

(def-fns _ $ (many cdb2-c : (many (List (Sub)) p) (many (List (List (Sub))) rt rs ru) (many (Nat) nt) (many (List (List (Sub))) acc) (subterm many (Nat) m)
    -> (many (Bool) ok) (many (List (List (Sub))) out) (erased (IfT ok (Db2 p rt rs ru nt acc out)) w))
  (let-match many m (Succ m1) ((Zero) (values (BFalse) acc (IfF _))))
  (let-match many rt (Cons _ r rt1) ((Nil _) (values (BTrue) acc (IfY _ (D2Nil p rs ru nt acc)))))
  (let ((many l) (erased pl)) (list-count _ rt1))
  (let-match many (lt-test l nt) (LtNo _ _) ((LtYes _ _ lt) (values (BTrue) acc (IfY _ (D2Small p r rt1 rs ru nt l acc pl lt)))))
  (let ((many p1) (erased wm)) (part-meet p r))
  (let ((many ok1) (many acc1) (erased w1))
    (let ((many uf) (erased wu)) (check-unfit-c p1 ru))
    (match many uf (((Bool) ok1) ((List (List (Sub))) acc1) ((IfT ok1 (Db2In p1 rt1 rs ru nt acc acc1)) w1))
      ((BTrue) (let-match erased wu (IfY _ im)) (values (BTrue) acc (IfY _ (I2Unfit p1 rt1 rs ru nt acc im))))
      ((BFalse)
        (let ((many dnt) (many rt2) (erased wt)) (sort-drules-c p1 rt1))
        (let ((many dns) (many rs2) (erased ws)) (sort-drules-c p1 rs))
        (let ((many u) (erased au)) (add dns nt))
        (let ((many k) (erased mo)) (monus-c u dnt))
        (let-match many k (Succ nt1) ((Zero) (values (BTrue) (Cons _ p1 acc) (IfY _ (I2Red p1 rt1 rs ru rt2 rs2 nt dnt dns u acc wt ws au mo)))))
        (let ((many ok2) (many acc2) (erased w2)) (notail $ cdb2-c p1 rt2 rs2 ru nt1 acc m1))
        (values ok2 acc2 (match erased w2 _
          ((IfY _ d) (IfY _ (I2Rec p1 rt1 rs ru rt2 rs2 nt dnt dns u nt1 acc acc2 wt ws au mo d)))
          ((IfF _) (IfF _)))))))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) acc1 (IfF _))))
  (let-match erased w1 (IfY _ di))
  (let ((many ok) (many out) (erased w)) (tail $ cdb2-c p rt1 rs (Cons _ r ru) nt acc1 m1))
  (values ok out (match erased w _ ((IfY _ dt) (IfY _ (D2Step p p1 r rt1 rs ru nt acc acc1 out wm di dt))) ((IfF _) (IfF _)))))

(def-fns _ $ (erased db2-ext : (erased (List (Sub)) p) (erased (List (List (Sub))) rt rs ru) (erased (Nat) nt) (erased (List (List (Sub))) acc out)
    (subterm erased (Db2 p rt rs ru nt acc out) d) -> (erased (Ext acc out) e))
  (let-match erased d (D2Step _ p1 r rt1 _ _ _ _ acc1 _ _ di dt) ((D2Nil _ _ _ _ _) (ExtRefl acc)) ((D2Small _ _ _ _ _ _ _ _ _ _) (ExtRefl acc)))
  (let ((erased (Ext acc acc1) e1))
    (match erased di _
      ((I2Unfit _ _ _ _ _ _ _) (ExtRefl acc))
      ((I2Rec _ _ _ _ rt2 rs2 _ _ _ _ nt1 _ _ _ _ _ _ d1) (db2-ext p1 rt2 rs2 ru nt1 acc acc1 d1))
      ((I2Red _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (ExtCons acc acc p1 (ExtRefl acc)))))
  (ext-trans acc acc1 out e1 (db2-ext p rt1 rs (Cons _ r ru) nt acc1 out dt)))

; The arithmetic of a refined step: 1 + (dnt + c2) <= (dns + s2) + nt when dns + nt = dnt + (1 + nt1) and c2 <= s2 + nt1.
(def-fns _ $ (erased step-bound : (erased (Nat) dnt c2 c1 dns s2 cs nt u nt1 v w) (erased (Add dnt c2 c1) pa) (erased (Add dns s2 cs) pb)
    (erased (Add dns nt u) pcc) (erased (Add dnt (Succ nt1) u) pd) (erased (Add s2 nt1 v) pv) (erased (Lt c2 (Succ v)) le) (erased (Add cs nt w) pw)
    -> (erased (Lt (Succ c1) (Succ w)) r))
  (let ((erased y) (erased py)) (add dnt v))
  (let ((erased le1)) (add-le-r dnt c2 c1 v y pa py le))
  (let ((erased z) (erased pz) (erased pz2)) (plus-lcomm dnt s2 (Succ nt1) (Succ v) (Succ y) (add-succ-right s2 nt1 v pv) (add-succ-right dnt v y py)))
  (let-match erased (add-eq dnt (Succ nt1) z u pz pd) (Refl _ _))
  (let ((erased t) (erased pt) (erased pt2)) (plus-assoc dns s2 nt cs w pb pw))
  (let ((erased t2) (erased pq) (erased pq2)) (plus-lcomm s2 dns nt u (Succ y) pcc pz2))
  (let-match erased (add-eq s2 nt t2 t pq pt) (Refl _ _))
  (let-match erased (add-eq dns t (Succ y) w pq2 pt2) (Refl _ _))
  (LtS c1 w le1))

(def-fns _ $ (erased db2-sound : (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (List (List (Sub))) rt rs ru acc out) (erased (Nat) nt ct cs w)
    (erased (Exact os p) x) (subterm erased (Db2 p rt rs ru nt acc out) d) (erased (Count os rt ct) kt) (erased (Count os rs cs) ks)
    (erased (Count os ru (Zero)) ku) (erased (Add cs nt w) aw) -> (erased (Or (Lt ct (Succ w)) (Hit os out)) r))
  (let-match erased d (D2Step _ p1 r rt1 _ _ _ _ acc1 _ wm di dt)
    ((D2Nil _ _ _ _ _) (let-match erased kt (CNil _)) (OrL _ _ (LtZ w)))
    ((D2Small _ r rt1 _ _ _ l _ pl lt)
      (OrL _ _ (le-trans ct nt w (le-trans ct (Succ l) nt (count-le os rt ct (Succ l) kt (LengthCons _ r rt1 l pl)) (LtS l nt lt))
        (add-le-right cs nt w aw)))))
  (let-match erased kt (CYes _ _ _ c1 fr kt1)
    ((CNo _ _ _ _ b kt1) (db2-sound os p rt1 rs (Cons _ r ru) acc1 out nt ct cs w x dt kt1 ks (CNo os r ru (Zero) b ku) aw)))
  (let ((erased x1)) (exact-meet os p r p1 x fr wm))
  (let-match erased x1 (MkExact _ _ _ f1 _ _))
  (let ((erased et)) (db2-ext p rt1 rs (Cons _ r ru) nt acc1 out dt))
  (let-match erased di (I2Rec _ _ _ _ rt2 rs2 _ dnt dns u nt1 _ _ wt ws au mo d1)
    (absurd (I2Unfit _ _ _ _ _ _ im) (unfit-sound os p1 ru im f1 ku))
    ((I2Red _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (OrR _ _ (hit-ext os acc1 out (HitHere os p1 acc x1) et))))
  (let-match erased mo (MoAdd _ _ _ ad))
  (let ((erased c2) (erased kt2) (erased e1))
    (sr-count os p1 (Zero) dnt (Zero) c1 (Zero) c1 (Nil _) rt1 rt2 f1 wt (CNil os) kt1 (AddZero (Zero)) (AddZero c1)))
  (let ((erased s2) (erased ks2) (erased e2))
    (sr-count os p1 (Zero) dns (Zero) cs (Zero) cs (Nil _) rs rs2 f1 ws (CNil os) ks (AddZero (Zero)) (AddZero cs)))
  (let ((erased v) (erased av)) (add s2 nt1))
  (match erased (db2-sound os p1 rt2 rs2 ru acc acc1 nt1 c2 s2 v x1 d1 kt2 ks2 ku av) _
    ((OrL _ _ le) (OrL _ _ (step-bound dnt c2 c1 dns s2 cs nt u nt1 v w e1 e2 au ad av le aw)))
    ((OrR _ _ h) (OrR _ _ (hit-ext os acc1 out h et)))))

(def-adts $ (Db2Top : ((List (Sub)) p) ((List (List (Sub))) rt rs) ((Z) b) ((List (List (Sub))) acc out) -> Type)
  enum
  (many MkDb2Top : (erased (List (Sub)) p) (erased (List (List (Sub))) rt rs rt1 rs1 acc out) (erased (Nat) dnt dns bp bn x y nt)
      (erased (Sr p (Zero) (Nil (List (Sub))) rt dnt rt1) wt) (erased (Sr p (Zero) (Nil (List (Sub))) rs dns rs1) ws)
      (erased (Add dns bp x) ax) (erased (Add dnt bn y) ay) (erased (Add y nt x) an)
      (erased (Db2 p rt1 rs1 (Nil (List (Sub))) nt acc out) d) -> (Db2Top p rt rs (MkZ bp bn) acc out)))

(def-fns _ $ (many check-dbound2-c : (many (List (Sub)) p) (many (List (List (Sub))) rt rs) (many (Z) b) (many (List (List (Sub))) acc)
    -> (many (Bool) ok) (many (List (List (Sub))) out) (erased (IfT ok (Db2Top p rt rs b acc out)) w))
  (let-match many b (MkZ bp bn))
  (let ((many dnt) (many rt1) (erased wt)) (sort-drules-c p rt))
  (let ((many dns) (many rs1) (erased ws)) (sort-drules-c p rs))
  (let ((many x) (erased ax)) (add dns bp))
  (let ((many y) (erased ay)) (add dnt bn))
  (let-match many (le-dec y x) (LeY _ _ le) ((LeN _ _ _) (values (BFalse) acc (IfF _))))
  (let ((many nt) (erased mo)) (monus-c x y))
  (let-match erased mo (MoAdd _ _ _ an) (absurd (MoNeg _ _ l) (lt-le-absurd x y l le)))
  (let ((many l) (erased _)) (list-count _ rt1))
  (let ((many ok) (many out) (erased w)) (cdb2-c p rt1 rs1 (Nil _) nt acc (Succ $ Succ l)))
  (values ok out (match erased w _
    ((IfY _ d) (IfY _ (MkDb2Top p rt rs rt1 rs1 acc out dnt dns bp bn x y nt wt ws ax ay an d)))
    ((IfF _) (IfF _)))))

; The net transfer bound dbound2 <= b, read as ct + bn <= cs + bp for b = bp - bn.
(def-fns _ $ (erased db2-top-sound : (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (List (List (Sub))) rt rs acc out)
    (erased (Nat) bp bn ct cs l r) (erased (Exact os p) x) (erased (Db2Top p rt rs (MkZ bp bn) acc out) d) (erased (Count os rt ct) kt)
    (erased (Count os rs cs) ks) (erased (Add ct bn l) al) (erased (Add cs bp r) ar) -> (erased (Or (Lt l (Succ r)) (Hit os out)) o))
  (let-match erased d (MkDb2Top _ _ _ rt1 rs1 _ _ dnt dns _ _ sx y nt wt ws ax ay an d1))
  (let-match erased x (MkExact _ _ _ f _ _))
  (let ((erased ct1) (erased kt1) (erased et)) (sr-count os p (Zero) dnt (Zero) ct (Zero) ct (Nil _) rt rt1 f wt (CNil os) kt (AddZero (Zero)) (AddZero ct)))
  (let ((erased cs1) (erased ks1) (erased es)) (sr-count os p (Zero) dns (Zero) cs (Zero) cs (Nil _) rs rs1 f ws (CNil os) ks (AddZero (Zero)) (AddZero cs)))
  (let ((erased w0) (erased aw)) (add cs1 nt))
  (let-match erased (db2-sound os p rt1 rs1 (Nil _) acc out nt ct1 cs1 w0 x d1 kt1 ks1 (CNil os) aw) (OrL _ _ le) ((OrR _ _ h) (OrR _ _ h)))
  (let ((erased l2) (erased al2)) (add ct1 y))
  (let ((erased r2) (erased ar2)) (add w0 y))
  (let ((erased le2)) (le-sum ct1 w0 y y l2 r2 le (lt-succ y) al2 ar2))
  (let ((erased t1) (erased p1) (erased q1)) (plus-assoc dnt ct1 bn ct l et al))
  (let ((erased z1) (erased p2) (erased q2)) (plus-lcomm ct1 dnt bn y l2 ay al2))
  (let-match erased (add-eq ct1 bn z1 t1 p2 p1) (Refl _ _))
  (let-match erased (add-eq dnt z1 l2 l q2 q1) (Refl _ _))
  (let ((erased t2) (erased p3) (erased q3)) (plus-assoc cs1 nt y w0 r2 aw ar2))
  (let-match erased (add-eq y nt t2 sx (add-comm nt y t2 p3) an) (Refl _ _))
  (let ((erased t3) (erased p4) (erased q4)) (plus-assoc dns cs1 bp cs r es ar))
  (let ((erased z3) (erased p5) (erased q5)) (plus-lcomm cs1 dns bp t2 r2 ax q3))
  (let-match erased (add-eq cs1 bp z3 t3 p5 p4) (Refl _ _))
  (let-match erased (add-eq dns z3 r2 r q5 q4) (Refl _ _))
  (OrL _ _ le2))
