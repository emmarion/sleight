; A predicate on traces with one parameter x of any type X, as data, so that a parameterised one can be passed.
(def-adts $ (PredC : -> Type)
  enum
  (many MkPred : (erased Type X) (erased X x) (erased (TyCtor (X x) ((List (Col)) et) -> Type) Q) -> (PredC)))

(let ((erased Pred)) (PredC))

(def-adts $ (Holds : ((PredC) P) ((List (Col)) et) -> Type)
  enum
  (many MkHolds : (erased Type X) (erased X x) (erased (TyCtor (X x) ((List (Col)) et) -> Type) Q) (erased (List (Col)) et) (erased (Q x et) h)
      -> (Holds (MkPred X x Q) et)))

; r is the reverse of pre followed by w.
(def-adts $ (RevApp : (Type A) ((List A) pre) ((List A) w) ((List A) r) -> Type)
  enum
  (many RANil : (erased Type A) (erased (List A) w) -> (RevApp A (Nil A) w w))
  (many RACons : (erased Type A) (erased A s) (erased (List A) pre w r) (erased (RevApp A pre (Cons A s w) r) p)
      -> (RevApp A (Cons A s pre) w r)))

; The completion of the empty chromogram from d open chords and parity b is not balanced.
(def-adts $ (EndBad : ((Nat) d) ((Bool) b) -> Type)
  enum
  (many EB0 : -> (EndBad (Zero) (BFalse)))
  (many EB2 : (erased (Nat) d) (erased (Bool) b) -> (EndBad (Succ (Succ d)) b)))

(def-adts $ (PopPar : ((Gsym) s) ((Bool) b) ((Bool) c) -> Type)
  enum
  (many PPar0 : (erased (Bool) b) -> (PopPar (GPop0) b b))
  (many PPar1 : (erased (Bool) b c) (erased (Not b c) n) -> (PopPar (GPop1) b c)))

; The Kempe co-closure of P, as the least set of partial traces holding those whose completion satisfies P, holding each trace
; that a colour permutation sends into it, and holding each trace all of whose balanced matching chromograms are matched by a
; trace in it. AM P bs d b et pre: every chromogram w matching et from the stack bs, whose completion from d open chords and
; parity b is balanced, has its whole chromogram matched by a trace of the set.
(def-adts
  ((KC : (Pred P) ((List (Col)) et) -> Type)
    enum
    (many KIn : (erased Pred P) (erased (List (Col)) et ct) (erased (Ctr (C0) et ct) c) (erased (Holds P ct) p) -> (KC P et))
    (many KPerm : (erased Pred P) (erased (List (Col)) et et2) (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermT g et et2) pt)
        (erased (KC P et2) k) -> (KC P et))
    (many KGram : (erased Pred P) (erased (List (Col)) et) (erased (AM P (BS0) (Zero) (BFalse) et (Nil (Gsym))) a) -> (KC P et)))
  ((AM : (Pred P) ((Bstack) bs) ((Nat) d) ((Bool) b) ((List (Col)) et) ((List (Gsym)) pre) -> Type)
    enum
    (many AMEndOk : (erased Pred P) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b) (erased (List (Gsym)) pre w)
        (erased (GBal d b (Nil (Gsym))) g) (erased (RevApp (Gsym) pre (Nil (Gsym)) w) ra) (erased (Wit P w) wt)
        -> (AM P bs d b (Nil (Col)) pre))
    (many AMEndBad : (erased Pred P) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b) (erased (List (Gsym)) pre)
        (erased (EndBad d b) eb) -> (AM P bs d b (Nil (Col)) pre))
    (many AM0 : (erased Pred P) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b) (erased (List (Col)) et) (erased (List (Gsym)) pre)
        -> (AM P bs d b (Cons (Col) (C0) et) pre))
    (many AM1 : (erased Pred P) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b c) (erased (List (Col)) et) (erased (List (Gsym)) pre)
        (erased (Not b c) n) (erased (AM P bs d c et (Cons (Gsym) (GSkip) pre)) a) -> (AM P bs d b (Cons (Col) (C1) et) pre))
    (many AM23 : (erased Pred P) (erased (Bstack) bs bs1) (erased (Nat) d) (erased (Bool) b) (erased (Col) e) (erased (List (Col)) et)
        (erased (List (Gsym)) pre) (erased (Sym (GPush) bs e bs1) y) (erased (AM P bs1 (Succ d) b et (Cons (Gsym) (GPush) pre)) a)
        (erased (AMPop P bs d b e et pre) ap) -> (AM P bs d b (Cons (Col) e et) pre)))
  ((AMPop : (Pred P) ((Bstack) bs) ((Nat) d) ((Bool) b) ((Col) e) ((List (Col)) et) ((List (Gsym)) pre) -> Type)
    enum
    (many APNone : (erased Pred P) (erased (Nat) d) (erased (Bool) b) (erased (Col) e) (erased (List (Col)) et) (erased (List (Gsym)) pre)
        -> (AMPop P (BS0) d b e et pre))
    (many APZero : (erased Pred P) (erased (Bstack) bs) (erased (Bool) b) (erased (Col) e) (erased (List (Col)) et) (erased (List (Gsym)) pre)
        -> (AMPop P bs (Zero) b e et pre))
    (many APSome : (erased Pred P) (erased (Bstack) bs b0) (erased (Nat) d) (erased (Bool) b c) (erased (Gsym) s) (erased (Col) e)
        (erased (List (Col)) et) (erased (List (Gsym)) pre) (erased (Popped bs b0) pp) (erased (Sym s bs e b0) z) (erased (PopPar s b c) par)
        (erased (AM P b0 d c et (Cons (Gsym) s pre)) a) -> (AMPop P bs (Succ d) b e et pre)))
  ((Wit : (Pred P) ((List (Gsym)) w) -> Type)
    enum
    (many MkWit : (erased Pred P) (erased (List (Gsym)) w) (erased (List (Col)) et) (erased (MatchPG (BS0) et w) m) (erased (KC P et) k)
        -> (Wit P w))))

(def-fns _ $ (erased revapp-fn : (erased Type A) (erased (List A) pre w r1 r2) (subterm erased (RevApp A pre w r1) p) (erased (RevApp A pre w r2) q) ->
    (erased (Eq (List A) r1 r2) e))
  (match erased p _
    ((RANil _ _) (let-match erased q (RANil _ _)) (Refl _ r1))
    ((RACons _ s pre1 _ _ p1) (let-match erased q (RACons _ _ _ _ _ q1)) (revapp-fn A pre1 (Cons A s w) r1 r2 p1 q1))))

(def-fns _ $ (erased not-fn : (erased (Bool) b c d) (erased (Not b c) p) (erased (Not b d) q) -> (erased (Eq (Bool) c d) e))
  (match erased p _ ((NotT) (let-match erased q (NotT)) (Refl _ c)) ((NotF) (let-match erased q (NotF)) (Refl _ c))))

(def-fns _ $ (erased absurd endbad-bal : (erased (Nat) d) (erased (Bool) b) (erased (EndBad d b) e) (erased (GBal d b (Nil (Gsym))) g) -> (erased (False) f))
  (match erased e _ (absurd (EB0) g) (absurd (EB2 _ _) g)))

(def-adts $ (ES : -> Type)
  enum
  (many ESStart : -> (ES))
  (many ESTail : (many (Perm) g) -> (ES))
  (many ESEven : -> (ES))
  (many ESOdd : -> (ES)))

(def-adts $ (ESStep : ((ES) st) ((Col) c) ((ES) st2) -> Type)
  enum
  (many EStS0 : -> (ESStep (ESStart) (C0) (ESEven)))
  (many EStS1 : -> (ESStep (ESStart) (C1) (ESTail p123)))
  (many EStS2 : -> (ESStep (ESStart) (C2) (ESTail p312)))
  (many EStS3 : -> (ESStep (ESStart) (C3) (ESTail p231)))
  (many EStT0 : (erased (Perm) g) (erased (Col) c) (erased (PermC g c (C0)) p) -> (ESStep (ESTail g) c (ESTail g)))
  (many EStT1 : (erased (Perm) g) (erased (Col) c) (erased (PermC g c (C1)) p) -> (ESStep (ESTail g) c (ESTail g)))
  (many EStT2 : (erased (Perm) g) (erased (Col) c) (erased (PermC g c (C2)) p) -> (ESStep (ESTail g) c (ESEven)))
  (many EStT3 : (erased (Perm) g) (erased (Col) c) (erased (PermC g c (C3)) p) -> (ESStep (ESTail g) c (ESOdd)))
  (many EStE : (erased (Col) c) -> (ESStep (ESEven) c (ESEven)))
  (many EStO : (erased (Col) c) -> (ESStep (ESOdd) c (ESOdd))))

(def-adts $ (ESEnd : ((ES) st) ((Bool) b) -> Type)
  enum
  (many EESt : -> (ESEnd (ESStart) (BTrue)))
  (many EETl : (erased (Perm) g) -> (ESEnd (ESTail g) (BTrue)))
  (many EEEv : -> (ESEnd (ESEven) (BTrue)))
  (many EEOd : -> (ESEnd (ESOdd) (BFalse))))

(def-adts $ (ERun : ((ES) st) ((List (Col)) et) ((Bool) b) -> Type)
  enum
  (many ERNil : (erased (ES) st) (erased (Bool) b) (erased (ESEnd st b) p) -> (ERun st (Nil (Col)) b))
  (many ERCons : (erased (ES) st st2) (erased (Col) c) (erased (List (Col)) et) (erased (Bool) b) (erased (ESStep st c st2) p)
      (erased (ERun st2 et b) q) -> (ERun st (Cons (Col) c et) b)))

(def-fns _ $ (erased run-even : (subterm erased (List (Col)) et) -> (erased (ERun (ESEven) et (BTrue)) r))
  (match erased et _ ((Nil _) (ERNil (ESEven) (BTrue) (EEEv))) ((Cons _ c et1) (ERCons (ESEven) (ESEven) c et1 (BTrue) (EStE c) (run-even et1)))))

(def-fns _ $ (erased run-odd : (subterm erased (List (Col)) et) -> (erased (ERun (ESOdd) et (BFalse)) r))
  (match erased et _ ((Nil _) (ERNil (ESOdd) (BFalse) (EEOd))) ((Cons _ c et1) (ERCons (ESOdd) (ESOdd) c et1 (BFalse) (EStO c) (run-odd et1)))))

(def-fns _ $ (erased tail-run : (erased (Perm) g) (erased (List (Col)) l l2) (erased (Bool) b) (subterm erased (PermT g l l2) p)
    (erased (EvenTail l2 b) e) -> (erased (ERun (ESTail g) l b) r))
  (match erased p _
    ((PTNil _) (let-match erased e (ETNil)) (ERNil (ESTail g) b (EETl g)))
    ((PTCons _ c d l1 l3 pc p1)
      (match erased e _
        ((ET0 _ _ e1) (ERCons (ESTail g) (ESTail g) c l1 b (EStT0 g c pc) (tail-run g l1 l3 b p1 e1)))
        ((ET1 _ _ e1) (ERCons (ESTail g) (ESTail g) c l1 b (EStT1 g c pc) (tail-run g l1 l3 b p1 e1)))
        ((ET2 _) (ERCons (ESTail g) (ESEven) c l1 b (EStT2 g c pc) (run-even l1)))
        ((ET3 _) (ERCons (ESTail g) (ESOdd) c l1 b (EStT3 g c pc) (run-odd l1)))))))

(def-fns _ $ (erased tail-id : (subterm erased (List (Col)) l) -> (erased (PermT p123 l l) p))
  (match erased l _
    ((Nil _) (PTNil p123))
    ((Cons _ c l1)
      (PTCons p123 c c l1 l1 (match erased c (((PermC p123 c c) q)) ((C0) (PC0 p123)) ((C1) (PC1 (C1) (C2) (C3))) ((C2) (PC2 (C1) (C2) (C3))) ((C3) (PC3 (C1) (C2) (C3))))
        (tail-id l1)))))

(def-fns _ $ (erased even-run : (erased (List (Col)) et) (erased (Bool) b) (erased (EvenT et b) e) -> (erased (ERun (ESStart) et b) r))
  (match erased e _
    ((EvNil) (ERNil (ESStart) b (EESt)))
    ((Ev0 l) (ERCons (ESStart) (ESEven) (C0) l b (EStS0) (run-even l)))
    ((Ev1 l _ p) (ERCons (ESStart) (ESTail p123) (C1) l b (EStS1) (tail-run p123 l l b (tail-id l) p)))
    ((Ev2 l l2 _ q p) (ERCons (ESStart) (ESTail p312) (C2) l b (EStS2) (tail-run p312 l l2 b q p)))
    ((Ev3 l l2 _ q p) (ERCons (ESStart) (ESTail p231) (C3) l b (EStS3) (tail-run p231 l l2 b q p)))))

(def-fns _ $ (erased permc-fn : (erased (Perm) g) (erased (Col) c d1 d2) (erased (PermC g c d1) p) (erased (PermC g c d2) q) -> (erased (Eq (Col) d1 d2) e))
  (match erased p _
    ((PC0 _) (let-match erased q (PC0 _)) (Refl _ d1))
    ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (Refl _ d1))
    ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (Refl _ d1))
    ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (Refl _ d1))))

(def-fns _ $ (erased esstep-fn : (erased (ES) st s1 s2) (erased (Col) c) (erased (ESStep st c s1) p) (erased (ESStep st c s2) q) -> (erased (Eq (ES) s1 s2) e))
  (match erased p _
    ((EStS0) (let-match erased q (EStS0)) (Refl _ s1))
    ((EStS1) (let-match erased q (EStS1)) (Refl _ s1))
    ((EStS2) (let-match erased q (EStS2)) (Refl _ s1))
    ((EStS3) (let-match erased q (EStS3)) (Refl _ s1))
    ((EStT0 g _ p1)
      (match erased q _
        ((EStT0 _ _ _) (Refl _ s1)) (absurd (EStT1 _ _ q1) (permc-fn g c (C0) (C1) p1 q1))
        (absurd (EStT2 _ _ q1) (permc-fn g c (C0) (C2) p1 q1)) (absurd (EStT3 _ _ q1) (permc-fn g c (C0) (C3) p1 q1))))
    ((EStT1 g _ p1)
      (match erased q _
        (absurd (EStT0 _ _ q1) (permc-fn g c (C1) (C0) p1 q1)) ((EStT1 _ _ _) (Refl _ s1))
        (absurd (EStT2 _ _ q1) (permc-fn g c (C1) (C2) p1 q1)) (absurd (EStT3 _ _ q1) (permc-fn g c (C1) (C3) p1 q1))))
    ((EStT2 g _ p1)
      (match erased q _
        (absurd (EStT0 _ _ q1) (permc-fn g c (C2) (C0) p1 q1)) (absurd (EStT1 _ _ q1) (permc-fn g c (C2) (C1) p1 q1))
        ((EStT2 _ _ _) (Refl _ s1)) (absurd (EStT3 _ _ q1) (permc-fn g c (C2) (C3) p1 q1))))
    ((EStT3 g _ p1)
      (match erased q _
        (absurd (EStT0 _ _ q1) (permc-fn g c (C3) (C0) p1 q1)) (absurd (EStT1 _ _ q1) (permc-fn g c (C3) (C1) p1 q1))
        (absurd (EStT2 _ _ q1) (permc-fn g c (C3) (C2) p1 q1)) ((EStT3 _ _ _) (Refl _ s1))))
    ((EStE _) (let-match erased q (EStE _)) (Refl _ s1))
    ((EStO _) (let-match erased q (EStO _)) (Refl _ s1))))

(def-fns _ $ (erased esend-fn : (erased (ES) st) (erased (Bool) b c) (erased (ESEnd st b) p) (erased (ESEnd st c) q) -> (erased (Eq (Bool) b c) e))
  (match erased p _
    ((EESt) (let-match erased q (EESt)) (Refl _ b))
    ((EETl _) (let-match erased q (EETl _)) (Refl _ b))
    ((EEEv) (let-match erased q (EEEv)) (Refl _ b))
    ((EEOd) (let-match erased q (EEOd)) (Refl _ b))))

(def-fns _ $ (erased erun-fn : (erased (ES) st) (erased (List (Col)) et) (erased (Bool) b c) (subterm erased (ERun st et b) p)
    (erased (ERun st et c) q) -> (erased (Eq (Bool) b c) e))
  (match erased p _
    ((ERNil _ _ e1) (let-match erased q (ERNil _ _ e2)) (esend-fn st b c e1 e2))
    ((ERCons _ s1 x et1 _ p1 q1)
      (let-match erased q (ERCons _ s2 _ _ _ p2 q2))
      (let-match erased (esstep-fn st s1 s2 x p1 p2) (Refl _ _))
      (erun-fn s1 et1 b c q1 q2))))

(def-adts $ (NotOdd : ((ES) st) -> Type)
  enum
  (many NOS : -> (NotOdd (ESStart)))
  (many NOT : (erased (Perm) g) -> (NotOdd (ESTail g)))
  (many NOE : -> (NotOdd (ESEven))))

(def-fns _ $ (erased notodd-end : (erased (ES) st) (erased (NotOdd st) n) -> (erased (ESEnd st (BTrue)) e))
  (match erased n _ ((NOS) (EESt)) ((NOT g) (EETl g)) ((NOE) (EEEv))))

; Every trace of t, read from the evenness state st, is even.
(def-adts
  ((CEv : ((Ctree) t) ((ES) st) -> Type)
    enum
    (many CEvE : (erased (ES) st) -> (CEv (CEmpty) st))
    (many CEvEv : (erased (Ctree) t) -> (CEv t (ESEven)))
    (many CEvL : (erased (Ctree) lf) (erased (ES) st) (erased (NotOdd st) n) -> (CEv (CLeaf lf) st))
    (many CEvN : (erased (Ctree) t1 t2 t3) (erased (ES) st) (erased (CEvAt (CNode t1 t2 t3) st (C0)) a0) (erased (CEvAt (CNode t1 t2 t3) st (C1)) a1)
        (erased (CEvAt (CNode t1 t2 t3) st (C2)) a2) (erased (CEvAt (CNode t1 t2 t3) st (C3)) a3) -> (CEv (CNode t1 t2 t3) st)))
  ((CEvAt : ((Ctree) t) ((ES) st) ((Col) e) -> Type)
    enum
    (many MkCEvAt : (erased (Ctree) t u) (erased (ES) st st2) (erased (Col) e) (erased (CtSel t e u) s) (erased (ESStep st e st2) p)
        (erased (CEv u st2) c) -> (CEvAt t st e))))

(def-fns _ $ (erased cev-mem : (erased (Ctree) t) (erased (ES) st) (subterm erased (List (Col)) et) (erased (CEv t st) c) (erased (CtMem t et) m) ->
    (erased (ERun st et (BTrue)) r))
  (match erased c _
    (absurd (CEvE _) (mem-empty et m))
    ((CEvEv _) (run-even et))
    ((CEvL lf _ n) (let-match erased (leaf-mem-nil lf et m) (Refl _ _)) (ERNil st (BTrue) (notodd-end st n)))
    ((CEvN t1 t2 t3 _ a0 a1 a2 a3)
      (let ((erased e) (erased et1) (erased q) (erased u) (erased s) (erased m1)) (cons-mem t1 t2 t3 t et (CCNode t1 t2 t3) m))
      (let-match erased q (Refl _ _))
      (let-match erased (match erased e (((CEvAt t st e) k)) ((C0) a0) ((C1) a1) ((C2) a2) ((C3) a3)) (MkCEvAt _ u2 _ st2 _ s2 p c1))
      (let-match erased (sel-fn t u u2 e s s2) (Refl _ _))
      (ERCons st st2 e et1 (BTrue) p (cev-mem u st2 et1 c1 m1)))))

; One step of a balanced completion: from d open chords and parity b, the symbol s leads to d2 and b2.
(def-adts $ (GStep : ((Nat) d) ((Bool) b) ((Gsym) s) ((Nat) d2) ((Bool) b2) -> Type)
  enum
  (many GStPush : (erased (Nat) d) (erased (Bool) b) -> (GStep d b (GPush) (Succ d) b))
  (many GStSkip : (erased (Nat) d) (erased (Bool) b c) (erased (Not b c) n) -> (GStep d b (GSkip) d c))
  (many GStPop0 : (erased (Nat) d) (erased (Bool) b) -> (GStep (Succ d) b (GPop0) d b))
  (many GStPop1 : (erased (Nat) d) (erased (Bool) b c) (erased (Not b c) n) -> (GStep (Succ d) b (GPop1) d c)))

; Every chromogram of n symbols whose completion from d open chords and parity b is balanced is in gs.
(def-adts
  ((GCov : ((GSet) gs) ((Nat) d) ((Bool) b) ((Nat) n) -> Type)
    enum
    (many GCNilOk : (erased (GSet) gs) (erased (Nat) d) (erased (Bool) b) (erased (GBal d b (Nil (Gsym))) g) (erased (GRoot gs (Succ (Zero))) r)
        -> (GCov gs d b (Zero)))
    (many GCNilBad : (erased (GSet) gs) (erased (Nat) d) (erased (Bool) b) (erased (EndBad d b) e) -> (GCov gs d b (Zero)))
    (many GCVac : (erased (GSet) gs) (erased (Nat) d n) (erased (Bool) b) (erased (Lt (Succ n) d) l) -> (GCov gs d b n))
    (many GCCons : (erased (GSet) gs) (erased (Nat) d n) (erased (Bool) b) (erased (GCovAt gs d b n (GPush)) c0) (erased (GCovAt gs d b n (GSkip)) c1)
        (erased (GCovAt gs d b n (GPop0)) c2) (erased (GCovAt gs d b n (GPop1)) c3) -> (GCov gs d b (Succ n))))
  ((GCovAt : ((GSet) gs) ((Nat) d) ((Bool) b) ((Nat) n) ((Gsym) s) -> Type)
    enum
    (many GCAOk : (erased (GSet) gs gs2) (erased (Nat) d d2 n) (erased (Bool) b b2) (erased (Gsym) s) (erased (GStep d b s d2 b2) st)
        (erased (GSel gs s gs2) p) (erased (GCov gs2 d2 b2 n) c) -> (GCovAt gs d b n s))
    (many GCAPop0 : (erased (GSet) gs) (erased (Bool) b) (erased (Nat) n) -> (GCovAt gs (Zero) b n (GPop0)))
    (many GCAPop1 : (erased (GSet) gs) (erased (Bool) b) (erased (Nat) n) -> (GCovAt gs (Zero) b n (GPop1)))))

(def-fns _ $ (erased gstep-fn : (erased (Nat) d d2 d3) (erased (Bool) b b2 b3) (erased (Gsym) s) (erased (GStep d b s d2 b2) p)
    (erased (GStep d b s d3 b3) q) -> (erased (Eq (Nat) d2 d3) e) (erased (Eq (Bool) b2 b3) f))
  (match erased p _
    ((GStPush _ _) (let-match erased q (GStPush _ _)) (values (Refl _ d2) (Refl _ b2)))
    ((GStSkip _ _ _ n1) (let-match erased q (GStSkip _ _ _ n2)) (let-match erased (not-fn b b2 b3 n1 n2) (Refl _ _)) (values (Refl _ d2) (Refl _ b2)))
    ((GStPop0 _ _) (let-match erased q (GStPop0 _ _)) (values (Refl _ d2) (Refl _ b2)))
    ((GStPop1 _ _ _ n1) (let-match erased q (GStPop1 _ _ _ n2)) (let-match erased (not-fn b b2 b3 n1 n2) (Refl _ _)) (values (Refl _ d2) (Refl _ b2)))))

(def-fns _ $ (erased gbal-step : (erased (Nat) d) (erased (Bool) b) (erased (Gsym) s) (erased (List (Gsym)) w) (erased (GBal d b (Cons (Gsym) s w)) g) ->
    (erased (Nat) d2) (erased (Bool) b2) (erased (GStep d b s d2 b2) st) (erased (GBal d2 b2 w) g2))
  (match erased g _
    ((GBPush _ _ _ g1) (values (Succ d) b (GStPush d b) g1))
    ((GBSkip _ _ c _ n g1) (values d c (GStSkip d b c n) g1))
    ((GBPop0 d1 _ _ g1) (values d1 b (GStPop0 d1 b) g1))
    ((GBPop1 d1 _ c _ n g1) (values d1 c (GStPop1 d1 b c n) g1))))

(def-fns _ $ (erased gbal-depth : (erased (Nat) d n) (erased (Bool) b) (subterm erased (List (Gsym)) w) (erased (GBal d b w) g)
    (erased (Length (Gsym) w n) l) -> (erased (Lt d (Succ (Succ n))) r))
  (match erased w _
    ((Nil _)
      (let-match erased l (LengthNil _))
      (match erased g _ ((GBEnd0) (LtZ (Succ (Zero)))) ((GBEnd1 _) (LtS (Zero) (Succ (Zero)) (LtZ (Zero))))))
    ((Cons _ s w1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (match erased g _
        ((GBPush _ _ _ g1) (lt-weaken d (Succ (Succ n1)) (lt-weaken d (Succ n1) (lt-pred d (Succ n1) (gbal-depth (Succ d) n1 b w1 g1 l1)))))
        ((GBSkip _ _ c _ _ g1) (lt-weaken d (Succ n) (gbal-depth d n1 c w1 g1 l1)))
        ((GBPop0 d1 _ _ g1) (LtS d1 (Succ n) (gbal-depth d1 n1 b w1 g1 l1)))
        ((GBPop1 d1 _ c _ _ g1) (LtS d1 (Succ n) (gbal-depth d1 n1 c w1 g1 l1)))))))

(def-fns _ $ (erased gcov-mem : (erased (GSet) gs) (erased (Nat) d n) (erased (Bool) b) (subterm erased (List (Gsym)) w) (erased (GCov gs d b n) c)
    (erased (Length (Gsym) w n) l) (erased (GBal d b w) g) -> (erased (GMem gs w) r))
  (match erased c _
    (absurd (GCVac _ _ _ _ lv) (lt-asym (Succ n) d lv (gbal-depth d n b w g l)))
    ((GCNilOk _ _ _ _ rt) (let-match erased l (LengthNil _)) (let-match erased rt (GROne)) (GMNil))
    (absurd (GCNilBad _ _ _ e) (let-match erased l (LengthNil _)) (endbad-bal d b e g))
    ((GCCons _ _ n1 _ c0 c1 c2 c3)
      (let-match erased l (LengthCons _ s w1 _ l1))
      (let ((erased d2) (erased b2) (erased st) (erased g1)) (gbal-step d b s w1 g))
      (match erased (match erased s (((GCovAt gs d b n1 s) k)) ((GPush) c0) ((GSkip) c1) ((GPop0) c2) ((GPop1) c3)) _
        ((GCAOk _ gs2 _ d3 _ _ b3 _ st2 p c4)
          (let ((erased e1) (erased e2)) (gstep-fn d d2 d3 b b2 b3 s st st2))
          (let-match erased e1 (Refl _ _))
          (let-match erased e2 (Refl _ _))
          (GMCons gs gs2 s w1 p (gcov-mem gs2 d2 n1 b2 w1 c4 l1 g1)))
        (absurd (GCAPop0 _ _ _) st)
        (absurd (GCAPop1 _ _ _) st)))))

(let ((erased RS)) (Rx (GSet)))

; Matches in a list of gram sets, each read from its own stack.
(def-adts $ (PCnt : ((List RS) ps) ((List (Col)) et) ((Nat) n) -> Type)
  enum
  (many PCNil : (erased (List (Col)) et) -> (PCnt (Nil RS) et (Zero)))
  (many PCCons : (erased (Bstack) bs) (erased (GSet) gs) (erased (List RS) ps) (erased (List (Col)) et) (erased (Nat) a b n)
      (erased (MC gs bs et a) m) (erased (PCnt ps et b) c) (erased (Add a b n) p) -> (PCnt (Cons RS (MkRx (GSet) bs gs) ps) et n)))

(def-fns _ $ (erased pcnt-exists : (subterm erased (List RS) ps) (erased (List (Col)) et) -> (erased (Nat) n) (erased (PCnt ps et n) c))
  (let-match erased ps (Cons _ x rest) ((Nil _) (values (Zero) (PCNil et))))
  (let-match erased x (MkRx _ bs gs))
  (let ((erased a) (erased m)) (mc-exists gs bs et))
  (let ((erased b) (erased c)) (pcnt-exists rest et))
  (let ((erased n) (erased p)) (add a b))
  (values n (PCCons bs gs rest et a b n m c p)))

(def-fns _ $ (erased pcnt-fn : (erased (List RS) ps) (erased (List (Col)) et) (erased (Nat) n m) (subterm erased (PCnt ps et n) p)
    (erased (PCnt ps et m) q) -> (erased (Eq (Nat) n m) e))
  (match erased p _
    ((PCNil _) (let-match erased q (PCNil _)) (Refl _ n))
    ((PCCons bs gs rest _ a b _ ma ca pa)
      (let-match erased q (PCCons _ _ _ _ a2 b2 _ ma2 ca2 pa2))
      (let-match erased (mc-fn gs bs et a a2 ma ma2) (Refl _ _))
      (let-match erased (pcnt-fn rest et b b2 ca ca2) (Refl _ _))
      (add-fn a b n m pa pa2))))

(def-adts $ (RSCons : ((Bstack) bs) ((GSet) gs) ((List RS) a) ((List RS) b) -> Type)
  enum
  (many RSE : (erased (Bstack) bs) (erased (List RS) a) -> (RSCons bs (GSG (GEmpty)) a a))
  (many RSC : (erased (Bstack) bs) (erased (GSet) gs) (erased (List RS) a) -> (RSCons bs gs a (Cons RS (MkRx (GSet) bs gs) a))))

(def-adts $ (PPop : ((Bstack) bs) ((Col) e) ((GSet) gs) ((List RS) a) ((List RS) c) -> Type)
  enum
  (many PPNone : (erased (Col) e) (erased (GSet) gs) (erased (List RS) a) -> (PPop (BS0) e gs a a))
  (many PPSome : (erased (Bstack) bs b) (erased (Gsym) s) (erased (Col) e) (erased (GSet) gs g2) (erased (List RS) a c)
      (erased (Popped bs b) pp) (erased (Sym s bs e b) z) (erased (GSel gs s g2) p) (erased (RSCons b g2 a c) q) -> (PPop bs e gs a c)))

; b is a with the gram sets of x shifted past each symbol matching e.
(def-adts $ (PStepE : (RS x) ((Col) e) ((List RS) a) ((List RS) b) -> Type)
  enum
  (many PSE0 : (erased RS x) (erased (List RS) a) -> (PStepE x (C0) a a))
  (many PSE1 : (erased (Bstack) bs) (erased (GSet) gs g1) (erased (List RS) a b) (erased (GSel gs (GSkip) g1) p) (erased (RSCons bs g1 a b) q)
      -> (PStepE (MkRx (GSet) bs gs) (C1) a b))
  (many PSE23 : (erased (Bstack) bs bs1) (erased (Col) e) (erased (GSet) gs g1) (erased (List RS) a c b) (erased (Sym (GPush) bs e bs1) y)
      (erased (GSel gs (GPush) g1) p) (erased (PPop bs e gs a c) pp) (erased (RSCons bs1 g1 c b) q) -> (PStepE (MkRx (GSet) bs gs) e a b)))

(def-adts $ (PSplitE : ((Col) e) ((List RS) a) ((List RS) ps) ((List RS) s) -> Type)
  enum
  (many PSNil : (erased (Col) e) (erased (List RS) a) -> (PSplitE e a (Nil RS) a))
  (many PSCons : (erased (Col) e) (erased RS x) (erased (List RS) a b rest s) (erased (PStepE x e a b) p) (erased (PSplitE e b rest s) q)
      -> (PSplitE e a (Cons RS x rest) s)))

(def-fns _ $ (erased rscons-cnt : (erased (Bstack) bs) (erased (GSet) gs) (erased (List RS) a b) (erased (List (Col)) et) (erased (Nat) u v w)
    (erased (RSCons bs gs a b) p) (erased (PCnt a et u) ca) (erased (PCnt b et w) cb) (erased (MC gs bs et v) m) -> (erased (Add v u w) r))
  (match erased p _
    ((RSE _ _) (let-match erased (mc-zero bs et v m) (Refl _ _)) (let-match erased (pcnt-fn a et u w ca cb) (Refl _ _)) (AddZero u))
    ((RSC _ _ _)
      (let-match erased cb (PCCons _ _ _ _ v2 u2 _ m2 c2 s))
      (let-match erased (mc-fn gs bs et v v2 m m2) (Refl _ _))
      (let-match erased (pcnt-fn a et u u2 ca c2) (Refl _ _))
      s)))

(def-fns _ $ (erased pstepe-cnt : (erased (Bstack) bs) (erased (GSet) gs) (erased (Col) e) (erased (List RS) a b) (erased (List (Col)) et)
    (erased (Nat) u v w) (erased (PStepE (MkRx (GSet) bs gs) e a b) st) (erased (PCnt a et u) ca) (erased (PCnt b et w) cb)
    (erased (MC gs bs (Cons (Col) e et) v) m) -> (erased (Add v u w) r))
  (match erased st _
    ((PSE0 _ _) (let-match erased (mc-inv-0 gs bs et v m) (Refl _ _)) (let-match erased (pcnt-fn a et u w ca cb) (Refl _ _)) (AddZero u))
    ((PSE1 _ _ g1 _ _ p q)
      (let ((erased g2) (erased p2) (erased m1)) (mc-inv-skip gs bs et v m))
      (let-match erased (gsel-fn gs g1 g2 (GSkip) p p2) (Refl _ _))
      (rscons-cnt bs g1 a b et u v w q ca cb m1))
    ((PSE23 _ bs1 _ _ g1 _ c _ y p pp q)
      (let ((erased uc) (erased cq)) (pcnt-exists c et))
      (match erased pp _
        ((PPNone _ _ _)
          (let ((erased g2) (erased p2) (erased m2)) (mc-inv-push gs bs1 e et v y m))
          (let-match erased (gsel-fn gs g1 g2 (GPush) p p2) (Refl _ _))
          (rscons-cnt bs1 g1 a b et u v w q ca cb m2))
        ((PPSome _ b0 s _ _ g2 _ _ pp1 z p2 q2)
          (let ((erased n1) (erased n2) (erased h1) (erased h2) (erased s3) (erased m3) (erased s4) (erased m4) (erased ad))
            (mc-inv-pp gs bs b0 bs1 s e et v y pp1 z m))
          (let-match erased (gsel-fn gs g1 h1 (GPush) p s3) (Refl _ _))
          (let-match erased (gsel-fn gs g2 h2 s p2 s4) (Refl _ _))
          (let ((erased k2)) (rscons-cnt b0 g2 a c et u n2 uc q2 ca cq m4))
          (let ((erased k3)) (rscons-cnt bs1 g1 c b et uc n1 w q cq cb m3))
          (let ((erased k) (erased q4) (erased q5)) (add-assoc-back n1 n2 u uc w k3 k2))
          (let-match erased (add-fn n1 n2 k v q4 ad) (Refl _ _))
          q5)))))

(def-fns _ $ (erased psplit-cnt : (erased (Col) e) (erased (List RS) a ps s) (erased (List (Col)) et) (erased (Nat) u v w)
    (subterm erased (PSplitE e a ps s) sp) (erased (PCnt a et u) ca) (erased (PCnt s et w) cs) (erased (PCnt ps (Cons (Col) e et) v) cp) ->
    (erased (Add v u w) res))
  (match erased sp _
    ((PSNil _ _) (let-match erased cp (PCNil _)) (let-match erased (pcnt-fn a et u w ca cs) (Refl _ _)) (AddZero u))
    ((PSCons _ x _ b rest _ st q)
      (let-match erased cp (PCCons bs gs _ _ a1 b1 _ m c p))
      (let ((erased ub) (erased cb)) (pcnt-exists b et))
      (let ((erased q1)) (pstepe-cnt bs gs e a b et u a1 ub st ca cb m))
      (let ((erased q2)) (psplit-cnt e b rest s et ub b1 w q cb cs c))
      (let ((erased k) (erased q3) (erased q4)) (add-assoc-back b1 a1 u ub w q2 q1))
      (let-match erased (add-fn b1 a1 k v q3 (add-comm a1 b1 v p)) (Refl _ _))
      q4)))

(def-adts $ (PZero : ((List RS) ps) -> Type)
  enum
  (many PZNil : -> (PZero (Nil RS)))
  (many PZCons : (erased (Bstack) bs) (erased (List RS) ps) (erased (PZero ps) p) -> (PZero (Cons RS (MkRx (GSet) bs (GSG (GEmpty))) ps))))

(def-fns _ $ (erased pzero-cnt : (erased (List RS) ps) (erased (List (Col)) et) (erased (Nat) n) (subterm erased (PZero ps) z) (erased (PCnt ps et n) c) ->
    (erased (Eq (Nat) n (Zero)) e))
  (match erased z _
    ((PZNil) (let-match erased c (PCNil _)) (Refl _ n))
    ((PZCons bs rest z1)
      (let-match erased c (PCCons _ _ _ _ a b _ m c1 p))
      (let-match erased (mc-zero bs et a m) (Refl _ _))
      (let-match erased (pzero-cnt rest et b z1 c1) (Refl _ _))
      (let-match erased p (AddZero _))
      (Refl _ n))))

; For every even trace et of length k, read from the evenness state st, the multiplicity of et in t bounds the matches of ps.
(def-adts
  ((GE : ((Ctree) t) ((List RS) ps) ((ES) st) ((Nat) k) -> Type)
    enum
    (many GEDead : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (erased (Nat) k) (erased (PZero ps) z) -> (GE t ps st k))
    (many GEOdd : (erased (Ctree) t) (erased (List RS) ps) (erased (Nat) k) -> (GE t ps (ESOdd) k))
    (many GENil : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (erased (Nat) n c) (erased (CtRoot t n) rt)
        (erased (PCnt ps (Nil (Col)) c) pc) (erased (Lt c (Succ n)) le) -> (GE t ps st (Zero)))
    (many GES : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (erased (Nat) k) (erased (GEAt t ps st k (C0)) a0)
        (erased (GEAt t ps st k (C1)) a1) (erased (GEAt t ps st k (C2)) a2) (erased (GEAt t ps st k (C3)) a3) -> (GE t ps st (Succ k))))
  ((GEAt : ((Ctree) t) ((List RS) ps) ((ES) st) ((Nat) k) ((Col) e) -> Type)
    enum
    (many MkGEAt : (erased (Ctree) t u) (erased (List RS) ps ps2) (erased (ES) st st2) (erased (Nat) k) (erased (Col) e) (erased (CtSel t e u) s)
        (erased (PSplitE e (Nil RS) ps ps2) sp) (erased (ESStep st e st2) p) (erased (GE u ps2 st2 k) g) -> (GEAt t ps st k e))))

(def-fns _ $ (erased ge-cnt : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (erased (Nat) k) (subterm erased (List (Col)) et) (erased (Nat) n c)
    (erased (GE t ps st k) g) (erased (Length (Col) et k) len) (erased (ERun st et (BTrue)) run) (erased (CtSub t et n) s) (erased (PCnt ps et c) pc)
    -> (erased (Lt c (Succ n)) r))
  (match erased g _
    ((GEDead _ _ _ _ z) (let-match erased (pzero-cnt ps et c z pc) (Refl _ _)) (LtZ n))
    (absurd (GEOdd _ _ _) (erun-fn (ESOdd) et (BFalse) (BTrue) (run-odd et) run))
    ((GENil _ _ _ n0 c0 rt pc0 le)
      (let-match erased len (LengthNil _))
      (let-match erased s (SubNil _ _ rt2))
      (let-match erased (root-fn t n n0 rt2 rt) (Refl _ _))
      (let-match erased (pcnt-fn ps et c c0 pc pc0) (Refl _ _))
      le)
    ((GES _ _ _ k1 a0 a1 a2 a3)
      (let-match erased len (LengthCons _ e et1 _ len1))
      (let-match erased (match erased e (((GEAt t ps st k1 e) q)) ((C0) a0) ((C1) a1) ((C2) a2) ((C3) a3)) (MkGEAt _ u _ ps2 _ st2 _ _ sl sp p g1))
      (let-match erased run (ERCons _ st3 _ _ _ p3 run1))
      (let-match erased (esstep-fn st st2 st3 e p p3) (Refl _ _))
      (let ((erased c2) (erased pc2)) (pcnt-exists ps2 et1))
      (let-match erased (add-fn c (Zero) c2 c (psplit-cnt e (Nil RS) ps ps2 et1 (Zero) c c2 sp (PCNil et1) pc2 pc) (add-zero-right c)) (Refl _ _))
      (ge-cnt u ps2 st2 k1 et1 n c g1 len1 run1 (sub-sel t u e et1 n s sl) pc2))))

; The reversed trace prefix etc matches the reversed chromogram prefix pre, from stack bs0 to bs.
(def-adts $ (MPre : ((Bstack) bs0) ((List (Col)) etc) ((List (Gsym)) pre) ((Bstack) bs) -> Type)
  enum
  (many MPreNil : (erased (Bstack) bs0) -> (MPre bs0 (Nil (Col)) (Nil (Gsym)) bs0))
  (many MPreCons : (erased (Bstack) bs0 bs bs2) (erased (List (Col)) etc) (erased (List (Gsym)) pre) (erased (Col) e) (erased (Gsym) s)
      (erased (MPre bs0 etc pre bs) p) (erased (Sym s bs e bs2) y) -> (MPre bs0 (Cons (Col) e etc) (Cons (Gsym) s pre) bs2)))

(def-adts $ (GPre : ((Nat) d0) ((Bool) b0) ((List (Gsym)) pre) ((Nat) d) ((Bool) b) -> Type)
  enum
  (many GPreNil : (erased (Nat) d0) (erased (Bool) b0) -> (GPre d0 b0 (Nil (Gsym)) d0 b0))
  (many GPreCons : (erased (Nat) d0 d d2) (erased (Bool) b0 b b2) (erased (List (Gsym)) pre) (erased (Gsym) s)
      (erased (GPre d0 b0 pre d b) p) (erased (GStep d b s d2 b2) st) -> (GPre d0 b0 (Cons (Gsym) s pre) d2 b2)))

(def-fns _ $ (erased mpre-app : (erased (Bstack) bs0 bs) (erased (List (Col)) etc et fe) (erased (List (Gsym)) pre w fw)
    (subterm erased (MPre bs0 etc pre bs) p) (erased (MatchPG bs et w) m) (erased (RevApp (Col) etc et fe) re) (erased (RevApp (Gsym) pre w fw) rw)
    -> (erased (MatchPG bs0 fe fw) r))
  (match erased p _
    ((MPreNil _) (let-match erased re (RANil _ _)) (let-match erased rw (RANil _ _)) m)
    ((MPreCons _ bs1 _ etc1 pre1 e s p1 y)
      (let-match erased re (RACons _ _ _ _ _ re1))
      (let-match erased rw (RACons _ _ _ _ _ rw1))
      (mpre-app bs0 bs1 etc1 (Cons _ e et) fe pre1 (Cons _ s w) fw p1 (MPCons bs1 bs e s et w y m) re1 rw1))))

(def-fns _ $ (erased gstep-bal : (erased (Nat) d d2) (erased (Bool) b b2) (erased (Gsym) s) (erased (List (Gsym)) w) (erased (GStep d b s d2 b2) st)
    (erased (GBal d2 b2 w) g) -> (erased (GBal d b (Cons (Gsym) s w)) r))
  (match erased st _
    ((GStPush _ _) (GBPush d b w g))
    ((GStSkip _ _ _ n) (GBSkip d b b2 w n g))
    ((GStPop0 _ _) (GBPop0 d2 b w g))
    ((GStPop1 _ _ _ n) (GBPop1 d2 b b2 w n g))))

(def-fns _ $ (erased gpre-app : (erased (Nat) d0 d) (erased (Bool) b0 b) (erased (List (Gsym)) pre w fw) (subterm erased (GPre d0 b0 pre d b) p)
    (erased (GBal d b w) g) (erased (RevApp (Gsym) pre w fw) rw) -> (erased (GBal d0 b0 fw) r))
  (match erased p _
    ((GPreNil _ _) (let-match erased rw (RANil _ _)) g)
    ((GPreCons _ d1 _ _ b1 _ pre1 s p1 st)
      (let-match erased rw (RACons _ _ _ _ _ rw1))
      (gpre-app d0 d1 b0 b1 pre1 (Cons _ s w) fw p1 (gstep-bal d1 d b1 b s w st g) rw1))))

(def-fns _ $ (erased matchpg-length : (erased (Bstack) bs) (erased (List (Col)) et) (erased (List (Gsym)) w) (erased (Nat) n)
    (subterm erased (MatchPG bs et w) m) (erased (Length (Col) et n) l) -> (erased (Length (Gsym) w n) r))
  (match erased m _
    ((MPNil _) (let-match erased l (LengthNil _)) (LengthNil _))
    ((MPCons _ bs2 e s et1 w1 _ m1) (let-match erased l (LengthCons _ _ _ n1 l1)) (LengthCons _ s w1 n1 (matchpg-length bs2 et1 w1 n1 m1 l1)))))

(def-fns _ $ (erased revapp-exists : (erased Type A) (subterm erased (List A) pre) (erased (List A) w) -> (erased (List A) r) (erased (RevApp A pre w r) p))
  (match erased pre _
    ((Nil _) (values w (RANil A w)))
    ((Cons _ s pre1) (let ((erased r) (erased p)) (revapp-exists A pre1 (Cons A s w))) (values r (RACons A s pre1 w r p)))))

(def-fns _ $ (erased not-exists : (erased (Bool) b) -> (erased (Bool) c) (erased (Not b c) n))
  (match erased b _ ((BTrue) (values (BFalse) (NotT))) ((BFalse) (values (BTrue) (NotF)))))

(def-fns _ $ (erased end-dec : (erased (Nat) d) (erased (Bool) b) -> (erased (Or (GBal d b (Nil (Gsym))) (EndBad d b)) r))
  (match erased d _
    ((Zero) (match erased b _ ((BTrue) (InL _ _ (GBEnd0))) ((BFalse) (InR _ _ (EB0)))))
    ((Succ d1) (match erased d1 _ ((Zero) (InL _ _ (GBEnd1 b))) ((Succ d2) (InR _ _ (EB2 d2 b)))))))

; Every trace of t, after the reversed prefix pre, has a completion satisfying P.
(def-adts $ (CtAllP : (Pred P) ((Ctree) t) ((List (Col)) pre) -> Type)
  enum
  (many CAPE : (erased Pred P) (erased (List (Col)) pre) -> (CtAllP P (CEmpty) pre))
  (many CAPL : (erased Pred P) (erased (Ctree) lf) (erased (List (Col)) pre et ct) (erased (RevApp (Col) pre (Nil (Col)) et) r)
      (erased (Ctr (C0) et ct) c) (erased (Holds P ct) p) -> (CtAllP P (CLeaf lf) pre))
  (many CAPN : (erased Pred P) (erased (Ctree) t1 t2 t3) (erased (List (Col)) pre) (erased (CtAllP P t1 (Cons (Col) (C1) pre)) a1)
      (erased (CtAllP P t2 (Cons (Col) (C2) pre)) a2) (erased (CtAllP P t3 (Cons (Col) (C3) pre)) a3) -> (CtAllP P (CNode t1 t2 t3) pre)))

(def-fns _ $ (erased capp-mem : (erased Pred P) (erased (Ctree) t) (erased (List (Col)) pre full) (subterm erased (List (Col)) et)
    (erased (CtAllP P t pre) a) (erased (CtMem t et) m) (erased (RevApp (Col) pre et full) r) ->
    (erased (List (Col)) ct) (erased (Ctr (C0) full ct) c) (erased (Holds P ct) res))
  (match erased a _
    (absurd (CAPE _ _) (mem-empty et m))
    ((CAPL _ lf _ et2 ct r2 c p) (let-match erased (leaf-mem-nil lf et m) (Refl _ _)) (let-match erased (revapp-fn (Col) pre et full et2 r r2) (Refl _ _))
      (values ct c p))
    ((CAPN _ t1 t2 t3 _ a1 a2 a3)
      (let ((erased e) (erased et1) (erased q) (erased u) (erased s) (erased m1)) (cons-mem t1 t2 t3 t et (CCNode t1 t2 t3) m))
      (let-match erased q (Refl _ _))
      (let ((erased r1)) (RACons (Col) e pre et1 full r))
      (match erased s _
        (absurd (SelN0 _ _ _) (mem-empty et1 m1))
        ((SelN1 _ _ _) (capp-mem P t1 (Cons _ e pre) full et1 a1 m1 r1))
        ((SelN2 _ _ _) (capp-mem P t2 (Cons _ e pre) full et1 a2 m1 r1))
        ((SelN3 _ _ _) (capp-mem P t3 (Cons _ e pre) full et1 a3 m1 r1))))))

(def-fns _ $ (erased mem-length : (erased (Nat) h) (erased (Ctree) t) (subterm erased (List (Col)) et) (erased (CtH h t) k) (erased (CtMem t et) m) ->
    (erased (Length (Col) et h) r))
  (match erased k _
    (absurd (HE _) (mem-empty et m))
    ((HL lf _) (let-match erased (leaf-mem-nil lf et m) (Refl _ _)) (LengthNil _))
    ((HN h1 t1 t2 t3 k1 k2 k3)
      (let ((erased e) (erased et1) (erased q) (erased u) (erased s) (erased m1)) (cons-mem t1 t2 t3 t et (CCNode t1 t2 t3) m))
      (let-match erased q (Refl _ _))
      (LengthCons _ e et1 h1 (mem-length h1 u et1 (sel-h h1 t1 t2 t3 u e k s) m1)))))

(def-fns _ $ (erased monus-pos : (erased (Nat) n k m) (subterm erased (Monus n k (Succ m)) o) -> (erased (Lt (Zero) n) r))
  (match erased o _ ((MoZ _) (LtZ m)) ((MoS n1 _ _ _) (LtZ n1))))

(def-fns _ $ (erased monus-le : (erased (Nat) a b ab n m) (subterm erased (Add a b ab) p) (erased (Lt ab (Succ n)) l) (erased (Monus n a m) o) ->
    (erased (Lt b (Succ m)) r))
  (match erased p _
    ((AddZero _) (let-match erased o (MoZ _)) l)
    ((AddSucc a1 _ ab1 p1)
      (match erased o _
        (absurd (MoE _) (let-match erased l (LtS _ _ l1)) l1)
        ((MoS n1 _ _ o1) (let-match erased l (LtS _ _ l1)) (monus-le a1 b ab1 n1 m p1 l1 o1))))))

(def-fns _ $ (erased mem-sub : (erased (Ctree) t) (erased (List (Col)) et) (erased (Nat) n) (erased (CtMem t et) m) (erased (CtSub t et n) s) ->
    (erased (Nat) n1) (erased (Eq (Nat) n (Succ n1)) e))
  (let-match erased m (MkCtMem _ _ n1 s1))
  (values n1 (sub-fn t et n (Succ n1) s s1)))

(def-fns _ $ (erased mc-zero-mk : (erased (Bstack) bs) (erased (List (Col)) et) -> (erased (MC (GSG (GEmpty)) bs et (Zero)) m))
  (let ((erased n) (erased m)) (mc-exists (GSG (GEmpty)) bs et))
  (let-match erased (mc-zero bs et n m) (Refl _ _))
  m)

; A history of the Kempe closure state (ctu, gtr, gtu), from initial trees satisfying the three certificates above. ctr holds
; traces of the co-closure, of length h + 1.
(def-adts
  ((KV : (Pred P) ((Nat) h) ((Ctree) ctu) ((Gtree) gtr) ((Gtree) gtu) -> Type)
    enum
    (many KVBase : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
        (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
        -> (KV P h ctu (GEmpty) gtu))
    (many KVSplit : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu ctr) (erased (Gtree) gtu hit miss) (erased (KV P h ctu (GEmpty) gtu) kv)
        (erased (CtKC P h ctr) ck) (erased (GPart (GSG gtu) (GSG hit) (GSG miss)) pt)
        (erased (GHit (GSG hit) (Cons RC (MkRx (Ctree) (BS0) ctr) (Nil RC))) hs) -> (KV P h ctu hit miss))
    (many KVRestr : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu keep gone) (erased (Gtree) gtr gtu) (erased (KV P h ctu gtr gtu) kv)
        (erased (CtH (Succ h) ctu) hc) (erased (CtH (Succ h) keep) hk) (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) cr)
        -> (KV P h keep (GEmpty) gtu))
    (many KVEmpty : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr) (erased (KV P h ctu gtr (GEmpty)) kv)
        -> (KV P h (CEmpty) (GEmpty) (GEmpty))))
  ((CtKC : (Pred P) ((Nat) h) ((Ctree) ctr) -> Type)
    enum
    (many CKBase : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctr) (erased (CtAllP P ctr (Nil (Col))) a) -> (CtKC P h ctr))
    (many CKGone : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu keep gone ctr) (erased (Gtree) gtr gtu) (erased (KVWrap P h ctu gtr gtu) kw)
        (erased (CtH (Succ h) ctu) hc) (erased (CtH (Succ h) gone) hg)
        (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) cr) (erased (CtRLR gone gone ctr) rl) -> (CtKC P h ctr)))
  ((KVWrap : (Pred P) ((Nat) h) ((Ctree) ctu) ((Gtree) gtr) ((Gtree) gtu) -> Type)
    enum
    (many MkKVWrap : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (erased (KV P h ctu gtr gtu) kv)
        -> (KVWrap P h ctu gtr gtu))))

(def-fns _ $ (erased rg1-cnt : (erased (Gtree) g) (erased (List (Col)) et) (erased (Nat) a k) (erased (MC (GSG g) (BS0) et a) m)
    (erased (RCnt (Cons RG (MkRx (Gtree) (BS0) g) (Nil RG)) et k) c) -> (erased (Eq (Nat) k a) e))
  (let-match erased c (RCCons _ _ _ _ a2 b2 _ m2 c2 p))
  (let-match erased c2 (RCNil _))
  (let-match erased (mc-fn (GSG g) (BS0) et a a2 m m2) (Refl _ _))
  (add-fn a (Zero) k a p (add-zero-right a)))

(def-fns _ $ (erased kv-even : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (subterm erased (KV P h ctu gtr gtu) kv)
    (erased (List (Col)) et) (erased (CtMem ctu et) m) -> (erased (ERun (ESStart) et (BTrue)) r))
  (match erased kv _
    ((KVBase _ _ _ _ ce _ _) (cev-mem ctu (ESStart) et ce m))
    ((KVSplit _ _ _ _ gtu0 _ _ kv0 _ _ _) (kv-even P h ctu (GEmpty) gtu0 kv0 et m))
    ((KVRestr _ _ ctu0 _ gone gtr0 _ kv0 hc hk cr)
      (let ((erased len)) (mem-length (Succ h) ctu et hk m))
      (let ((erased n) (erased s)) (sub-exists ctu0 et))
      (let ((erased k) (erased c)) (rcnt-exists (Cons RG (MkRx (Gtree) (BS0) gtr0) (Nil RG)) et))
      (let-match erased (cres-sub h ctu0 ctu gone _ et n k cr hc len s c) (MkKeepSub _ _ _ _ m2 o s2))
      (let ((erased m1) (erased q)) (mem-sub ctu et m2 m s2))
      (let-match erased q (Refl _ _))
      (let-match erased (monus-pos n k m1 o) (LtZ n1))
      (kv-even P h ctu0 gtr0 gtu kv0 et (MkCtMem ctu0 et n1 s)))
    (absurd (KVEmpty _ _ _ _ _) (mem-empty et m))))

(def-fns _ $ (erased kv-count : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (subterm erased (KV P h ctu gtr gtu) kv)
    (erased (List (Col)) et) (erased (Nat) n a b) (erased (ERun (ESStart) et (BTrue)) ev) (erased (Length (Col) et (Succ h)) len)
    (erased (CtSub ctu et n) s) (erased (MC (GSG gtr) (BS0) et a) ma) (erased (MC (GSG gtu) (BS0) et b) mb) ->
    (erased (Nat) ab) (erased (Add a b ab) p) (erased (Lt ab (Succ n)) l))
  (match erased kv _
    ((KVBase _ _ _ _ _ ge _)
      (let-match erased (mc-zero (BS0) et a ma) (Refl _ _))
      (let ((erased ps)) (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)))
      (let ((erased pc)) (PCCons (BS0) (GSG gtu) (Nil RS) et b (Zero) b mb (PCNil et) (add-zero-right b)))
      (values b (AddZero b) (ge-cnt ctu ps (ESStart) (Succ h) et n b ge len ev s pc)))
    ((KVSplit _ _ _ _ gtu0 _ _ kv0 _ pt _)
      (let ((erased b0) (erased mb0)) (mc-exists (GSG gtu0) (BS0) et))
      (let ((erased ab0) (erased p0) (erased l0)) (kv-count P h ctu (GEmpty) gtu0 kv0 et n (Zero) b0 ev len s (mc-zero-mk (BS0) et) mb0))
      (let-match erased p0 (AddZero _))
      (values b0 (part-mc (GSG gtu0) (GSG gtr) (GSG gtu) (BS0) et b0 a b pt mb0 ma mb) l0))
    ((KVRestr _ _ ctu0 _ gone gtr0 _ kv0 hc hk cr)
      (let-match erased (mc-zero (BS0) et a ma) (Refl _ _))
      (let ((erased n0) (erased s0)) (sub-exists ctu0 et))
      (let ((erased a0) (erased ma0)) (mc-exists (GSG gtr0) (BS0) et))
      (let ((erased ab0) (erased p0) (erased l0)) (kv-count P h ctu0 gtr0 gtu kv0 et n0 a0 b ev len s0 ma0 mb))
      (let ((erased k) (erased c)) (rcnt-exists (Cons RG (MkRx (Gtree) (BS0) gtr0) (Nil RG)) et))
      (let-match erased (rg1-cnt gtr0 et a0 k ma0 c) (Refl _ _))
      (let-match erased (cres-sub h ctu0 ctu gone _ et n0 k cr hc len s0 c) (MkKeepSub _ _ _ _ m o s2))
      (let-match erased (sub-fn ctu et n m s s2) (Refl _ _))
      (values b (AddZero b) (monus-le a0 b ab0 n0 n p0 l0 o)))
    ((KVEmpty _ _ _ _ _)
      (let-match erased (sub-fn ctu et n (Zero) s (empty-sub et)) (Refl _ _))
      (let-match erased (mc-zero (BS0) et a ma) (Refl _ _))
      (let-match erased (mc-zero (BS0) et b mb) (Refl _ _))
      (values (Zero) (AddZero (Zero)) (LtZ (Zero))))))

(def-fns _ $ (erased rlr-pick : (erased (Ctree) gone ctr) (erased (List (Col)) et) (erased (CtRLR gone gone ctr) rl) (erased (CtMem ctr et) m) ->
    (erased (Perm) g) (erased (IsPerm g) ip) (erased (List (Col)) et2) (erased (PermT g et et2) pt) (erased (CtMem gone et2) m2))
  (match erased (rlr-mem gone gone ctr et rl m) _
    ((InL _ _ pm) (let-match erased pm (MkPermMem _ _ _ et2 pt m2)) (values p312 (IP312) et2 pt m2))
    ((InR _ _ pm) (let-match erased pm (MkPermMem _ _ _ et2 pt m2)) (values p231 (IP231) et2 pt m2))))

(def-fns _
  ((erased kv-closed : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (subterm erased (KV P h ctu gtr gtu) kv)
      (erased (List (Gsym)) w) (erased (InitG (Succ h) w) ig) -> (erased (Or (GMem (GSG gtu) w) (Wit P w)) r))
    (match erased kv _
      ((KVBase _ _ _ _ _ _ gc) (let-match erased ig (MkInitG _ _ l bl)) (InL _ _ (gcov-mem (GSG gtu) (Zero) (Succ h) (BFalse) w gc l bl)))
      ((KVSplit _ _ _ ctr gtu0 _ _ kv0 ck pt hs)
        (match erased (kv-closed P h ctu (GEmpty) gtu0 kv0 w ig) _
          ((InL _ _ g0)
            (match erased (part-mem (GSG gtu0) (GSG gtr) (GSG gtu) w pt g0) _
              ((InL _ _ gh)
                (let-match erased (ghit-mem (GSG gtr) (Cons RC (MkRx (Ctree) (BS0) ctr) (Nil RC)) w hs gh) (MkHits _ _ bs t et el m mt))
                (let-match erased el (ElHere _ _ _) (absurd (ElThere _ _ _ _ el2) el2))
                (InR _ _ (MkWit P w et mt (ck-mem P h ctr ck et m))))
              ((InR _ _ gm) (InL _ _ gm))))
          ((InR _ _ wt) (InR _ _ wt))))
      ((KVRestr _ _ ctu0 _ _ gtr0 _ kv0 _ _ _) (kv-closed P h ctu0 gtr0 gtu kv0 w ig))
      ((KVEmpty _ _ ctu0 gtr0 kv0)
        (match erased (kv-closed P h ctu0 gtr0 (GEmpty) kv0 w ig) _
          (absurd (InL _ _ g0) (gmem-empty w g0))
          ((InR _ _ wt) (InR _ _ wt))))))
  ((erased ck-mem : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctr) (subterm erased (CtKC P h ctr) ck) (erased (List (Col)) et)
      (erased (CtMem ctr et) m) -> (erased (KC P et) r))
    (match erased ck _
      ((CKBase _ _ _ a) (let ((erased ct) (erased c) (erased p)) (capp-mem P ctr (Nil _) et et a m (RANil (Col) et))) (KIn P et ct c p))
      ((CKGone _ _ ctu keep gone _ gtr gtu kw hc hg cr rl)
        (let ((erased g) (erased ip) (erased et2) (erased pt) (erased m2)) (rlr-pick gone ctr et rl m))
        (let-match erased kw (MkKVWrap _ _ _ _ _ kv0))
        (let ((erased len)) (mem-length (Succ h) gone et2 hg m2))
        (let-match erased (cres-gone h ctu keep gone _ et2 cr len m2) (MkGone _ _ _ mc s0))
        (let ((erased ev)) (kv-even P h ctu gtr gtu kv0 et2 mc))
        (let ((erased n) (erased s)) (sub-exists ctu et2))
        (let ((erased a) (erased ma)) (mc-exists (GSG gtr) (BS0) et2))
        (let ((erased b) (erased mb)) (mc-exists (GSG gtu) (BS0) et2))
        (let ((erased ab) (erased p) (erased l)) (kv-count P h ctu gtr gtu kv0 et2 n a b ev len s ma mb))
        (let ((erased k) (erased c)) (rcnt-exists (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) et2))
        (let-match erased (rg1-cnt gtr et2 a k ma c) (Refl _ _))
        (let-match erased (cres-sub h ctu keep gone _ et2 n k cr hc len s c) (MkKeepSub _ _ _ _ m0 o s1))
        (let-match erased (sub-fn keep et2 m0 (Zero) s1 s0) (Refl _ _))
        (let-match erased (monus-le a b ab n (Zero) p l o) (LtZ _) (absurd (LtS _ _ l1) l1))
        (KPerm P et et2 g ip pt
          (KGram P et2 (am-build P h ctu gtr gtu kw et2 et2 len mb (Nil _) (Nil _) (BS0) (Zero) (BFalse) (MPreNil (BS0)) (GPreNil (Zero) (BFalse))
            (RANil (Col) et2)))))))
  ((erased am-build : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (subterm erased (KVWrap P h ctu gtr gtu) kw)
      (subterm erased (List (Col)) et) (erased (List (Col)) full) (erased (Length (Col) full (Succ h)) len) (erased (MC (GSG gtu) (BS0) full (Zero)) mz)
      (erased (List (Col)) etc) (erased (List (Gsym)) pre) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b)
      (erased (MPre (BS0) etc pre bs) mp) (erased (GPre (Zero) (BFalse) pre d b) gp) (erased (RevApp (Col) etc et full) ra) ->
      (erased (AM P bs d b et pre) r))
    (let-match erased kw (MkKVWrap _ _ _ _ _ kv0))
    (match erased et _
      ((Nil _)
        (match erased (end-dec d b) _
          ((InR _ _ eb) (AMEndBad P bs d b pre eb))
          ((InL _ _ g)
            (let ((erased w) (erased rw)) (revapp-exists (Gsym) pre (Nil _)))
            (let ((erased mt)) (mpre-app (BS0) bs etc (Nil _) full pre (Nil _) w mp (MPNil bs) ra rw))
            (let ((erased ig)) (MkInitG (Succ h) w (matchpg-length (BS0) full w (Succ h) mt len) (gpre-app (Zero) d (BFalse) b pre (Nil _) w gp g rw)))
            (match erased (kv-closed P h ctu gtr gtu kv0 w ig) _
              (absurd (InL _ _ gm) (mc-pos (GSG gtu) (BS0) full w (Zero) gm mt mz))
              ((InR _ _ wt) (AMEndOk P bs d b pre w g rw wt))))))
      ((Cons _ e et1)
        (let ((erased ra1)) (RACons (Col) e etc et1 full ra))
        (match erased (col-kind e bs) _
          ((K0 _) (AM0 P bs d b et1 pre))
          ((K1 _)
            (let ((erased c) (erased n)) (not-exists b))
            (AM1 P bs d b c et1 pre n
              (am-build P h ctu gtr gtu kw et1 full len mz (Cons _ e etc) (Cons _ (GSkip) pre) bs d c
                (MPreCons (BS0) bs bs etc pre e (GSkip) mp (SSkip bs)) (GPreCons (Zero) d d (BFalse) b c pre (GSkip) gp (GStSkip d b c n)) ra1)))
          ((K23 _ _ bs1 y po)
            (AM23 P bs bs1 d b e et1 pre y
              (am-build P h ctu gtr gtu kw et1 full len mz (Cons _ e etc) (Cons _ (GPush) pre) bs1 (Succ d) b
                (MPreCons (BS0) bs bs1 etc pre e (GPush) mp y) (GPreCons (Zero) d (Succ d) (BFalse) b b pre (GPush) gp (GStPush d b)) ra1)
              (match erased po _
                ((PNone _) (APNone P d b e et1 pre))
                ((PSome _ b0 _ s pp z)
                  (match erased d _
                    ((Zero) (APZero P bs b e et1 pre))
                    ((Succ d1)
                      (match erased s _
                        ((GPop0)
                          (APSome P bs b0 d1 b b s e et1 pre pp z (PPar0 b)
                            (am-build P h ctu gtr gtu kw et1 full len mz (Cons _ e etc) (Cons _ s pre) b0 d1 b
                              (MPreCons (BS0) bs b0 etc pre e s mp z) (GPreCons (Zero) d d1 (BFalse) b b pre s gp (GStPop0 d1 b)) ra1)))
                        ((GPop1)
                          (let ((erased c) (erased n)) (not-exists b))
                          (APSome P bs b0 d1 b c s e et1 pre pp z (PPar1 b c n)
                            (am-build P h ctu gtr gtu kw et1 full len mz (Cons _ e etc) (Cons _ s pre) b0 d1 c
                              (MPreCons (BS0) bs b0 etc pre e s mp z) (GPreCons (Zero) d d1 (BFalse) b c pre s gp (GStPop1 d1 b c n)) ra1)))
                        (absurd (GPush) (match erased z _ (absurd (SPush2 _) pp) (absurd (SPush3 _) pp)))
                        (absurd (GSkip) (let-match erased z (SSkip _)) pp)))))))))))))

(def-fns _ $ (erased kempe-sound : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (erased (KV P h ctu gtr gtu) kv)
    (erased (List (Col)) et) (erased (ERun (ESStart) et (BTrue)) ev) (erased (Length (Col) et (Succ h)) len) (erased (CtSub ctu et (Zero)) s) ->
    (erased (KC P et) r))
  (let ((erased a) (erased ma)) (mc-exists (GSG gtr) (BS0) et))
  (let ((erased b) (erased mb)) (mc-exists (GSG gtu) (BS0) et))
  (let ((erased ab) (erased p) (erased l)) (kv-count P h ctu gtr gtu kv et (Zero) a b ev len s ma mb))
  (let-match erased l (LtZ _) (absurd (LtS _ _ l1) l1))
  (let-match erased p (AddZero _))
  (KGram P et (am-build P h ctu gtr gtu (MkKVWrap P h ctu gtr gtu kv) et et len mb (Nil _) (Nil _) (BS0) (Zero) (BFalse) (MPreNil (BS0))
    (GPreNil (Zero) (BFalse)) (RANil (Col) et))))

; The states (ctu, gtr, gtu) the closure loop below reaches from c0, r0 and g0, and the traces it removes on the way, as KV and
; CtKC record them but without the predicate.
(def-adts
  ((KR : ((Nat) h) ((Ctree) c0 r0) ((Gtree) g0) ((Ctree) ctu) ((Gtree) gtr gtu) -> Type)
    enum
    (many KRBase : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) -> (KR h c0 r0 g0 c0 (GEmpty) g0))
    (many KRSplit : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (Ctree) ctu ctr) (erased (Gtree) gtu hit miss)
        (erased (KR h c0 r0 g0 ctu (GEmpty) gtu) kr) (erased (CR h c0 r0 g0 ctr) cr) (erased (GPart (GSG gtu) (GSG hit) (GSG miss)) pt)
        (erased (GHit (GSG hit) (Cons RC (MkRx (Ctree) (BS0) ctr) (Nil RC))) hs) -> (KR h c0 r0 g0 ctu hit miss))
    (many KRRestr : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (Ctree) ctu keep gone) (erased (Gtree) gtr gtu)
        (erased (KR h c0 r0 g0 ctu gtr gtu) kr) (erased (CtH (Succ h) ctu) hc) (erased (CtH (Succ h) keep) hk)
        (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) cres) -> (KR h c0 r0 g0 keep (GEmpty) gtu))
    (many KREmpty : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (Ctree) ctu) (erased (Gtree) gtr)
        (erased (KR h c0 r0 g0 ctu gtr (GEmpty)) kr) -> (KR h c0 r0 g0 (CEmpty) (GEmpty) (GEmpty))))
  ((CR : ((Nat) h) ((Ctree) c0 r0) ((Gtree) g0) ((Ctree) ctr) -> Type)
    enum
    (many CRBase : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) -> (CR h c0 r0 g0 r0))
    (many CRGone : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (Ctree) ctu keep gone ctr) (erased (Gtree) gtr gtu)
        (erased (KR h c0 r0 g0 ctu gtr gtu) kr) (erased (CtH (Succ h) ctu) hc) (erased (CtH (Succ h) gone) hg)
        (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) cres) (erased (CtRLR gone gone ctr) rl) -> (CR h c0 r0 g0 ctr))))

(def-fns _
  ((erased kr-kv : (erased Pred P) (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (KV P h c0 (GEmpty) g0) kv0)
      (erased (CtKC P h r0) ck0) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (subterm erased (KR h c0 r0 g0 ctu gtr gtu) kr)
      -> (erased (KV P h ctu gtr gtu) r))
    (match erased kr _
      ((KRBase _ _ _ _) kv0)
      ((KRSplit _ _ _ _ _ ctr gtu1 _ _ kr1 cr pt hs)
        (KVSplit P h ctu ctr gtu1 gtr gtu (kr-kv P h c0 r0 g0 kv0 ck0 ctu (GEmpty) gtu1 kr1) (cr-ck P h c0 r0 g0 kv0 ck0 ctr cr) pt hs))
      ((KRRestr _ _ _ _ ctu1 _ gone gtr1 _ kr1 hc hk cres)
        (KVRestr P h ctu1 ctu gone gtr1 gtu (kr-kv P h c0 r0 g0 kv0 ck0 ctu1 gtr1 gtu kr1) hc hk cres))
      ((KREmpty _ _ _ _ ctu1 gtr1 kr1) (KVEmpty P h ctu1 gtr1 (kr-kv P h c0 r0 g0 kv0 ck0 ctu1 gtr1 (GEmpty) kr1)))))
  ((erased cr-ck : (erased Pred P) (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (KV P h c0 (GEmpty) g0) kv0)
      (erased (CtKC P h r0) ck0) (erased (Ctree) ctr) (subterm erased (CR h c0 r0 g0 ctr) cr) -> (erased (CtKC P h ctr) r))
    (match erased cr _
      ((CRBase _ _ _ _) ck0)
      ((CRGone _ _ _ _ ctu keep gone _ gtr gtu kr hc hg cres rl)
        (CKGone P h ctu keep gone ctr gtr gtu (MkKVWrap P h ctu gtr gtu (kr-kv P h c0 r0 g0 kv0 ck0 ctu gtr gtu kr)) hc hg cres rl)))))

(def-adts $ (KrC : ((Nat) h) ((Ctree) c0 r0) ((Gtree) g0) -> Type)
  enum
  (many KDoneC : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (unique (UTree) u) (erased (Ctree) ctu) (many (KeepE ctu) e)
      (many (Gtree) gtr) (unique (UGtree) gu) (erased (Gtree) gtu) (many (GKeep gtu) ge) (erased (KR h c0 r0 g0 ctu gtr gtu) kr)
      (erased (UT h u ctu) ut) (erased (UG gu gtu) ug) -> (KrC h c0 r0 g0))
  (many KGoC : (erased (Nat) h) (erased (Ctree) c0 r0) (erased (Gtree) g0) (unique (UTree) u) (erased (Ctree) ctu) (many (KeepE ctu) e)
      (many (Ctree) ctr) (unique (UGtree) gu) (erased (Gtree) gtu) (many (GKeep gtu) ge) (erased (KR h c0 r0 g0 ctu (GEmpty) gtu) kr)
      (erased (CR h c0 r0 g0 ctr) cr) (erased (UT h u ctu) ut) (erased (UG gu gtu) ug) -> (KrC h c0 r0 g0)))

(def-fns _ $ (many ktc-step-c : (erased (Ctree) c0 r0) (erased (Gtree) g0) (many (Nat) h) (unique (UTree) u) (erased (Ctree) ctu) (many (KeepE ctu) e)
    (many (Gtree) gtr) (unique (UGtree) gu) (erased (Gtree) gtu) (many (GKeep gtu) ge) (erased (KR h c0 r0 g0 ctu gtr gtu) kr) (erased (UT h u ctu) ut)
    (erased (UG gu gtu) ug) -> (unique (KrC h c0 r0 g0) k))
  (let-match many e (KLive _) ((KEmpty) (KDoneC h c0 r0 g0 u ctu e gtr gu gtu ge kr ut ug)))
  (let-match many gtr (GEmpty) (else
    (let-match many ge (GKLive _) ((GKEmpty)
      (KDoneC h c0 r0 g0 (UEmpty) (CEmpty) (KEmpty) (GEmpty) (UGEmpty) (GEmpty) (GKEmpty) (KREmpty h c0 r0 g0 ctu gtr kr) (UTE h) (UGE))))
    (let ((unique ku) (many gone) (erased keep) (erased uk) (erased cres) (erased hg) (many e2))
      (ctree-restrict-u h u ctu ut (Cons _ (MkRx _ (BS0) gtr) $ Nil _) (RxCons _ (BS0) gtr _ (RxNil _))))
    (let ((many ctr) (erased rl) (erased _)) (ctree-union-rotlr (Succ h) gone gone hg hg))
    (let ((erased hc) (erased hk)) (values (ut-h h u ctu ut) (ut-h h ku keep uk)))
    (KGoC h c0 r0 g0 ku keep (k-drop keep _ _ e2) ctr gu gtu ge (KRRestr h c0 r0 g0 ctu keep gone gtr gtu kr hc hk cres)
      (CRGone h c0 r0 g0 ctu keep gone ctr gtr gtu kr hc hg cres rl) uk ug)))
  (KDoneC h c0 r0 g0 u ctu e gtr gu gtu ge kr ut ug))

(def-fns _ $ (many ktc-u : (erased (Ctree) c0 r0) (erased (Gtree) g0) (subterm many (Nat) d) (many (Nat) h) (unique (UTree) u) (erased (Ctree) ctu)
    (many (KeepE ctu) e) (many (Ctree) ctr) (unique (UGtree) gu) (erased (Gtree) gtu) (many (GKeep gtu) ge) (erased (KR h c0 r0 g0 ctu (GEmpty) gtu) kr)
    (erased (CR h c0 r0 g0 ctr) cr) (erased (UT h u ctu) ut) (erased (UG gu gtu) ug) ->
    (unique (UTree) u2) (erased (Ctree) ctu2) (many (KeepE ctu2) e2) (many (Gtree) gtr2) (unique (UGtree) gu2) (erased (Gtree) gtu2)
    (many (GKeep gtu2) ge2) (erased (KR h c0 r0 g0 ctu2 gtr2 gtu2) kr2) (erased (UT h u2 ctu2) ut2) (erased (UG gu2 gtu2) ug2))
  (let-match many d (Succ d1)
    ((Zero)
      (let ((many hit) (unique mu) (erased miss) (erased um) (erased pt) (erased hs) (many me))
        (gtree-restrict-u gu gtu ug (Cons _ (MkRx _ (BS0) ctr) $ Nil _) (RxCons _ (BS0) ctr _ (RxNil _))))
      (values u ctu e hit mu miss (gk-drop miss _ _ me) (KRSplit h c0 r0 g0 ctu ctr gtu hit miss kr cr pt hs) ut um)))
  (let ((unique u1) (erased c1) (many e1) (many g1) (unique gu1) (erased v1) (many ge1) (erased kr1) (erased ut1) (erased ug1))
    (notail $ ktc-u c0 r0 g0 d1 h u ctu e ctr gu gtu ge kr cr ut ug))
  (let ((unique (UTree) u2) (erased (Ctree) c2) (many (KeepE c2) e2) (many (Gtree) g2) (unique (UGtree) gu2) (erased (Gtree) v2) (many (GKeep v2) ge2)
      (erased (KR h c0 r0 g0 c2 g2 v2) kr2) (erased (UT h u2 c2) ut2) (erased (UG gu2 v2) ug2))
    (match unique (ktc-step-c c0 r0 g0 h u1 c1 e1 g1 gu1 v1 ge1 kr1 ut1 ug1) _
      ((KDoneC _ _ _ _ a ca ea b gb vb eb k ua ub) (values a ca ea b gb vb eb k ua ub))
      ((KGoC _ _ _ _ a ca ea b gb vb eb k cr2 ua ub) (notail $ ktc-u c0 r0 g0 d1 h a ca ea b gb vb eb k cr2 ua ub))))
  (match unique (ktc-step-c c0 r0 g0 h u2 c2 e2 g2 gu2 v2 ge2 kr2 ut2 ug2) _
    ((KDoneC _ _ _ _ a ca ea b gb vb eb k ua ub) (values a ca ea b gb vb eb k ua ub))
    ((KGoC _ _ _ _ a ca ea b gb vb eb k cr2 ua ub) (tail $ ktc-u c0 r0 g0 d1 h a ca ea b gb vb eb k cr2 ua ub))))

(def-fns _ $ (many ktc-run : (erased (Ctree) c0 r0) (erased (Gtree) g0) (many (Nat) d) (many (Nat) h) (many (Ctree) ctu ctr) (many (Gtree) gtu)
    (erased (KR h c0 r0 g0 ctu (GEmpty) gtu) kr) (erased (CR h c0 r0 g0 ctr) cr) (erased (CtH (Succ h) ctu) hc) ->
    (many (Ctree) ctu2) (many (Gtree) gtr2) (unique (UGtree) gu2) (erased (Gtree) gtu2) (erased (UG gu2 gtu2) ug2)
    (erased (KR h c0 r0 g0 ctu2 gtr2 gtu2) kr2) (erased (CtH (Succ h) ctu2) hc2))
  (let ((unique u) (erased ut) (many e)) (ut-of h ctu hc))
  (let ((unique gu) (erased ug) (many ge)) (ug-of gtu))
  (let ((unique u2) (erased c2) (many _) (many g2) (unique gu2) (erased v2) (many _) (erased kr2) (erased ut2) (erased ug2))
    (ktc-u c0 r0 g0 d h u ctu e ctr gu gtu ge kr cr ut ug))
  (values (ct-of h u2 c2 ut2) g2 gu2 v2 ug2 kr2 (ut-h h u2 c2 ut2)))

(def-fns _ $ (many ktc-c : (erased (Ctree) c0 r0) (erased (Gtree) g0) (many (Nat) d) (many (Nat) h) (many (Ctree) ctu ctr) (many (Gtree) gtu)
    (erased (KR h c0 r0 g0 ctu (GEmpty) gtu) kr) (erased (CR h c0 r0 g0 ctr) cr) (erased (CtH (Succ h) ctu) hc) ->
    (many (Ctree) ctu2) (many (Gtree) gtr2 gtu2) (erased (KR h c0 r0 g0 ctu2 gtr2 gtu2) kr2) (erased (CtH (Succ h) ctu2) hc2))
  (let ((many c2) (many g2) (unique gu2) (erased v2) (erased ug2) (erased kr2) (erased hc2)) (ktc-run c0 r0 g0 d h ctu ctr gtu kr cr hc))
  (values c2 g2 (gt-of gu2 v2 ug2) kr2 hc2))

(def-adts $ (KSound : (Pred P) ((Nat) h) ((Ctree) ct) -> Type)
  enum
  (many MkKSound : (erased Pred P) (erased (Nat) h) (erased (Ctree) ct) (erased (Gtree) gtr gtu) (erased (KV P h ct gtr gtu) kv)
      -> (KSound P h ct)))

(def-fns _ $ (many kempe-tree-c : (erased Pred P) (many (Nat) h) (many (Ctree) ctu ctr) (many (Gtree) gtu)
    (erased (CEv ctu (ESStart)) ce) (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge)
    (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc) (erased (CtAllP P ctr (Nil (Col))) ca) (erased (CtH (Succ h) ctu) hc) ->
    (many (Ctree) ct) (erased (KSound P h ct) ks))
  (let ((many ct) (erased gtr) (unique _) (erased gtu2) (erased _) (erased kr) (erased _))
    (ktc-run ctu ctr gtu (Succ $ Succ h) h ctu ctr gtu (KRBase h ctu ctr gtu) (CRBase h ctu ctr gtu) hc))
  (values ct (MkKSound P h ct gtr gtu2 (kr-kv P h ctu ctr gtu (KVBase P h ctu gtu ce ge gc) (CKBase P h ctr ca) ct gtr gtu2 kr))))

(def-adts $ (FlipPair : ((Perm) g) ((Perm) g2) -> Type)
  enum
  (many FP123 : -> (FlipPair p123 p123))
  (many FP312 : -> (FlipPair p312 p231))
  (many FP231 : -> (FlipPair p231 p312)))

(def-fns _ $ (erased flip-c : (erased (Perm) g g2) (erased (Col) c d c2 d2) (erased (FlipPair g g2) fp) (erased (PermC g c d) p)
    (erased (PermC p132 c c2) q) (erased (PermC g2 c2 d2) r) -> (erased (PermC p132 d d2) res))
  (match erased fp _
    ((FP123) (match erased p _
      ((PC0 _) (let-match erased q (PC0 _)) (let-match erased r (PC0 _)) (PC0 p132))
      ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (let-match erased r (PC1 _ _ _)) (PC1 (C1) (C3) (C2)))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (let-match erased r (PC3 _ _ _)) (PC2 (C1) (C3) (C2)))
      ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (let-match erased r (PC2 _ _ _)) (PC3 (C1) (C3) (C2)))))
    ((FP312) (match erased p _
      ((PC0 _) (let-match erased q (PC0 _)) (let-match erased r (PC0 _)) (PC0 p132))
      ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (let-match erased r (PC1 _ _ _)) (PC3 (C1) (C3) (C2)))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (let-match erased r (PC3 _ _ _)) (PC1 (C1) (C3) (C2)))
      ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (let-match erased r (PC2 _ _ _)) (PC2 (C1) (C3) (C2)))))
    ((FP231) (match erased p _
      ((PC0 _) (let-match erased q (PC0 _)) (let-match erased r (PC0 _)) (PC0 p132))
      ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (let-match erased r (PC1 _ _ _)) (PC2 (C1) (C3) (C2)))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (let-match erased r (PC3 _ _ _)) (PC3 (C1) (C3) (C2)))
      ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (let-match erased r (PC2 _ _ _)) (PC1 (C1) (C3) (C2)))))))

(def-fns _ $ (erased permc-total : (erased (Perm) g) (erased (Col) c) -> (erased (Col) d) (erased (PermC g c d) p))
  (let-match erased g (MkPerm p1 p2 p3))
  (match erased c _ ((C0) (values c (PC0 g))) ((C1) (values p1 (PC1 p1 p2 p3))) ((C2) (values p2 (PC2 p1 p2 p3))) ((C3) (values p3 (PC3 p1 p2 p3)))))

(def-fns _ $ (erased flip-run : (erased (Perm) g g2) (erased (List (Col)) l l2) (erased (FlipPair g g2) fp) (subterm erased (PermT p132 l l2) pt)
    (erased (ERun (ESTail g) l (BFalse)) run) -> (erased (ERun (ESTail g2) l2 (BTrue)) r))
  (match erased pt _
    (absurd (PTNil _) (let-match erased run (ERNil _ _ e)) e)
    ((PTCons _ c c2 l1 l3 q pt1)
      (let-match erased run (ERCons _ st _ _ _ stp run1))
      (let ((erased d2) (erased r2)) (permc-total g2 c2))
      (match erased stp _
        ((EStT0 _ _ p)
          (let-match erased (flip-c g g2 c (C0) c2 d2 fp p q r2) (PC0 _))
          (ERCons (ESTail g2) (ESTail g2) c2 l3 (BTrue) (EStT0 g2 c2 r2) (flip-run g g2 l1 l3 fp pt1 run1)))
        ((EStT1 _ _ p)
          (let-match erased (flip-c g g2 c (C1) c2 d2 fp p q r2) (PC1 _ _ _))
          (ERCons (ESTail g2) (ESTail g2) c2 l3 (BTrue) (EStT1 g2 c2 r2) (flip-run g g2 l1 l3 fp pt1 run1)))
        (absurd (EStT2 _ _ p) (erun-fn (ESEven) l1 (BTrue) (BFalse) (run-even l1) run1))
        ((EStT3 _ _ p)
          (let-match erased (flip-c g g2 c (C3) c2 d2 fp p q r2) (PC3 _ _ _))
          (ERCons (ESTail g2) (ESEven) c2 l3 (BTrue) (EStT2 g2 c2 r2) (run-even l3)))))))

(def-fns _ $ (erased etrace-run : (erased (List (Col)) et et2) (erased (ETrace et et2) e) -> (erased (ERun (ESStart) et2 (BTrue)) r))
  (match erased e _
    ((ETrEven _ p) (even-run et (BTrue) p))
    ((ETrOdd _ _ p pt)
      (let ((erased run)) (even-run et (BFalse) p))
      (let-match erased pt (PTCons _ c c2 l l2 q pt1) (absurd (PTNil _) (let-match erased run (ERNil _ _ x)) x))
      (let-match erased run (ERCons _ st _ _ _ stp run1))
      (match erased stp _
        (absurd (EStS0) (erun-fn (ESEven) l (BTrue) (BFalse) (run-even l) run1))
        ((EStS1) (let-match erased q (PC1 _ _ _)) (ERCons (ESStart) (ESTail p123) c2 l2 (BTrue) (EStS1) (flip-run p123 p123 l l2 (FP123) pt1 run1)))
        ((EStS2) (let-match erased q (PC2 _ _ _)) (ERCons (ESStart) (ESTail p231) c2 l2 (BTrue) (EStS3) (flip-run p312 p231 l l2 (FP312) pt1 run1)))
        ((EStS3) (let-match erased q (PC3 _ _ _)) (ERCons (ESStart) (ESTail p312) c2 l2 (BTrue) (EStS2) (flip-run p231 p312 l l2 (FP231) pt1 run1)))))))

(def-fns _ $ (erased permt-length : (erased (Perm) g) (erased (List (Col)) et et2) (erased (Nat) n) (subterm erased (PermT g et et2) p)
    (erased (Length (Col) et n) l) -> (erased (Length (Col) et2 n) r))
  (match erased p _
    ((PTNil _) l)
    ((PTCons _ c d et1 et3 _ p1) (let-match erased l (LengthCons _ _ _ n1 l1)) (LengthCons _ d et3 n1 (permt-length g et1 et3 n1 p1 l1)))))

(def-fns _ $ (erased kempe-treeP : (erased Pred P) (erased (Nat) h) (erased (Ctree) kt) (erased (KSound P h kt) ks)
    (erased (List (Col)) et et2) (erased (Length (Col) et (Succ h)) len) (erased (ETrace et et2) e) (erased (CtSub kt et2 (Zero)) s) ->
    (erased (KC P et) r))
  (let-match erased ks (MkKSound _ _ _ gtr gtu kv))
  (match erased e _
    ((ETrEven _ _) (kempe-sound P h kt gtr gtu kv et (etrace-run et et2 e) len s))
    ((ETrOdd _ _ _ pt)
      (KPerm P et et2 p132 (IP132) pt
        (kempe-sound P h kt gtr gtu kv et2 (etrace-run et et2 e) (permt-length p132 et et2 (Succ h) pt len) s)))))
