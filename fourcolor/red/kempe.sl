(let ((erased Pred)) (TyCtor ((List (Col)) et) -> Type))

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

; The Kempe co-closure of P (Kempe_coclosure of chromogram.v), as the least set of partial traces holding P, holding
; each trace that a colour permutation sends into it, and holding each trace all of whose balanced matching
; chromograms are matched by a trace in it. AM P bs d b et pre: every chromogram w matching et from the stack bs, whose
; completion from d open chords and parity b is balanced, has its whole chromogram (the reverse of pre, then w)
; matched by a trace of the set.
(def-adts
  ((KC : (Pred P) ((List (Col)) et) -> Type)
    enum
    (many KIn : (erased Pred P) (erased (List (Col)) et) (erased (P et) p) -> (KC P et))
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

; A matching, balanced chromogram has its witness.
(def-fns _ $ (erased am-sound : (erased Pred P) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b) (erased (List (Col)) et)
    (erased (List (Gsym)) pre w full) (subterm erased (MatchPG bs et w) mt) (erased (AM P bs d b et pre) a) (erased (GBal d b w) g)
    (erased (RevApp (Gsym) pre w full) ra) -> (erased (Wit P full) r))
  (match erased mt _
    ((MPNil _)
      (match erased a _
        ((AMEndOk _ _ _ _ _ w2 _ ra2 wt) (let-match erased (revapp-fn (Gsym) pre w full w2 ra ra2) (Refl _ _)) wt)
        (absurd (AMEndBad _ _ _ _ _ eb) (endbad-bal d b eb g))))
    ((MPCons _ bs2 e s et1 w1 y mt1)
      (let ((erased ra1)) (RACons (Gsym) s pre w1 full ra))
      (match erased (sym-cls s bs bs2 e y) _
        ((SCSkip _)
          (let-match erased a (AM1 _ _ _ _ c _ _ n a1) (absurd (AM23 _ _ _ _ _ _ _ _ y1 _ _) y1))
          (let-match erased g (GBSkip _ _ c2 _ n2 g1))
          (let-match erased (not-fn b c c2 n n2) (Refl _ _))
          (am-sound P bs d c et1 (Cons _ (GSkip) pre) w1 full mt1 a1 g1 ra1))
        ((SCPush _ _ _ _)
          (let-match erased a (AM23 _ _ bs1 _ _ _ _ _ y1 a1 _) (absurd (AM0 _ _ _ _ _ _) y) (absurd (AM1 _ _ _ _ _ _ _ _ _) y))
          (let-match erased (sym-fn (GPush) bs bs2 bs1 e y y1) (Refl _ _))
          (let-match erased g (GBPush _ _ _ g1))
          (am-sound P bs2 (Succ d) b et1 (Cons _ (GPush) pre) w1 full mt1 a1 g1 ra1))
        ((SCPop _ _ _ _ pp _)
          (let-match erased a (AM23 _ _ bs1 _ _ _ _ _ y1 _ ap) (absurd (AM0 _ _ _ _ _ _) y) (absurd (AM1 _ _ _ _ _ _ _ _ _) (let-match erased y (SSkip _)) pp))
          (match erased ap _
            (absurd (APNone _ _ _ _ _ _) pp)
            (absurd (APZero _ _ _ _ _ _)
              (match erased g _
                (absurd (GBSkip _ _ _ _ _ _) (let-match erased y (SSkip _)) pp)
                (absurd (GBPush _ _ _ _) (match erased y _ (absurd (SPush2 _) pp) (absurd (SPush3 _) pp)))))
            ((APSome _ _ b0 d1 _ c t _ _ _ pp2 z par a1)
              (let-match erased (popped-fn bs bs2 b0 pp pp2) (Refl _ _))
              (let-match erased (pop-fn s t bs bs2 e pp y z) (Refl _ _))
              (match erased par _
                ((PPar0 _) (let-match erased g (GBPop0 _ _ _ g1)) (am-sound P bs2 d1 b et1 (Cons _ s pre) w1 full mt1 a1 g1 ra1))
                ((PPar1 _ _ n)
                  (let-match erased g (GBPop1 _ _ c2 _ n2 g1))
                  (let-match erased (not-fn b c c2 n n2) (Refl _ _))
                  (am-sound P bs2 d1 c et1 (Cons _ s pre) w1 full mt1 a1 g1 ra1))))))))))

; even_trace of color.v as an automaton over the trace.
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

; For every even trace et, read from the evenness state st, the multiplicity of et in t bounds the matches of ps.
(def-adts
  ((GE : ((Ctree) t) ((List RS) ps) ((ES) st) -> Type)
    enum
    (many GEDead : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (erased (PZero ps) z) -> (GE t ps st))
    (many GEOdd : (erased (Ctree) t) (erased (List RS) ps) -> (GE t ps (ESOdd)))
    (many GES : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (erased (Nat) n k) (erased (CtRoot t n) rt) (erased (PCnt ps (Nil (Col)) k) pk)
        (erased (Lt k (Succ n)) le) (erased (GEAt t ps st (C0)) a0) (erased (GEAt t ps st (C1)) a1) (erased (GEAt t ps st (C2)) a2)
        (erased (GEAt t ps st (C3)) a3) -> (GE t ps st)))
  ((GEAt : ((Ctree) t) ((List RS) ps) ((ES) st) ((Col) e) -> Type)
    enum
    (many MkGEAt : (erased (Ctree) t u) (erased (List RS) ps ps2) (erased (ES) st st2) (erased (Col) e) (erased (CtSel t e u) s)
        (erased (PSplitE e (Nil RS) ps ps2) sp) (erased (ESStep st e st2) p) (erased (GE u ps2 st2) g) -> (GEAt t ps st e))))

(def-fns _ $ (erased ge-cnt : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (subterm erased (List (Col)) et) (erased (Nat) n k)
    (erased (GE t ps st) g) (erased (ERun st et (BTrue)) run) (erased (CtSub t et n) s) (erased (PCnt ps et k) c) -> (erased (Lt k (Succ n)) r))
  (match erased g _
    ((GEDead _ _ _ z) (let-match erased (pzero-cnt ps et k z c) (Refl _ _)) (LtZ n))
    (absurd (GEOdd _ _) (erun-fn (ESOdd) et (BFalse) (BTrue) (run-odd et) run))
    ((GES _ _ _ n0 k0 rt pk le a0 a1 a2 a3)
      (match erased et _
        ((Nil _)
          (let-match erased s (SubNil _ _ rt2))
          (let-match erased (root-fn t n n0 rt2 rt) (Refl _ _))
          (let-match erased (pcnt-fn ps et k k0 c pk) (Refl _ _))
          le)
        ((Cons _ e et1)
          (let-match erased (match erased e (((GEAt t ps st e) q)) ((C0) a0) ((C1) a1) ((C2) a2) ((C3) a3)) (MkGEAt _ u _ ps2 _ st2 _ sl sp p g1))
          (let-match erased run (ERCons _ st3 _ _ _ p3 run1))
          (let-match erased (esstep-fn st st2 st3 e p p3) (Refl _ _))
          (let ((erased k2) (erased c2)) (pcnt-exists ps2 et1))
          (let-match erased (add-fn k (Zero) k2 k (psplit-cnt e (Nil RS) ps ps2 et1 (Zero) k k2 sp (PCNil et1) c2 c) (add-zero-right k)) (Refl _ _))
          (ge-cnt u ps2 st2 et1 n k g1 run1 (sub-sel t u e et1 n s sl) c2))))))

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

; Every trace of t, after the reversed prefix pre, satisfies P.
(def-adts $ (CtAllP : (Pred P) ((Ctree) t) ((List (Col)) pre) -> Type)
  enum
  (many CAPE : (erased Pred P) (erased (List (Col)) pre) -> (CtAllP P (CEmpty) pre))
  (many CAPL : (erased Pred P) (erased (Ctree) lf) (erased (List (Col)) pre et) (erased (RevApp (Col) pre (Nil (Col)) et) r) (erased (P et) p)
      -> (CtAllP P (CLeaf lf) pre))
  (many CAPN : (erased Pred P) (erased (Ctree) t1 t2 t3) (erased (List (Col)) pre) (erased (CtAllP P t1 (Cons (Col) (C1) pre)) a1)
      (erased (CtAllP P t2 (Cons (Col) (C2) pre)) a2) (erased (CtAllP P t3 (Cons (Col) (C3) pre)) a3) -> (CtAllP P (CNode t1 t2 t3) pre)))

(def-fns _ $ (erased capp-mem : (erased Pred P) (erased (Ctree) t) (erased (List (Col)) pre full) (subterm erased (List (Col)) et)
    (erased (CtAllP P t pre) a) (erased (CtMem t et) m) (erased (RevApp (Col) pre et full) r) -> (erased (P full) res))
  (match erased a _
    (absurd (CAPE _ _) (mem-empty et m))
    ((CAPL _ lf _ et2 r2 p) (let-match erased (leaf-mem-nil lf et m) (Refl _ _)) (let-match erased (revapp-fn (Col) pre et full et2 r r2) (Refl _ _)) p)
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

; From a + b <= n, b <= n - a.
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

; Kempe_valid of kempetree.v, for soundness only: a history of the Kempe_tree_closure state (ctu, gtr, gtu), from
; initial trees satisfying the three certificates above. ctr holds traces of the co-closure, of length h + 1.
(def-adts
  ((KV : (Pred P) ((Nat) h) ((Ctree) ctu) ((Gtree) gtr) ((Gtree) gtu) -> Type)
    enum
    (many KVBase : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
        (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
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

; Kempe_valid's multiplicities: for an even trace, the matches in gtr and gtu are bounded by the multiplicity in ctu.
(def-fns _ $ (erased kv-count : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (subterm erased (KV P h ctu gtr gtu) kv)
    (erased (List (Col)) et) (erased (Nat) n a b) (erased (ERun (ESStart) et (BTrue)) ev) (erased (Length (Col) et (Succ h)) len)
    (erased (CtSub ctu et n) s) (erased (MC (GSG gtr) (BS0) et a) ma) (erased (MC (GSG gtu) (BS0) et b) mb) ->
    (erased (Nat) ab) (erased (Add a b ab) p) (erased (Lt ab (Succ n)) l))
  (match erased kv _
    ((KVBase _ _ _ _ _ ge _)
      (let-match erased (mc-zero (BS0) et a ma) (Refl _ _))
      (let ((erased ps)) (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)))
      (let ((erased pc)) (PCCons (BS0) (GSG gtu) (Nil RS) et b (Zero) b mb (PCNil et) (add-zero-right b)))
      (values b (AddZero b) (ge-cnt ctu ps (ESStart) et n b ge ev s pc)))
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
  ; The chromograms of the initial gtree have either stayed in gtu or been witnessed by a co-closure trace.
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
  ; Every trace of ctr is in the co-closure.
  ((erased ck-mem : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctr) (subterm erased (CtKC P h ctr) ck) (erased (List (Col)) et)
      (erased (CtMem ctr et) m) -> (erased (KC P et) r))
    (match erased ck _
      ((CKBase _ _ _ a) (KIn P et (capp-mem P ctr (Nil _) et et a m (RANil (Col) et))))
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
  ; With no chromogram of gtu matching full, every balanced chromogram matching full has a witness.
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

; Soundness of the Kempe tree state: an even trace of length h + 1 absent from ctu is in the co-closure of P.
(def-fns _ $ (erased kempe-sound : (erased Pred P) (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (erased (KV P h ctu gtr gtu) kv)
    (erased (List (Col)) et) (erased (EvenT et (BTrue)) ev) (erased (Length (Col) et (Succ h)) len) (erased (CtSub ctu et (Zero)) s) ->
    (erased (KC P et) r))
  (let ((erased a) (erased ma)) (mc-exists (GSG gtr) (BS0) et))
  (let ((erased b) (erased mb)) (mc-exists (GSG gtu) (BS0) et))
  (let ((erased ab) (erased p) (erased l)) (kv-count P h ctu gtr gtu kv et (Zero) a b (even-run et (BTrue) ev) len s ma mb))
  (let-match erased l (LtZ _) (absurd (LtS _ _ l1) l1))
  (let-match erased p (AddZero _))
  (KGram P et (am-build P h ctu gtr gtu (MkKVWrap P h ctu gtr gtu kv) et et len mb (Nil _) (Nil _) (BS0) (Zero) (BFalse) (MPreNil (BS0))
    (GPreNil (Zero) (BFalse)) (RANil (Col) et))))

(def-adts $ (KrC : (Pred P) ((Nat) h) -> Type)
  enum
  (many KDoneC : (erased Pred P) (erased (Nat) h) (many (Ctree) ctu) (many (Gtree) gtr gtu) (erased (KV P h ctu gtr gtu) kv)
      (erased (CtH (Succ h) ctu) hc) -> (KrC P h))
  (many KGoC : (erased Pred P) (erased (Nat) h) (many (Ctree) ctu ctr) (many (Gtree) gtu) (erased (KV P h ctu (GEmpty) gtu) kv)
      (erased (CtKC P h ctr) ck) (erased (CtH (Succ h) ctu) hc) -> (KrC P h)))

; ktc_step of kempetree.v.
(def-fns _ $ (many ktc-step-c : (erased Pred P) (many (Nat) h) (many (Ctree) ctu) (many (Gtree) gtr gtu) (erased (KV P h ctu gtr gtu) kv)
    (erased (CtH (Succ h) ctu) hc) -> (many (KrC P h) k))
  (let-match many ctu (CEmpty) (else
    (let-match many gtr (GEmpty) (else
      (let-match many gtu (GEmpty) (else
        (let ((erased r)) (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)))
        (let ((many keep) (many gone) (erased cr) (erased hk) (erased hg)) (ctree-restrict-c h ctu (Cons _ (MkRx _ (BS0) gtr) $ Nil _) hc))
        (let ((many ctr) (erased rl) (erased _)) (ctree-union-rotlr (Succ h) gone gone hg hg))
        (KGoC P h keep ctr gtu (KVRestr P h ctu keep gone gtr gtu kv hc hk cr)
          (CKGone P h ctu keep gone ctr gtr gtu (MkKVWrap P h ctu gtr gtu kv) hc hg cr rl) hk)))
      (KDoneC P h (CEmpty) (GEmpty) (GEmpty) (KVEmpty P h ctu gtr kv) (HE (Succ h)))))
    (KDoneC P h ctu gtr gtu kv hc)))
  (KDoneC P h ctu gtr gtu kv hc))

; Kempe_tree_closure of kempetree.v.
(def-fns _ $ (many ktc-c : (erased Pred P) (subterm many (Nat) d) (many (Nat) h) (many (Ctree) ctu ctr) (many (Gtree) gtu)
    (erased (KV P h ctu (GEmpty) gtu) kv) (erased (CtKC P h ctr) ck) (erased (CtH (Succ h) ctu) hc) ->
    (many (Ctree) ctu2) (many (Gtree) gtr2 gtu2) (erased (KV P h ctu2 gtr2 gtu2) kv2) (erased (CtH (Succ h) ctu2) hc2))
  (let-match many d (Succ d1)
    ((Zero)
      (let ((many hit) (many miss) (erased pt) (erased hs)) (gtree-restrict-c gtu (Cons _ (MkRx _ (BS0) ctr) $ Nil _)))
      (values ctu hit miss (KVSplit P h ctu ctr gtu hit miss kv ck pt hs) hc)))
  (let ((many c1) (many g1) (many u1) (erased kv1) (erased hc1)) (notail $ ktc-c P d1 h ctu ctr gtu kv ck hc))
  (let ((many (Ctree) c2) (many (Gtree) g2) (many (Gtree) u2) (erased (KV P h c2 g2 u2) kv2) (erased (CtH (Succ h) c2) hc2))
    (match many (ktc-step-c P h c1 g1 u1 kv1 hc1) _
      ((KDoneC _ _ a b c k hk) (values a b c k hk))
      ((KGoC _ _ a b c k ck2 hk) (notail $ ktc-c P d1 h a b c k ck2 hk))))
  (match many (ktc-step-c P h c2 g2 u2 kv2 hc2) _
    ((KDoneC _ _ a b c k hk) (values a b c k hk))
    ((KGoC _ _ a b c k ck2 hk) (tail $ ktc-c P d1 h a b c k ck2 hk))))

(def-adts $ (KSound : (Pred P) ((Nat) h) ((Ctree) ct) -> Type)
  enum
  (many MkKSound : (erased Pred P) (erased (Nat) h) (erased (Ctree) ct) (erased (Gtree) gtr gtu) (erased (KV P h ct gtr gtu) kv)
      -> (KSound P h ct)))

; Kempe_tree of kempetree.v, from initial trees ctu and gtu carrying the base certificates and from ctr, whose traces satisfy P.
(def-fns _ $ (many kempe-tree-c : (erased Pred P) (many (Nat) h) (many (Ctree) ctu ctr) (many (Gtree) gtu)
    (erased (CEv ctu (ESStart)) ce) (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart)) ge)
    (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc) (erased (CtAllP P ctr (Nil (Col))) ca) (erased (CtH (Succ h) ctu) hc) ->
    (many (Ctree) ct) (erased (KSound P h ct) ks))
  (let ((many ct) (many gtr) (many gtu2) (erased kv) (erased _))
    (ktc-c P (Succ $ Succ h) h ctu ctr gtu (KVBase P h ctu gtu ce ge gc) (CKBase P h ctr ca) hc))
  (values ct (MkKSound P h ct gtr gtu2 kv)))

; The meaning of the Kempe tree, with the contract test: an even trace of a ctree disjoint from it is in the co-closure.
(def-fns _ $ (erased kempe-tree-sound : (erased Pred P) (erased (Nat) h) (erased (Ctree) kt ct) (erased (KSound P h kt) ks)
    (erased (CtDisj kt ct) dj) (erased (List (Col)) et) (erased (CtMem ct et) m) (erased (EvenT et (BTrue)) ev)
    (erased (Length (Col) et (Succ h)) len) -> (erased (KC P et) r))
  (let-match erased ks (MkKSound _ _ _ gtr gtu kv))
  (let ((erased n) (erased s)) (sub-exists kt et))
  (match erased n _
    ((Zero) (kempe-sound P h kt gtr gtu kv et ev len s))
    (absurd (Succ n1) (disj-mem kt ct et dj (MkCtMem kt et n1 s) m))))
