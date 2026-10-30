; A certified cpcolor: every trace of the tree it computes is a ring trace of a colouring of the configuration's map
; (the soundness half of ctree_mem_cpcolor of cfcolor.v). Load after cfcolor.sl and red/kempe.sl.

; Every trace of t, after the reversed prefix pre, is a ring trace of cp's map with its first entry dropped.
(def-adts $ (CtRing : ((List (Step)) cp) ((Ctree) t) ((List (Col)) pre) -> Type)
  enum
  (many CRE : (erased (List (Step)) cp) (erased (List (Col)) pre) -> (CtRing cp (CEmpty) pre))
  (many CRL : (erased (List (Step)) cp) (erased (Ctree) lf) (erased (List (Col)) pre et) (erased (Col) e0) (erased (RevApp (Col) pre (Nil (Col)) et) r)
      (erased (CpCol cp (Cons (Col) e0 et)) c) -> (CtRing cp (CLeaf lf) pre))
  (many CRN : (erased (List (Step)) cp) (erased (Ctree) t1 t2 t3) (erased (List (Col)) pre) (erased (CtRing cp t1 (Cons (Col) (C1) pre)) r1)
      (erased (CtRing cp t2 (Cons (Col) (C2) pre)) r2) (erased (CtRing cp t3 (Cons (Col) (C3) pre)) r3) -> (CtRing cp (CNode t1 t2 t3) pre)))

(def-fns _ $ (erased ctring-cons : (erased (List (Step)) cp) (erased (Ctree) t1 t2 t3 t) (erased (List (Col)) pre) (erased (CtCons t1 t2 t3 t) c)
    (erased (CtRing cp t1 (Cons (Col) (C1) pre)) r1) (erased (CtRing cp t2 (Cons (Col) (C2) pre)) r2) (erased (CtRing cp t3 (Cons (Col) (C3) pre)) r3)
    -> (erased (CtRing cp t pre) r))
  (match erased c _ ((CCEmpty) (CRE cp pre)) ((CCNode _ _ _) (CRN cp t1 t2 t3 pre r1 r2 r3))))

(def-fns _ $ (erased ctring-or : (erased (List (Step)) cp) (erased (Ctree) tl tr t) (erased (List (Col)) pre) (subterm erased (CtOr tl tr t) o)
    (erased (CtRing cp tl pre) rl) (erased (CtRing cp tr pre) rr) -> (erased (CtRing cp t pre) r))
  (match erased o _
    ((OrEL _) rr)
    ((OrER _) rl)
    ((OrLL a b) (let-match erased rl (CRL _ _ _ et e0 ra c)) (CRL cp (CEmpty) pre et e0 ra c))
    ((OrNN l1 l2 l3 r1 r2 r3 u1 u2 u3 _ o1 o2 o3 c)
      (let-match erased rl (CRN _ _ _ _ _ a1 a2 a3))
      (let-match erased rr (CRN _ _ _ _ _ b1 b2 b3))
      (ctring-cons cp u1 u2 u3 t pre c (ctring-or cp l1 r1 u1 (Cons (Col) (C1) pre) o1 a1 b1) (ctring-or cp l2 r2 u2 (Cons (Col) (C2) pre) o2 a2 b2)
        (ctring-or cp l3 r3 u3 (Cons (Col) (C3) pre) o3 a3 b3)))))

(def-fns _ $ (erased permt-invert : (erased (Perm) g g2) (erased (List (Col)) et et2) (erased (PermInv g g2) pi) (subterm erased (PermT g et et2) p)
    -> (erased (PermT g2 et2 et) r))
  (let-match erased p (PTCons _ c d et1 et3 pc p1) ((PTNil _) (PTNil g2)))
  (PTCons g2 d c et3 et1 (permc-invert g g2 c d pi pc) (permt-invert g g2 et1 et3 pi p1)))

(def-fns _ $ (erased permt-revapp : (erased (Perm) g) (erased (List (Col)) pre w r pre2 w2 r2) (subterm erased (RevApp (Col) pre w r) a)
    (erased (RevApp (Col) pre2 w2 r2) b) (erased (PermT g pre2 pre) pp) (erased (PermT g w2 w) pw) -> (erased (PermT g r2 r) res))
  (let-match erased a (RACons _ s pre1 _ _ a1) ((RANil _ _) (let-match erased pp (PTNil _)) (let-match erased b (RANil _ _)) pw))
  (let-match erased pp (PTCons _ s2 _ pre3 _ ps pp1))
  (let-match erased b (RACons _ _ _ _ _ b1))
  (permt-revapp g pre1 (Cons (Col) s w) r pre3 (Cons (Col) s2 w2) r2 a1 b1 pp1 (PTCons g s2 s w2 w ps pw)))

(def-fns _ $ (erased ctring-sel : (erased (List (Step)) cp) (erased (Ctree) t1 t2 t3 u) (erased (Col) c) (erased (List (Col)) pre)
    (erased (CtSel (CNode t1 t2 t3) c u) s) (erased (CtRing cp (CNode t1 t2 t3) pre) r) -> (erased (CtRing cp u (Cons (Col) c pre)) res))
  (let-match erased r (CRN _ _ _ _ _ r1 r2 r3))
  (match erased s _ ((SelN0 _ _ _) (CRE cp _)) ((SelN1 _ _ _) r1) ((SelN2 _ _ _) r2) ((SelN3 _ _ _) r3)))

; The traces of a permuted tree t2 are those whose image under g is a trace of t.
(def-fns _ $ (erased ctring-perm : (erased (List (Step)) cp) (erased (Perm) g gi) (erased (Ctree) t t2) (erased (List (Col)) pre pre2) (subterm erased (CtPerm g t t2) p)
    (erased (CtRing cp t pre) r) (erased (PermT g pre2 pre) pp) (erased (PermInv g gi) pi) (erased (IsPerm gi) ip) -> (erased (CtRing cp t2 pre2) res))
  (match erased p _
    ((CPE _) (CRE cp pre2))
    ((CPL _ lf)
      (let-match erased r (CRL _ _ _ et e0 ra c))
      (let ((erased et2) (erased ra2)) (revapp-exists (Col) pre2 (Nil (Col))))
      (let ((erased pet)) (permt-revapp g pre (Nil (Col)) et pre2 (Nil (Col)) et2 ra ra2 pp (PTNil g)))
      (let ((erased e2) (erased pe)) (permc-ex gi e0 ip))
      (CRL cp lf pre2 et2 e2 ra2 (cpcol-perm cp (Cons (Col) e0 et) (Cons (Col) e2 et2) gi c ip (PTCons gi e0 e2 et et2 pe (permt-invert g gi et2 et pi pet)))))
    ((CPN g1 g2 g3 w1 w2 w3 u1 u2 u3 a1 a2 a3 _ s1 s2 s3 p1 p2 p3 c)
      (ctring-cons cp a1 a2 a3 t2 pre2 c
        (ctring-perm cp g gi u1 a1 (Cons (Col) g1 pre) (Cons (Col) (C1) pre2) p1 (ctring-sel cp w1 w2 w3 u1 g1 pre s1 r)
          (PTCons g (C1) g1 pre2 pre (PC1 g1 g2 g3) pp) pi ip)
        (ctring-perm cp g gi u2 a2 (Cons (Col) g2 pre) (Cons (Col) (C2) pre2) p2 (ctring-sel cp w1 w2 w3 u2 g2 pre s2 r)
          (PTCons g (C2) g2 pre2 pre (PC2 g1 g2 g3) pp) pi ip)
        (ctring-perm cp g gi u3 a3 (Cons (Col) g3 pre) (Cons (Col) (C3) pre2) p3 (ctring-sel cp w1 w2 w3 u3 g3 pre s3 r)
          (PTCons g (C3) g3 pre2 pre (PC3 g1 g2 g3) pp) pi ip)))))

(def-fns _ $ (many permc-r : (many (Perm) g) (many (Col) c) -> (many (Col) d) (erased (PermC g c d) p))
  (let-match many g (MkPerm p1 p2 p3))
  (match many c _ ((C0) (values c (PC0 g))) ((C1) (values p1 (PC1 p1 p2 p3))) ((C2) (values p2 (PC2 p1 p2 p3))) ((C3) (values p3 (PC3 p1 p2 p3)))))

; t2 has t below colour c (Gonthier's ctree_cons_e).
(def-fns _ $ (many ct-cons-e-c : (erased (List (Step)) cp) (erased (List (Col)) pre) (erased (Nat) h) (many (Col) c) (many (Ctree) t) (erased (CtH h t) ht)
    (erased (CtRing cp t (Cons (Col) c pre)) rt) -> (many (Ctree) t2) (erased (CtH (Succ h) t2) ht2) (erased (CtRing cp t2 pre) rt2))
  (let ((erased e) (erased he) (erased re2) (erased re3)) (values (CEmpty) (HE h) (CRE cp (Cons (Col) (C2) pre)) (CRE cp (Cons (Col) (C3) pre))))
  (match many c _
    ((C0) (values (CEmpty) (HE (Succ h)) (CRE cp pre)))
    ((C1) (let ((many t2) (erased cc)) (ctree-cons t (CEmpty) (CEmpty)))
      (values t2 (cons-h h t e e t2 cc ht he he) (ctring-cons cp t e e t2 pre cc rt re2 re3)))
    ((C2) (let ((many t2) (erased cc)) (ctree-cons (CEmpty) t (CEmpty)))
      (values t2 (cons-h h e t e t2 cc he ht he) (ctring-cons cp e t e t2 pre cc (CRE cp (Cons (Col) (C1) pre)) rt re3)))
    ((C3) (let ((many t2) (erased cc)) (ctree-cons (CEmpty) (CEmpty) t))
      (values t2 (cons-h h e e t t2 cc he he ht) (ctring-cons cp e e t t2 pre cc (CRE cp (Cons (Col) (C1) pre)) re2 rt)))))

(let ((many simple-leaf-c)) (CLeaf (CEmpty)))

; The tree of the one trace et under g, after the reversed prefix pre (cfcbr2 of cfcolor.v), given that trace is good.
(def-fns _ $ (many cfcbr2-c : (erased (List (Step)) cp) (erased (List (Col)) pre get full) (erased (Col) e0) (many (Perm) g) (subterm many (List (Col)) et)
    (erased (PermT g et get) pt) (erased (RevApp (Col) pre get full) ra) (erased (CpCol cp (Cons (Col) e0 full)) cc)
    -> (many (Ctree) t) (erased (Nat) h) (erased (Length (Col) et h) l) (erased (CtH h t) ht) (erased (CtRing cp t pre) rt))
  (let-match many et (Cons _ e rest)
    ((Nil _) (let-match erased pt (PTNil _)) (values simple-leaf-c (Zero) (LengthNil _) (HL (CEmpty) (HE (Zero))) (CRL cp (CEmpty) pre full e0 ra cc))))
  (let-match erased pt (PTCons _ _ c _ grest pc pt1))
  (let ((many c2) (erased pc2)) (permc-r g e))
  (let-match erased (permc-fn g e c c2 pc pc2) (Refl _ _))
  (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1)) (notail $ cfcbr2-c cp (Cons (Col) c pre) grest full e0 g rest pt1 (RACons (Col) c pre grest full ra) cc))
  (let ((many t) (erased ht) (erased rt)) (ct-cons-e-c cp pre h1 c2 t1 ht1 rt1))
  (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt))

(def-fns _ $ (erased p132-of : (erased (Col) p1 p2 p3 q1 q2 q3) (erased (IsPerm (MkPerm p1 p2 p3)) ip) (erased (PermC p132 p1 q1) c1)
    (erased (PermC p132 p2 q2) c2) (erased (PermC p132 p3 q3) c3) -> (erased (P132Comp (MkPerm p1 p2 p3) (MkPerm q1 q2 q3)) pk)
    (erased (IsPerm (MkPerm q1 q2 q3)) iq))
  (match erased ip _
    ((IP123) (let-match erased c1 (PC1 _ _ _)) (let-match erased c2 (PC2 _ _ _)) (let-match erased c3 (PC3 _ _ _)) (values (PK123) (IP132)))
    ((IP132) (let-match erased c1 (PC1 _ _ _)) (let-match erased c2 (PC3 _ _ _)) (let-match erased c3 (PC2 _ _ _)) (values (PK132) (IP123)))
    ((IP213) (let-match erased c1 (PC2 _ _ _)) (let-match erased c2 (PC1 _ _ _)) (let-match erased c3 (PC3 _ _ _)) (values (PK213) (IP312)))
    ((IP231) (let-match erased c1 (PC2 _ _ _)) (let-match erased c2 (PC3 _ _ _)) (let-match erased c3 (PC1 _ _ _)) (values (PK231) (IP321)))
    ((IP312) (let-match erased c1 (PC3 _ _ _)) (let-match erased c2 (PC1 _ _ _)) (let-match erased c3 (PC2 _ _ _)) (values (PK312) (IP213)))
    ((IP321) (let-match erased c1 (PC3 _ _ _)) (let-match erased c2 (PC2 _ _ _)) (let-match erased c3 (PC1 _ _ _)) (values (PK321) (IP231)))))

(def-adts $ (AllC1 : ((List (Col)) pre) -> Type)
  enum
  (many AC1Nil : -> (AllC1 (Nil (Col))))
  (many AC1Cons : (erased (List (Col)) pre) (erased (AllC1 pre) p) -> (AllC1 (Cons (Col) (C1) pre))))

(def-fns _ $ (erased permt-ex : (erased (Perm) g) (subterm erased (List (Col)) et) (erased (IsPerm g) ip) -> (erased (List (Col)) et2) (erased (PermT g et et2) p))
  (let-match erased et (Cons _ c rest) ((Nil _) (values (Nil (Col)) (PTNil g))))
  (let ((erased d) (erased pc)) (permc-ex g c ip))
  (let ((erased rest2) (erased p1)) (permt-ex g rest ip))
  (values (Cons (Col) d rest2) (PTCons g c d rest rest2 pc p1)))

(def-fns _ $ (erased permt-p132 : (erased (Perm) g h) (erased (List (Col)) et get hget) (erased (P132Comp g h) pk) (subterm erased (PermT g et get) p)
    (erased (PermT p132 get hget) q) -> (erased (PermT h et hget) r))
  (let-match erased p (PTCons _ c d et1 get1 pc p1) ((PTNil _) (let-match erased q (PTNil _)) (PTNil h)))
  (let-match erased q (PTCons _ _ e _ hget1 qc q1))
  (PTCons h c e et1 hget1 (permc-p132 g h c d e pk pc qc) (permt-p132 g h et1 get1 hget1 pk p1 q1)))

(def-fns _ $ (erased permt-c1 : (subterm erased (List (Col)) pre) (erased (AllC1 pre) a) -> (erased (PermT p132 pre pre) r))
  (let-match erased a (AC1Cons pre1 a1) ((AC1Nil) (PTNil p132)))
  (PTCons p132 (C1) (C1) pre1 pre1 (PC1 (C1) (C3) (C2)) (permt-c1 pre1 a1)))

; The tree of the one trace et normalised so that its first entry other than C1 under g is C2, after the reversed prefix
; pre of C1 entries (cfcbr1 of cfcolor.v), given that the trace under g is good.
(def-fns _ $ (many cfcbr1-c : (erased (List (Step)) cp) (erased (List (Col)) pre get full) (erased (Col) e0) (many (Perm) g) (subterm many (List (Col)) et)
    (erased (PermT g et get) pt) (erased (RevApp (Col) pre get full) ra) (erased (CpCol cp (Cons (Col) e0 full)) cc) (erased (IsPerm g) ip)
    (erased (AllC1 pre) a1) -> (many (Ctree) t) (erased (Nat) h) (erased (Length (Col) et h) l) (erased (CtH h t) ht) (erased (CtRing cp t pre) rt))
  (let-match many et (Cons _ e rest)
    ((Nil _) (let-match erased pt (PTNil _)) (values simple-leaf-c (Zero) (LengthNil _) (HL (CEmpty) (HE (Zero))) (CRL cp (CEmpty) pre full e0 ra cc))))
  (let-match erased pt (PTCons _ _ c _ grest pc pt1))
  (let ((many c2) (erased pc2)) (permc-r g e))
  (let-match erased (permc-fn g e c c2 pc pc2) (Refl _ _))
  (let ((erased ra1)) (RACons (Col) c pre grest full ra))
  (match many c2 _
    ((C0) (let ((erased h1) (erased l1)) (length-exists _ rest)) (values (CEmpty) (Succ h1) (LengthCons _ e rest h1 l1) (HE (Succ h1)) (CRE cp pre)))
    ((C1)
      (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1)) (notail $ cfcbr1-c cp (Cons (Col) c pre) grest full e0 g rest pt1 ra1 cc ip (AC1Cons pre a1)))
      (let ((many t) (erased ht) (erased rt)) (ct-cons-e-c cp pre h1 c2 t1 ht1 rt1))
      (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt))
    ((C2)
      (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1)) (cfcbr2-c cp (Cons (Col) c pre) grest full e0 g rest pt1 ra1 cc))
      (let ((many t) (erased ht) (erased rt)) (ct-cons-e-c cp pre h1 c2 t1 ht1 rt1))
      (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt))
    ((C3)
      (let-match many g (MkPerm g1 g2 g3))
      (let ((many q1) (erased c1)) (permc-r p132 g1))
      (let ((many q2) (erased c2p)) (permc-r p132 g2))
      (let ((many q3) (erased c3)) (permc-r p132 g3))
      (let ((erased pk) (erased iq)) (p132-of g1 g2 g3 q1 q2 q3 ip c1 c2p c3))
      (let ((many hp)) (MkPerm q1 q2 q3))
      (let ((erased hrest) (erased ph)) (permt-ex p132 grest (IP132)))
      (let ((erased full2) (erased ra2)) (revapp-exists (Col) pre (Cons (Col) (C2) hrest)))
      (let ((erased pf)) (permt-revapp p132 pre (Cons (Col) (C2) hrest) full2 pre (Cons (Col) (C3) grest) full ra2 ra (permt-c1 pre a1)
        (PTCons p132 (C3) (C2) grest hrest (PC3 (C1) (C3) (C2)) ph)))
      (let ((erased e02) (erased pe)) (permc-ex p132 e0 (IP132)))
      (let ((erased cc2)) (cpcol-perm cp (Cons (Col) e0 full) (Cons (Col) e02 full2) p132 cc (IP132) (PTCons p132 e0 e02 full full2 pe pf)))
      (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1)) (cfcbr2-c cp (Cons (Col) (C2) pre) hrest full2 e02 hp rest
        (permt-p132 g hp rest grest hrest pk pt1 ph) (RACons (Col) (C2) pre hrest full2 ra2) cc2))
      (let ((many t) (erased ht) (erased rt)) (ct-cons-e-c cp pre h1 (C2) t1 ht1 rt1))
      (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt))))

(def-fns _ $ (many edge-rot-c : (many (Col) e) (erased (NZ e) nz) -> (many (Perm) g) (erased (IsPerm g) ip) (erased (PermC g e (C1)) p))
  (match many e _
    ((C1) (values p123 (IP123) (PC1 (C1) (C2) (C3))))
    ((C2) (values p312 (IP312) (PC2 (C3) (C1) (C2))))
    ((C3) (values p231 (IP231) (PC3 (C2) (C3) (C1))))
    (absurd (C0) nz)))

; The tree of the even normal form of a ring trace with its first two entries dropped, below C1 (cpbranch of cfcolor.v).
(def-fns _ $ (many cpbranch-c : (erased (List (Step)) cp) (erased (Nat) h) (many (List (Col)) et) (erased (CpCol cp et) cc)
    (erased (Length (Col) et (Succ (Succ h))) l) -> (many (Ctree) t) (erased (CtH h t) ht) (erased (CtRing cp t (Cons (Col) (C1) (Nil (Col)))) rt))
  (let ((erased nzs)) (cpcol-nz cp et cc))
  (let-match many et (Cons _ e0 r1) (absurd (Nil _) l))
  (let-match many r1 (Cons _ e1 rest) (absurd (Nil _) (let-match erased l (LengthCons _ _ _ _ l1)) l1))
  (let-match erased nzs (AllNZCons _ _ _ nzs1))
  (let-match erased nzs1 (AllNZCons _ _ nz1 _))
  (let ((many g) (erased ip) (erased pg)) (edge-rot-c e1 nz1))
  (let ((erased grest) (erased pt)) (permt-ex g rest ip))
  (let ((erased e02) (erased pe)) (permc-ex g e0 ip))
  (let ((erased full)) (Cons (Col) (C1) grest))
  (let ((erased cc2)) (cpcol-perm cp et (Cons (Col) e02 full) g cc ip (PTCons g e0 e02 r1 full pe (PTCons g e1 (C1) rest grest pg pt))))
  (let ((many t) (erased h1) (erased l1) (erased ht) (erased rt))
    (cfcbr1-c cp (Cons (Col) (C1) (Nil (Col))) grest full e02 g rest pt (RACons (Col) (C1) (Nil (Col)) grest full (RANil (Col) full)) cc2 ip
      (AC1Cons (Nil (Col)) (AC1Nil))))
  (let-match erased l (LengthCons _ _ _ _ l2))
  (let-match erased l2 (LengthCons _ _ _ _ l3))
  (let-match erased (length-fn _ rest h h1 l3 l1) (Refl _ _))
  (values t ht rt))
