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
    ((OrLL _ _) (let-match erased rl (CRL _ _ _ et e0 ra c)) (CRL cp (CEmpty) pre et e0 ra c))
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

(def-fns _ $ (erased ctring-perm : (erased (List (Step)) cp) (erased (Perm) g gi) (erased (Ctree) t t2) (erased (List (Col)) pre pre2) (subterm erased (CtPerm g t t2) p)
    (erased (CtRing cp t pre) r) (erased (PermT g pre2 pre) pp) (erased (PermInv g gi) pi) (erased (IsPerm gi) ip) -> (erased (CtRing cp t2 pre2) res))
  (let-match erased p (CPL _ lf)
    ((CPE _) (CRE cp pre2))
    ((CPN g1 g2 g3 w1 w2 w3 u1 u2 u3 a1 a2 a3 _ s1 s2 s3 p1 p2 p3 c)
      (ctring-cons cp a1 a2 a3 t2 pre2 c
        (ctring-perm cp g gi u1 a1 (Cons (Col) g1 pre) (Cons (Col) (C1) pre2) p1 (ctring-sel cp w1 w2 w3 u1 g1 pre s1 r)
          (PTCons g (C1) g1 pre2 pre (PC1 g1 g2 g3) pp) pi ip)
        (ctring-perm cp g gi u2 a2 (Cons (Col) g2 pre) (Cons (Col) (C2) pre2) p2 (ctring-sel cp w1 w2 w3 u2 g2 pre s2 r)
          (PTCons g (C2) g2 pre2 pre (PC2 g1 g2 g3) pp) pi ip)
        (ctring-perm cp g gi u3 a3 (Cons (Col) g3 pre) (Cons (Col) (C3) pre2) p3 (ctring-sel cp w1 w2 w3 u3 g3 pre s3 r)
          (PTCons g (C3) g3 pre2 pre (PC3 g1 g2 g3) pp) pi ip))))
  (let-match erased r (CRL _ _ _ et e0 ra c))
  (let ((erased et2) (erased ra2)) (revapp-exists (Col) pre2 (Nil (Col))))
  (let ((erased pet)) (permt-revapp g pre (Nil (Col)) et pre2 (Nil (Col)) et2 ra ra2 pp (PTNil g)))
  (let ((erased e2) (erased pe)) (permc-ex gi e0 ip))
  (CRL cp lf pre2 et2 e2 ra2 (cpcol-perm cp (Cons (Col) e0 et) (Cons (Col) e2 et2) gi c ip (PTCons gi e0 e2 et et2 pe (permt-invert g gi et2 et pi pet)))))

(def-fns _ $ (many permc-r : (many (Perm) g) (many (Col) c) -> (many (Col) d) (erased (PermC g c d) p))
  (let-match many g (MkPerm p1 p2 p3))
  (match many c _ ((C0) (values c (PC0 g))) ((C1) (values p1 (PC1 p1 p2 p3))) ((C2) (values p2 (PC2 p1 p2 p3))) ((C3) (values p3 (PC3 p1 p2 p3)))))

; l has a C0 entry.
(def-adts $ (HasC0 : ((List (Col)) l) -> Type)
  enum
  (many HZHere : (erased (List (Col)) l) -> (HasC0 (Cons (Col) (C0) l)))
  (many HZThere : (erased (Col) c) (erased (List (Col)) l) (erased (HasC0 l) p) -> (HasC0 (Cons (Col) c l))))

; p is l with Color2 and Color3 swapped when Color3 comes first.
(def-adts $ (ENrm : ((List (Col)) l p) -> Type)
  enum
  (many NrEven : (erased (List (Col)) l) (erased (EvenTail l (BTrue)) e) -> (ENrm l l))
  (many NrOdd : (erased (List (Col)) l p) (erased (EvenTail l (BFalse)) e) (erased (PermT p132 l p) q) -> (ENrm l p)))

; t holds the normalisation of l, unless l has a C0 entry.
(def-adts $ (NMem : ((Ctree) t) ((List (Col)) l) -> Type)
  enum
  (many NMZ : (erased (Ctree) t) (erased (List (Col)) l) (erased (HasC0 l) z) -> (NMem t l))
  (many NMIn : (erased (Ctree) t) (erased (List (Col)) l p) (erased (ENrm l p) n) (erased (CtMem t p) m) -> (NMem t l)))

(def-fns _ $ (erased zmem-cons : (erased (Col) c) (erased (Ctree) u t) (erased (List (Col)) l) (erased (Or (Eq (Col) c (C0)) (CtSel t c u)) sl)
    (erased (Or (HasC0 l) (CtMem u l)) zm) -> (erased (Or (HasC0 (Cons (Col) c l)) (CtMem t (Cons (Col) c l))) r))
  (match erased sl _
    ((InL _ _ q) (let-match erased q (Refl _ _)) (InL _ _ (HZHere l)))
    ((InR _ _ s) (match erased zm _ ((InL _ _ z) (InL _ _ (HZThere c l z))) ((InR _ _ m) (InR _ _ (mem-cons t u c l s m)))))))

(def-fns _ $ (many ct-cons-e-c : (erased (List (Step)) cp) (erased (List (Col)) pre) (erased (Nat) h) (many (Col) c) (many (Ctree) t) (erased (CtH h t) ht)
    (erased (CtRing cp t (Cons (Col) c pre)) rt) -> (many (Ctree) t2) (erased (CtH (Succ h) t2) ht2) (erased (CtRing cp t2 pre) rt2)
    (erased (Or (Eq (Col) c (C0)) (CtSel t2 c t)) sl))
  (let ((erased e) (erased he) (erased re2) (erased re3)) (values (CEmpty) (HE h) (CRE cp (Cons (Col) (C2) pre)) (CRE cp (Cons (Col) (C3) pre))))
  (match many c _
    ((C0) (values (CEmpty) (HE (Succ h)) (CRE cp pre) (InL _ _ (Refl _ c))))
    ((C1) (let ((many t2) (erased cc)) (ctree-cons t (CEmpty) (CEmpty)))
      (values t2 (cons-h h t e e t2 cc ht he he) (ctring-cons cp t e e t2 pre cc rt re2 re3) (InR _ _ (cons-sel-back t e e t2 t c cc (SelN1 t e e)))))
    ((C2) (let ((many t2) (erased cc)) (ctree-cons (CEmpty) t (CEmpty)))
      (values t2 (cons-h h e t e t2 cc he ht he) (ctring-cons cp e t e t2 pre cc (CRE cp (Cons (Col) (C1) pre)) rt re3)
        (InR _ _ (cons-sel-back e t e t2 t c cc (SelN2 e t e)))))
    ((C3) (let ((many t2) (erased cc)) (ctree-cons (CEmpty) (CEmpty) t))
      (values t2 (cons-h h e e t t2 cc he he ht) (ctring-cons cp e e t t2 pre cc (CRE cp (Cons (Col) (C1) pre)) re2 rt)
        (InR _ _ (cons-sel-back e e t t2 t c cc (SelN3 e e t)))))))

(let ((many simple-leaf-c)) (CLeaf (CEmpty)))

(def-fns _ $ (many cfcbr2-c : (erased (List (Step)) cp) (erased (List (Col)) pre get full) (erased (Col) e0) (many (Perm) g) (subterm many (List (Col)) et)
    (erased (PermT g et get) pt) (erased (RevApp (Col) pre get full) ra) (erased (CpCol cp (Cons (Col) e0 full)) cc)
    -> (many (Ctree) t) (erased (Nat) h) (erased (Length (Col) et h) l) (erased (CtH h t) ht) (erased (CtRing cp t pre) rt)
    (erased (Or (HasC0 get) (CtMem t get)) zm))
  (let-match many et (Cons _ e rest)
    ((Nil _) (let-match erased pt (PTNil _)) (values simple-leaf-c (Zero) (LengthNil _) (HL (CEmpty) (HE (Zero))) (CRL cp (CEmpty) pre full e0 ra cc)
      (InR _ _ (leaf-mem (CEmpty))))))
  (let-match erased pt (PTCons _ _ c _ grest pc pt1))
  (let ((many c2) (erased pc2)) (permc-r g e))
  (let-match erased (permc-fn g e c c2 pc pc2) (Refl _ _))
  (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1) (erased zm1))
    (notail $ cfcbr2-c cp (Cons (Col) c pre) grest full e0 g rest pt1 (RACons (Col) c pre grest full ra) cc))
  (let ((many t) (erased ht) (erased rt) (erased sl)) (ct-cons-e-c cp pre h1 c2 t1 ht1 rt1))
  (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt (zmem-cons c t1 t grest sl zm1)))

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

(def-fns _ $ (erased nmem-c1 : (erased (Ctree) u t) (erased (List (Col)) l) (erased (Or (Eq (Col) (C1) (C0)) (CtSel t (C1) u)) sl) (erased (NMem u l) nm)
    -> (erased (NMem t (Cons (Col) (C1) l)) r))
  (let-match erased sl (InR _ _ s) (absurd (InL _ _ q) q))
  (match erased nm _
    ((NMZ _ _ z) (NMZ t _ (HZThere (C1) l z)))
    ((NMIn _ _ p n m)
      (NMIn t _ (Cons (Col) (C1) p)
        (match erased n _
          ((NrEven _ e) (NrEven _ (ET1 l (BTrue) e)))
          ((NrOdd _ _ e q) (NrOdd _ _ (ET1 l (BFalse) e) (PTCons p132 (C1) (C1) l p (PC1 (C1) (C3) (C2)) q))))
        (mem-cons t u (C1) p s m)))))

(def-fns _ $ (erased hasc0-back : (erased (Perm) g) (erased (List (Col)) l l2) (erased (IsPerm g) ip) (subterm erased (PermT g l l2) p) (erased (HasC0 l2) z)
    -> (erased (HasC0 l) r))
  (let-match erased p (PTCons _ c _ l1 l3 pc p1) (absurd (PTNil _) z))
  (let-match erased z (HZHere _)
    ((HZThere _ _ z1) (HZThere c l1 (hasc0-back g l1 l3 ip p1 z1))))
  (match erased pc _ ((PC0 _) (HZHere l1)) (absurd (PC1 _ _ _) ip) (absurd (PC2 _ _ _) ip) (absurd (PC3 _ _ _) ip)))

(def-fns _ $ (many cfcbr1-c : (erased (List (Step)) cp) (erased (List (Col)) pre get full) (erased (Col) e0) (many (Perm) g) (subterm many (List (Col)) et)
    (erased (PermT g et get) pt) (erased (RevApp (Col) pre get full) ra) (erased (CpCol cp (Cons (Col) e0 full)) cc) (erased (IsPerm g) ip)
    (erased (AllC1 pre) a1) -> (many (Ctree) t) (erased (Nat) h) (erased (Length (Col) et h) l) (erased (CtH h t) ht) (erased (CtRing cp t pre) rt)
    (erased (NMem t get) nm))
  (let-match many et (Cons _ e rest)
    ((Nil _) (let-match erased pt (PTNil _)) (values simple-leaf-c (Zero) (LengthNil _) (HL (CEmpty) (HE (Zero))) (CRL cp (CEmpty) pre full e0 ra cc)
      (NMIn simple-leaf-c (Nil (Col)) (Nil (Col)) (NrEven _ (ETNil)) (leaf-mem (CEmpty))))))
  (let-match erased pt (PTCons _ _ c _ grest pc pt1))
  (let ((many c2) (erased pc2)) (permc-r g e))
  (let-match erased (permc-fn g e c c2 pc pc2) (Refl _ _))
  (let ((erased ra1)) (RACons (Col) c pre grest full ra))
  (match many c2 _
    ((C0) (let ((erased h1) (erased l1)) (length-exists _ rest))
      (values (CEmpty) (Succ h1) (LengthCons _ e rest h1 l1) (HE (Succ h1)) (CRE cp pre) (NMZ (CEmpty) _ (HZHere grest))))
    ((C1)
      (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1) (erased nm1))
        (notail $ cfcbr1-c cp (Cons (Col) c pre) grest full e0 g rest pt1 ra1 cc ip (AC1Cons pre a1)))
      (let ((many t) (erased ht) (erased rt) (erased sl)) (ct-cons-e-c cp pre h1 c2 t1 ht1 rt1))
      (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt (nmem-c1 t1 t grest sl nm1)))
    ((C2)
      (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1) (erased zm1)) (cfcbr2-c cp (Cons (Col) c pre) grest full e0 g rest pt1 ra1 cc))
      (let ((many t) (erased ht) (erased rt) (erased sl)) (ct-cons-e-c cp pre h1 c2 t1 ht1 rt1))
      (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt
        (match erased (zmem-cons c t1 t grest sl zm1) _
          ((InL _ _ z) (NMZ t _ z))
          ((InR _ _ m) (NMIn t _ _ (NrEven _ (ET2 grest)) m)))))
    ((C3)
      (let-match many g (MkPerm g1 g2 g3))
      (let ((many q1) (erased c1)) (permc-r p132 g1))
      (let ((many q2) (erased c2p)) (permc-r p132 g2))
      (let ((many q3) (erased c3)) (permc-r p132 g3))
      (let ((erased pk) (erased _)) (p132-of g1 g2 g3 q1 q2 q3 ip c1 c2p c3))
      (let ((many hp)) (MkPerm q1 q2 q3))
      (let ((erased hrest) (erased ph)) (permt-ex p132 grest (IP132)))
      (let ((erased full2) (erased ra2)) (revapp-exists (Col) pre (Cons (Col) (C2) hrest)))
      (let ((erased pf)) (permt-revapp p132 pre (Cons (Col) (C2) hrest) full2 pre (Cons (Col) (C3) grest) full ra2 ra (permt-c1 pre a1)
        (PTCons p132 (C3) (C2) grest hrest (PC3 (C1) (C3) (C2)) ph)))
      (let ((erased e02) (erased pe)) (permc-ex p132 e0 (IP132)))
      (let ((erased cc2)) (cpcol-perm cp (Cons (Col) e0 full) (Cons (Col) e02 full2) p132 cc (IP132) (PTCons p132 e0 e02 full full2 pe pf)))
      (let ((many t1) (erased h1) (erased l1) (erased ht1) (erased rt1) (erased zm1)) (cfcbr2-c cp (Cons (Col) (C2) pre) hrest full2 e02 hp rest
        (permt-p132 g hp rest grest hrest pk pt1 ph) (RACons (Col) (C2) pre hrest full2 ra2) cc2))
      (let ((many t) (erased ht) (erased rt) (erased sl)) (ct-cons-e-c cp pre h1 (C2) t1 ht1 rt1))
      (values t (Succ h1) (LengthCons _ e rest h1 l1) ht rt
        (match erased (zmem-cons (C2) t1 t hrest sl zm1) _
          ((InL _ _ z) (let-match erased z (HZThere _ _ z1)) (NMZ t _ (HZThere (C3) grest (hasc0-back p132 grest hrest (IP132) ph z1))))
          ((InR _ _ m) (NMIn t _ _ (NrOdd _ _ (ET3 grest) (PTCons p132 (C3) (C2) grest hrest (PC3 (C1) (C3) (C2)) ph)) m)))))))

(def-fns _ $ (many edge-rot-c : (many (Col) e) (erased (NZ e) nz) -> (many (Perm) g) (erased (IsPerm g) ip) (erased (PermC g e (C1)) p))
  (match many e _
    ((C1) (values p123 (IP123) (PC1 (C1) (C2) (C3))))
    ((C2) (values p312 (IP312) (PC2 (C3) (C1) (C2))))
    ((C3) (values p231 (IP231) (PC3 (C2) (C3) (C1))))
    (absurd (C0) nz)))

; The trace et is e0 :: e1 :: rest, and t holds the normalisation of rest under a colour permutation g taking e1 to C1.
(def-adts $ (BrMem : ((List (Col)) et) ((Ctree) t) -> Type)
  enum
  (many MkBrMem : (erased (Col) e0 e1) (erased (List (Col)) rest grest) (erased (Ctree) t) (erased (Perm) g) (erased (IsPerm g) ip)
      (erased (PermC g e1 (C1)) pg) (erased (PermT g rest grest) pt) (erased (NMem t grest) nm) -> (BrMem (Cons (Col) e0 (Cons (Col) e1 rest)) t)))

(def-fns _ $ (many cpbranch-c : (erased (List (Step)) cp) (erased (Nat) h) (many (List (Col)) et) (erased (CpCol cp et) cc)
    (erased (Length (Col) et (Succ (Succ h))) l) -> (many (Ctree) t) (erased (CtH h t) ht) (erased (CtRing cp t (Cons (Col) (C1) (Nil (Col)))) rt)
    (erased (BrMem et t) bm))
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
  (let ((many t) (erased h1) (erased l1) (erased ht) (erased rt) (erased nm))
    (cfcbr1-c cp (Cons (Col) (C1) (Nil (Col))) grest full e02 g rest pt (RACons (Col) (C1) (Nil (Col)) grest full (RANil (Col) full)) cc2 ip
      (AC1Cons (Nil (Col)) (AC1Nil))))
  (let-match erased l (LengthCons _ _ _ _ l2))
  (let-match erased l2 (LengthCons _ _ _ _ l3))
  (let-match erased (length-fn _ rest h h1 l3 l1) (Refl _ _))
  (values t ht rt (MkBrMem e0 e1 rest grest t g ip pg pt nm)))

(def-adts $ (NZDec : ((Col) c) -> Type)
  enum
  (many NZZero : -> (NZDec (C0)))
  (many NZYes : (erased (Col) c) (erased (NZ c) p) -> (NZDec c)))

(def-fns _ $ (many nz-dec : (many (Col) c) -> (many (NZDec c) r))
  (match many c _ ((C0) (NZZero)) ((C1) (NZYes c (NZ1))) ((C2) (NZYes c (NZ2))) ((C3) (NZYes c (NZ3)))))

(def-fns _ $ (erased others : (erased (Col) e1 e2 e3) (erased (NZ e1) nz) (erased (PermC p231 e1 e2) p2) (erased (PermC p312 e1 e3) p3)
    -> (erased (AddC e1 e2 e3) a) (erased (AddC e1 e3 e2) b) (erased (NZ e2) n2) (erased (NZ e3) n3))
  (match erased nz _
    ((NZ1) (let-match erased p2 (PC1 _ _ _)) (let-match erased p3 (PC1 _ _ _)) (values (Add12) (Add13) (NZ2) (NZ3)))
    ((NZ2) (let-match erased p2 (PC2 _ _ _)) (let-match erased p3 (PC2 _ _ _)) (values (Add23) (Add21) (NZ3) (NZ1)))
    ((NZ3) (let-match erased p2 (PC3 _ _ _)) (let-match erased p3 (PC3 _ _ _)) (values (Add31) (Add32) (NZ1) (NZ2)))))

(def-fns _ $ (erased sub2gt2-fn : (erased (Nat) k a b) (erased (Sub2gt2 k a) p) (erased (Sub2gt2 k b) q) -> (erased (Eq (Nat) a b) e))
  (match erased p _
    ((S2Big _) (let-match erased q (S2Big _)
      (absurd (S2Small _ lt) (let-match erased lt (LtS _ _ l1)) (let-match erased l1 (LtS _ _ l2)) (let-match erased l2 (LtS _ _ l3)) l3)) (Refl _ a))
    ((S2Small _ lt) (let-match erased q (S2Small _ _)
      (absurd (S2Big _) (let-match erased lt (LtS _ _ l1)) (let-match erased l1 (LtS _ _ l2)) (let-match erased l2 (LtS _ _ l3)) l3)) (Refl _ a))))

(def-fns _ $ (erased pred2s-fn : (erased (Nat) k a b) (erased (Pred2S k a) p) (erased (Pred2S k b) q) -> (erased (Eq (Nat) a b) e))
  (match erased p _
    ((P2Zero) (let-match erased q (P2Zero)) (Refl _ a))
    ((P2One) (let-match erased q (P2One)) (Refl _ a))
    ((P2Step _) (let-match erased q (P2Step _)) (Refl _ a))))

(def-fns _ $ (erased cprsize-fn : (erased (List (Step)) cp) (erased (Nat) a b) (subterm erased (Cprsize cp a) p) (erased (Cprsize cp b) q) -> (erased (Eq (Nat) a b) e))
  (match erased p _
    ((CsNil) (let-match erased q (CsNil)) (Refl _ a))
    ((CsR _ _ cp1 p1) (let-match erased q (CsR _ _ _ q1)) (cprsize-fn cp1 a b p1 q1))
    ((CsRr _ cp1 p1) (let-match erased q (CsRr _ _ q1)) (cprsize-fn cp1 a b p1 q1))
    ((CsH _ cp1 p1) (let-match erased q (CsH _ _ q1)) (cprsize-fn cp1 a b p1 q1))
    ((CsY a1 cp1 p1) (let-match erased q (CsY b1 _ q1)) (let-match erased (cprsize-fn cp1 a1 b1 p1 q1) (Refl _ _)) (Refl _ a))
    ((CsU a1 cp1 p1) (let-match erased q (CsU b1 _ q1)) (let-match erased (cprsize-fn cp1 a1 b1 p1 q1) (Refl _ _)) (Refl _ a))
    ((CsK a1 _ cp1 p1 pa) (let-match erased q (CsK b1 _ _ q1 pb)) (let-match erased (cprsize-fn cp1 a1 b1 p1 q1) (Refl _ _)) (pred2s-fn a1 a b pa pb))
    ((CsA a1 _ cp1 p1 pa) (let-match erased q (CsA b1 _ _ q1 pb)) (let-match erased (cprsize-fn cp1 a1 b1 p1 q1) (Refl _ _)) (sub2gt2-fn a1 a b pa pb))))

(def-fns _ $ (erased cpcol-length : (erased (List (Step)) cp) (erased (List (Col)) et) (erased (CpCol cp et) cc) -> (erased (Nat) k) (erased (Length (Col) et k) l)
    (erased (Cprsize cp k) cs))
  (let-match erased cc (MkCpCol _ d e f r ks rc cs _ cm _ rr nc tr))
  (let ((erased k) (erased l) (erased c)) (cpmap-size cp d e f r cm))
  (values k (trace-length cs et k tr (ncols-length rc cs k nc (respects-length ks r rc k rr l))) c))

(def-fns _ $ (erased noa-suffix : (erased (List (Step)) pre w r) (subterm erased (RevApp (Step) pre w r) a) (erased (NoA r) na) -> (erased (NoA w) res))
  (let-match erased a (RACons _ s pre1 _ _ a1) ((RANil _ _) na))
  (noa-tail s w (noa-suffix pre1 (Cons (Step) s w) r a1 na)))

; et has fewer than two entries.
(def-adts $ (Short : ((List (Col)) et) -> Type)
  enum
  (many ShortNil : -> (Short (Nil (Col))))
  (many ShortOne : (erased (Col) e) -> (Short (Cons (Col) e (Nil (Col))))))

; et is e1 :: e2 :: r2, and sm is e1 + e2.
(def-adts $ (Two : ((List (Col)) et) -> Type)
  enum
  (many TwoNo : (erased (List (Col)) et) (erased (Short et) sh) -> (Two et))
  (many TwoYes : (erased (List (Col)) et) (many (Col) e1 e2) (many (List (Col)) r2) (many (Col) sm)
      (erased (Eq (List (Col)) et (Cons (Col) e1 (Cons (Col) e2 r2))) q) (erased (AddC e1 e2 sm) p) -> (Two et)))

(def-fns _ $ (many two-c : (many (List (Col)) et) -> (many (Two et) r))
  (let-match many et (Cons _ e1 r1) ((Nil _) (TwoNo et (ShortNil))))
  (let-match many r1 (Cons _ e2 r2) ((Nil _) (TwoNo et (ShortOne e1))))
  (let ((many sm) (erased p)) (addc-c e1 e2))
  (TwoYes et e1 e2 r2 sm (Refl _ et) p))

; No cubic step s applies to et.
(def-adts $ (NotTr : ((Step) s) ((List (Col)) et) -> Type)
  enum
  (many NTRr : (erased (List (Col)) et) -> (NotTr (SRr) et))
  (many NTK : (erased (List (Col)) et) -> (NotTr (SK) et))
  (many NTY : -> (NotTr (SY) (Nil (Col))))
  (many NTH : (erased (List (Col)) et) (erased (Short et) sh) -> (NotTr (SH) et)))

; How cpcol-c built t from et and the steps cp1.
(def-adts $ (CpCov : ((List (Step)) cp1) ((List (Col)) et) ((Ctree) t) -> Type)
  enum
  (many CoNil : (erased (List (Col)) et) (erased (Ctree) t) (erased (BrMem et t) bm) -> (CpCov (Nil (Step)) et t))
  (many CoVoid : (erased (Step) s) (erased (List (Step)) cp1) (erased (List (Col)) et) (erased (Ctree) t) (erased (NotTr s et) nt)
      -> (CpCov (Cons (Step) s cp1) et t))
  (many CoR : (erased (Nat) k) (erased (List (Step)) cp1) (erased (List (Col)) et et2) (erased (Ctree) t) (erased (Rot (Col) k et et2) rt)
      (erased (CpCov cp1 et2 t) c) -> (CpCov (Cons (Step) (SR k) cp1) et t))
  (many CoU : (erased (List (Step)) cp1) (erased (List (Col)) et) (erased (Ctree) t1 t2 t3 u t) (erased (CtOr t2 t3 u) ou) (erased (CtOr t1 u t) o)
      (erased (CpCov cp1 (Cons (Col) (C1) (Cons (Col) (C1) et)) t1) c1) (erased (CpCov cp1 (Cons (Col) (C2) (Cons (Col) (C2) et)) t2) c2)
      (erased (CpCov cp1 (Cons (Col) (C3) (Cons (Col) (C3) et)) t3) c3) -> (CpCov (Cons (Step) (SU) cp1) et t))
  (many CoY : (erased (Col) e1 e2 e3) (erased (List (Col)) r1) (erased (List (Step)) cp1) (erased (Ctree) t1 t2 t) (erased (PermC p231 e1 e2) p2)
      (erased (PermC p312 e1 e3) p3) (erased (CpCov cp1 (Cons (Col) e2 (Cons (Col) e3 r1)) t1) c1) (erased (CpCov cp1 (Cons (Col) e3 (Cons (Col) e2 r1)) t2) c2)
      (erased (CtOr t1 t2 t) o) -> (CpCov (Cons (Step) (SY) cp1) (Cons (Col) e1 r1) t))
  (many CoH0 : (erased (Col) e1 e2 g1 g2) (erased (List (Col)) r2) (erased (List (Step)) cp1) (erased (Ctree) t1 t2 t) (erased (AddC e1 e2 (C0)) p)
      (erased (PermC p231 e1 g1) p2) (erased (PermC p312 e1 g2) p3) (erased (CpCov cp1 (Cons (Col) g1 (Cons (Col) g1 r2)) t1) c1)
      (erased (CpCov cp1 (Cons (Col) g2 (Cons (Col) g2 r2)) t2) c2) (erased (CtOr t1 t2 t) o) -> (CpCov (Cons (Step) (SH) cp1) (Cons (Col) e1 (Cons (Col) e2 r2)) t))
  (many CoH : (erased (Col) e1 e2 sm) (erased (List (Col)) r2) (erased (List (Step)) cp1) (erased (Ctree) t) (erased (AddC e1 e2 sm) p) (erased (NZ sm) nz)
      (erased (CpCov cp1 (Cons (Col) e2 (Cons (Col) e1 r2)) t) c) -> (CpCov (Cons (Step) (SH) cp1) (Cons (Col) e1 (Cons (Col) e2 r2)) t)))

(def-fns _ $ (many cpcol-c : (erased (List (Step)) cp2 full) (erased (Nat) h) (subterm many (List (Step)) cp1) (many (List (Col)) et)
    (erased (RevApp (Step) cp1 cp2 full) ra) (erased (CpCol cp2 et) cc) (erased (Cprsize full (Succ (Succ h))) cs) (erased (NoA full) na)
    -> (many (Ctree) t) (erased (CtH h t) ht) (erased (CtRing full t (Cons (Col) (C1) (Nil (Col)))) rt) (erased (CpCov cp1 et t) cv))
  (let ((erased pre1)) (Cons (Col) (C1) (Nil (Col))))
  (let ((many no) (erased hno) (erased rno)) (values (CEmpty) (HE h) (CRE full pre1)))
  (let-match many cp1 (Cons _ s rest)
    ((Nil _)
      (let-match erased ra (RANil _ _))
      (let ((erased k) (erased l) (erased cs2)) (cpcol-length cp2 et cc))
      (let-match erased (cprsize-fn cp2 k (Succ (Succ h)) cs2 cs) (Refl _ _))
      (let ((many t) (erased ht) (erased rt) (erased bm)) (cpbranch-c full h et cc l))
      (values t ht rt (CoNil et t bm))))
  (let-match erased ra (RACons _ _ _ _ _ ra1))
  (let ((erased nzs)) (cpcol-nz cp2 et cc))
  (match many s _
    ((SR k)
      (let ((many et2) (erased rt)) (rot-c _ k et))
      (let ((many t) (erased ht) (erased rt1) (erased cv)) (tail $ cpcol-c (Cons (Step) s cp2) full h rest et2 ra1 (cpcol-r cp2 k et et2 cc rt) cs na))
      (values t ht rt1 (CoR k rest et et2 t rt cv)))
    ((SRr)
      (let ((erased cvn)) (CoVoid s rest et no (NTRr et)))
      (let ((many m1) (erased lm)) (size-c _ et))
      (let-match many m1 (Succ m) ((Zero) (values no hno rno cvn)))
      (let-match many m (Succ _) ((Zero) (values no hno rno cvn)))
      (let ((many et2) (erased rt)) (rot-c _ m et))
      (let ((many t) (erased ht) (erased rt1) (erased _)) (tail $ cpcol-c (Cons (Step) s cp2) full h rest et2 ra1 (cpcol-rr cp2 m et et2 cc lm rt) cs na))
      (values t ht rt1 (CoVoid s rest et t (NTRr et))))
    ((SU)
      (let ((erased cp3)) (Cons (Step) s cp2))
      (let ((many t1) (erased h1) (erased r1) (erased c1))
        (notail $ cpcol-c cp3 full h rest (Cons _ (C1) (Cons _ (C1) et)) ra1 (cpcol-u cp2 et (C1) cc (NZ1)) cs na))
      (let ((many t2) (erased h2) (erased r2) (erased c2))
        (notail $ cpcol-c cp3 full h rest (Cons _ (C2) (Cons _ (C2) et)) ra1 (cpcol-u cp2 et (C2) cc (NZ2)) cs na))
      (let ((many t3) (erased h3) (erased r3) (erased c3))
        (notail $ cpcol-c cp3 full h rest (Cons _ (C3) (Cons _ (C3) et)) ra1 (cpcol-u cp2 et (C3) cc (NZ3)) cs na))
      (let ((many u) (erased ou) (erased hu)) (ctree-union h t2 t3 h2 h3))
      (let ((many t) (erased o) (erased ht)) (ctree-union h t1 u h1 hu))
      (values t ht (ctring-or full t1 u t pre1 o r1 (ctring-or full t2 t3 u pre1 ou r2 r3)) (CoU rest et t1 t2 t3 u t ou o c1 c2 c3)))
    ((SY)
      (let-match many et (Cons _ e1 r1) ((Nil _) (values no hno rno (CoVoid s rest et no (NTY)))))
      (let-match erased nzs (AllNZCons _ _ nz1 _))
      (let ((many e2) (erased p2)) (permc-r p231 e1))
      (let ((many e3) (erased p3)) (permc-r p312 e1))
      (let ((erased a23) (erased a32) (erased n2) (erased n3)) (others e1 e2 e3 nz1 p2 p3))
      (let ((erased cp3)) (Cons (Step) s cp2))
      (let ((many t1) (erased h1) (erased q1) (erased c1))
        (notail $ cpcol-c cp3 full h rest (Cons _ e2 (Cons _ e3 r1)) ra1 (cpcol-y cp2 r1 e1 e2 e3 cc a23 n2 n3) cs na))
      (let ((many t2) (erased h2) (erased q2) (erased c2))
        (notail $ cpcol-c cp3 full h rest (Cons _ e3 (Cons _ e2 r1)) ra1 (cpcol-y cp2 r1 e1 e3 e2 cc a32 n3 n2) cs na))
      (let ((many t) (erased o) (erased ht)) (ctree-union h t1 t2 h1 h2))
      (values t ht (ctring-or full t1 t2 t pre1 o q1 q2) (CoY e1 e2 e3 r1 rest t1 t2 t p2 p3 c1 c2 o)))
    ((SK)
      (let ((erased cvn)) (CoVoid s rest et no (NTK et)))
      (let-match many (two-c et) (TwoYes _ e1 e2 r2 sm q psm) ((TwoNo _ _) (values no hno rno cvn)))
      (let-match erased q (Refl _ _))
      (let-match many (nz-dec sm) (NZYes _ nzs2) ((NZZero) (values no hno rno cvn)))
      (let ((many t) (erased ht) (erased rt1) (erased _))
        (tail $ cpcol-c (Cons (Step) s cp2) full h rest (Cons _ sm r2) ra1 (cpcol-k cp2 r2 e1 e2 sm cc psm nzs2) cs na))
      (values t ht rt1 (CoVoid s rest et t (NTK et))))
    ((SH)
      (let-match many (two-c et) (TwoYes _ e1 e2 r2 sm q psm) ((TwoNo _ sh) (values no hno rno (CoVoid s rest et no (NTH et sh)))))
      (let-match erased q (Refl _ _))
      (let-match erased nzs (AllNZCons _ _ nz1 nzs1))
      (let-match erased nzs1 (AllNZCons _ _ nz2 _))
      (let ((erased cp3)) (Cons (Step) s cp2))
      (match many (nz-dec sm) _
        ((NZZero)
          (let ((many g1) (erased p2)) (permc-r p231 e1))
          (let ((many g2) (erased p3)) (permc-r p312 e1))
          (let ((erased a23) (erased a32) (erased n2) (erased n3)) (others e1 g1 g2 nz1 p2 p3))
          (let ((many t1) (erased h1) (erased q1) (erased c1)) (notail $ cpcol-c cp3 full h rest (Cons _ g1 (Cons _ g1 r2)) ra1
            (cpcol-h cp2 r2 e1 e2 (C0) g1 g2 g1 cc psm a23 (addc-0l g1) n2 n3 n2) cs na))
          (let ((many t2) (erased h2) (erased q2) (erased c2)) (notail $ cpcol-c cp3 full h rest (Cons _ g2 (Cons _ g2 r2)) ra1
            (cpcol-h cp2 r2 e1 e2 (C0) g2 g1 g2 cc psm a32 (addc-0l g2) n3 n2 n3) cs na))
          (let ((many t) (erased o) (erased ht)) (ctree-union h t1 t2 h1 h2))
          (values t ht (ctring-or full t1 t2 t pre1 o q1 q2) (CoH0 e1 e2 g1 g2 r2 rest t1 t2 t psm p2 p3 c1 c2 o)))
        ((NZYes _ nzs2)
          (let ((erased pse)) (addc-comm e2 sm e1 (addc-cancel e2 sm e1 (addc-comm e1 e2 sm psm))))
          (let ((many t) (erased ht) (erased rt1) (erased c1))
            (tail $ cpcol-c cp3 full h rest (Cons _ e2 (Cons _ e1 r2)) ra1 (cpcol-h cp2 r2 e1 e2 sm e2 sm e1 cc psm psm pse nz2 nzs2 nz1) cs na))
          (values t ht rt1 (CoH e1 e2 sm r2 rest t psm nzs2 c1)))))
    (absurd (SA) (noa-suffix rest (Cons (Step) (SA) cp2) full ra1 na))))

(let ((many c11)) (Cons (Col) (C1) (Cons (Col) (C1) (Nil (Col)))))

(def-fns _ $ (erased cpcol0 : -> (erased (CpCol (Nil (Step)) c11) r))
  (let ((erased o) (erased z)) (values (Succ (Zero)) (Zero)))
  (let ((erased l1) (erased l0) (erased ks)) (values (Cons (Nat) o (Nil (Nat))) (Cons (Nat) z (Nil (Nat))) (Cons (Nat) z (Cons (Nat) o (Nil (Nat))))))
  (let ((erased e)) (Cons (Nat) o l0))
  (let ((erased n0) (erased n1)) (values (NthHere _ z l1) (NthThere _ z l1 z o (NthHere _ o (Nil (Nat))))))
  (let ((erased re)) (RespCons ks l0 l0 o o n1 (RespCons ks (Nil (Nat)) (Nil (Nat)) z z n0 (RespNil ks))))
  (let ((erased rf)) (RespCons ks l1 l1 z z n0 (RespCons ks (Nil (Nat)) (Nil (Nat)) o o n1 (RespNil ks))))
  (let ((erased df)) (DifferCons l0 l1 o z (ApGt _ _ o z (LtZ z)) (DifferCons (Nil (Nat)) (Nil (Nat)) z o (ApLt _ _ z o (LtZ z)) (DifferNil))))
  (let ((erased un)) (UnderCons l1 z 4 (LtZ _) (UnderCons (Nil (Nat)) o 4 (LtS z _ (LtZ _)) (UnderNil 4))))
  (MkCpCol (Nil (Step)) (Succ o) e ks e ks e (Cons (Col) (C1) (Cons (Col) (C0) (Nil (Col)))) c11 (CmNil) (MkFourColoring e ks ks e rf re df un) re
    (NCsCons o (C1) l0 (Cons (Col) (C0) (Nil (Col))) (NC1) (NCsCons z (C0) (Nil (Nat)) (Nil (Col)) (NC0) (NCsNil)))
    (MkTrace (C1) (Cons (Col) (C0) (Nil (Col))) c11 (CTStep (C1) (C1) (C0) (C1) (Nil (Col)) (Cons (Col) (C1) (Nil (Col))) (Add10) (CTLast (C1) (C0) (C1) (Add01))))))

(def-fns _ $ (erased rots-cc : (erased (Col) c) (subterm erased (Nat) k) -> (erased (Rots (Col) k (Cons (Col) c (Cons (Col) c (Nil (Col))))
    (Cons (Col) c (Cons (Col) c (Nil (Col))))) r))
  (let ((erased cl) (erased cc2)) (values (Cons (Col) c (Nil (Col))) (Cons (Col) c (Cons (Col) c (Nil (Col))))))
  (let-match erased k (Succ k1) ((Zero) (RotsZ _ cc2)))
  (RotsS _ k1 c cl cc2 cc2 (SnocCons _ c c (Nil (Col)) cl (SnocNil _ c)) (rots-cc c k1)))

(def-fns _ $ (erased rot-cc : (erased (Col) c) (erased (Nat) k) -> (erased (Rot (Col) k (Cons (Col) c (Cons (Col) c (Nil (Col)))) (Cons (Col) c (Cons (Col) c (Nil (Col))))) r))
  (let ((erased cc2)) (Cons (Col) c (Cons (Col) c (Nil (Col)))))
  (let ((erased m) (erased l)) (values (Succ (Succ (Zero))) (LengthCons _ c (Cons (Col) c (Nil (Col))) (Succ (Zero)) (LengthCons _ c (Nil (Col)) (Zero) (LengthNil _)))))
  (match erased (nat-cmp k m) _
    ((CLt _ _ _ _ lt) (RotIn _ k m cc2 cc2 l (lt-weaken k m lt) (rots-cc c k)))
    ((CEq _ _ _) (RotIn _ k m cc2 cc2 l (lt-succ k) (rots-cc c k)))
    ((CGt _ _ _ _ gt) (RotOver _ k m cc2 l gt))))

; How cpcolor0-c built t from the steps cp1.
(def-adts $ (CpCov0 : ((List (Step)) cp1) ((Ctree) t) -> Type)
  enum
  (many C0Base : (erased (List (Step)) cp1) (erased (Ctree) t) (erased (CpCov cp1 c11 t) c) -> (CpCov0 cp1 t))
  (many C0R : (erased (Nat) k) (erased (List (Step)) cp1) (erased (Ctree) t) (erased (CpCov0 cp1 t) c) -> (CpCov0 (Cons (Step) (SR k) cp1) t))
  (many C0Y : (erased (List (Step)) cp1) (erased (Ctree) t) (erased (CpCov cp1 (Cons (Col) (C1) (Cons (Col) (C2) (Cons (Col) (C3) (Nil (Col))))) t) c)
      -> (CpCov0 (Cons (Step) (SY) cp1) t))
  (many C0U : (erased (List (Step)) cp1) (erased (Ctree) t1 t2 t)
      (erased (CpCov cp1 (Cons (Col) (C1) (Cons (Col) (C1) (Cons (Col) (C2) (Cons (Col) (C2) (Nil (Col)))))) t1) c1)
      (erased (CpCov cp1 (Cons (Col) (C1) (Cons (Col) (C1) c11)) t2) c2) (erased (CtOr t1 t2 t) o) -> (CpCov0 (Cons (Step) (SU) cp1) t)))

(def-fns _ $ (many cpcolor0-c : (erased (List (Step)) cp2 full) (erased (Nat) h) (subterm many (List (Step)) cp1) (erased (RevApp (Step) cp1 cp2 full) ra)
    (erased (CpCol cp2 c11) cc) (erased (Cprsize full (Succ (Succ h))) cs) (erased (NoA full) na)
    -> (many (Ctree) t) (erased (CtH h t) ht) (erased (CtRing full t (Cons (Col) (C1) (Nil (Col)))) rt) (erased (CpCov0 cp1 t) cv))
  (let-match many cp1 (Cons _ s rest)
    ((Nil _) (let ((many t) (erased ht) (erased rt) (erased cv)) (cpcol-c cp2 full h cp1 c11 ra cc cs na)) (values t ht rt (C0Base cp1 t cv))))
  (let-match erased ra (RACons _ _ _ _ _ ra1))
  (let ((erased cp3)) (Cons (Step) s cp2))
  (let ((erased c1l)) (Cons (Col) (C1) (Nil (Col))))
  (match many s _
    ((SR k)
      (let ((many t) (erased ht) (erased rt) (erased cv)) (tail $ cpcolor0-c cp3 full h rest ra1 (cpcol-r cp2 k c11 c11 cc (rot-cc (C1) k)) cs na))
      (values t ht rt (C0R k rest t cv)))
    ((SY)
      (let ((erased g) (erased et) (erased et2)) (values p312 (Cons (Col) (C2) (Cons (Col) (C3) c1l)) (Cons (Col) (C1) (Cons (Col) (C2) (Cons (Col) (C3) (Nil (Col)))))))
      (let ((erased pt)) (PTCons g (C2) (C1) (Cons (Col) (C3) c1l) (Cons (Col) (C2) (Cons (Col) (C3) (Nil (Col)))) (PC2 (C3) (C1) (C2))
        (PTCons g (C3) (C2) c1l (Cons (Col) (C3) (Nil (Col))) (PC3 (C3) (C1) (C2)) (PTCons g (C1) (C3) (Nil (Col)) (Nil (Col)) (PC1 (C3) (C1) (C2)) (PTNil g)))))
      (let ((many t) (erased ht) (erased rt) (erased cv)) (tail $ cpcol-c cp3 full h rest (Cons _ (C1) $ Cons _ (C2) $ Cons _ (C3) $ Nil _) ra1
        (cpcol-perm cp3 et et2 g (cpcol-y cp2 c1l (C1) (C2) (C3) cc (Add12) (NZ2) (NZ3)) (IP312) pt) cs na))
      (values t ht rt (C0Y rest t cv)))
    ((SU)
      (let ((erased g) (erased c22)) (values (MkPerm (C2) (C1) (C3)) (Cons (Col) (C2) (Cons (Col) (C2) c11))))
      (let ((erased e1122)) (Cons (Col) (C1) (Cons (Col) (C1) (Cons (Col) (C2) (Cons (Col) (C2) (Nil (Col)))))))
      (let ((erased p21) (erased p12)) (values (PC2 (C2) (C1) (C3)) (PC1 (C2) (C1) (C3))))
      (let ((erased pt)) (PTCons g (C2) (C1) (Cons (Col) (C2) c11) (Cons (Col) (C1) (Cons (Col) (C2) (Cons (Col) (C2) (Nil (Col))))) p21
        (PTCons g (C2) (C1) c11 (Cons (Col) (C2) (Cons (Col) (C2) (Nil (Col)))) p21
          (PTCons g (C1) (C2) c1l (Cons (Col) (C2) (Nil (Col))) p12 (PTCons g (C1) (C2) (Nil (Col)) (Nil (Col)) p12 (PTNil g))))))
      (let ((many t1) (erased h1) (erased r1) (erased c1)) (notail $ cpcol-c cp3 full h rest (Cons _ (C1) $ Cons _ (C1) $ Cons _ (C2) $ Cons _ (C2) $ Nil _) ra1
        (cpcol-perm cp3 c22 e1122 g (cpcol-u cp2 c11 (C2) cc (NZ2)) (IP213) pt) cs na))
      (let ((many t2) (erased h2) (erased r2) (erased c2)) (notail $ cpcol-c cp3 full h rest (Cons _ (C1) $ Cons _ (C1) c11) ra1 (cpcol-u cp2 c11 (C1) cc (NZ1)) cs na))
      (let ((many t) (erased o) (erased ht)) (ctree-union h t1 t2 h1 h2))
      (values t ht (ctring-or full t1 t2 t c1l o r1 r2) (C0U rest t1 t2 t c1 c2 o)))
    (else (let ((many t) (erased ht) (erased rt) (erased cv)) (cpcol-c cp2 full h cp1 c11 ra cc cs na)) (values t ht rt (C0Base cp1 t cv)))))

(def-fns _ $ (many rev-onto-c : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) zs) (erased (RevApp A xs acc zs) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values acc (RANil A acc))))
  (let ((many zs) (erased p)) (tail $ rev-onto-c _ rest (Cons _ x acc)))
  (values zs (RACons A x rest acc zs p)))

(def-fns _ $ (erased revapp-flip : (erased Type A) (erased (List A) pre w r t) (subterm erased (RevApp A pre w r) a) (erased (RevApp A w pre t) b)
    -> (erased (RevApp A r (Nil A) t) res))
  (let-match erased a (RACons _ s pre1 _ _ a1) ((RANil _ _) b))
  (revapp-flip A pre1 (Cons A s w) r t a1 (RACons A s w pre1 t b)))

; t is C1 then t0, with the rotations ta and tb of t0 below C2 and C3, and cp read backwards is rcp, the steps cpcolor0-c ran
; to build t0.
(def-adts $ (CpComp : ((List (Step)) cp) ((Ctree) t) -> Type)
  enum
  (many MkCpComp : (erased (List (Step)) cp rcp) (erased (Ctree) t0 ta tb t) (erased (RevApp (Step) rcp (Nil (Step)) cp) ra) (erased (CpCov0 rcp t0) cv)
      (erased (CtCons t0 ta tb t) c) (erased (CtPerm p312 t0 ta) pa) (erased (CtPerm p231 t0 tb) pb) -> (CpComp cp t)))

(def-fns _ $ (many cpcolor-c : (erased (Nat) h) (many (List (Step)) cp) (erased (Cprsize cp (Succ (Succ h))) cs) (erased (NoA cp) na)
    -> (many (Ctree) t) (erased (CtH (Succ h) t) ht) (erased (CtRing cp t (Nil (Col))) rt) (erased (CpComp cp t) comp))
  (let ((many rcp) (erased ra)) (rev-onto-c _ cp (Nil _)))
  (let ((erased ra2)) (revapp-flip (Step) cp (Nil (Step)) rcp cp ra (RANil (Step) cp)))
  (let ((many t0) (erased ht0) (erased rt0) (erased cv)) (cpcolor0-c (Nil (Step)) cp h rcp ra2 (cpcol0) cs na))
  (let ((many ta) (erased pa)) (ctree-rot (BTrue) p312 (RDL) t0))
  (let ((many tb) (erased pb)) (ctree-rot (BFalse) p231 (RDR) t0))
  (let ((many t) (erased c)) (ctree-cons t0 ta tb))
  (values t (cons-h h t0 ta tb t c ht0 (perm-h p312 h t0 ta pa ht0) (perm-h p231 h t0 tb pb ht0))
    (ctring-cons cp t0 ta tb t (Nil (Col)) c rt0
      (ctring-perm cp p312 p231 t0 ta (Cons (Col) (C1) (Nil (Col))) (Cons (Col) (C2) (Nil (Col))) pa rt0
        (PTCons p312 (C2) (C1) (Nil (Col)) (Nil (Col)) (PC2 (C3) (C1) (C2)) (PTNil p312)) (PI312) (IP231))
      (ctring-perm cp p231 p312 t0 tb (Cons (Col) (C1) (Nil (Col))) (Cons (Col) (C3) (Nil (Col))) pb rt0
        (PTCons p231 (C3) (C1) (Nil (Col)) (Nil (Col)) (PC3 (C2) (C3) (C1)) (PTNil p231)) (PI231) (IP312)))
    (MkCpComp cp rcp t0 ta tb t ra2 cv c pa pb)))

; ct is a ring trace of cp's map with its first entry moved to the end.
(def-adts $ (CpColR : ((List (Step)) cp) ((List (Col)) ct) -> Type)
  enum
  (many MkCpColR : (erased (List (Step)) cp) (erased (List (Col)) et ct) (erased (Col) e0) (erased (Snoc (Col) et e0 ct) s)
      (erased (CpCol cp (Cons (Col) e0 et)) c) -> (CpColR cp ct)))

(def-fns _ $ (erased ctr-ctrace : (erased (Col) s c0 x sx t) (erased (List (Col)) cs et) (subterm erased (CTr c0 x cs et) p) (erased (AddC s x sx) a)
    (erased (AddC sx c0 t) b) -> (erased (List (Col)) ct) (erased (Ctr s et ct) cr) (erased (Snoc (Col) et t ct) sn))
  (let-match erased p (CTStep _ _ y t1 cs1 et1 p1 rest)
    ((CTLast _ _ t1 p1)
      (values (Cons _ t1 (Cons _ t (Nil _))) (CtrCons s t1 t (Nil _) (Cons _ t (Nil _)) (addc-k s t1 t (addc-assoc s x c0 sx t1 t a b p1)) (CtrNil t))
        (SnocCons _ t1 t (Nil _) (Cons _ t (Nil _)) (SnocNil _ t)))))
  (let ((erased s2) (erased q)) (addc-c sx y))
  (let ((erased ct1) (erased cr1) (erased sn1))
    (ctr-ctrace s2 c0 y sx t cs1 et1 rest (addc-comm y s2 sx (addc-cancel y s2 sx (addc-comm sx y s2 q))) b))
  (values (Cons _ t1 ct1) (CtrCons s t1 s2 et1 ct1 (addc-k s t1 s2 (addc-assoc s x y sx t1 s2 a q p1)) cr1) (SnocCons _ t1 t et1 ct1 sn1)))

(def-fns _ $ (erased trace-ctr : (erased (List (Col)) cs et) (erased (Col) e0) (erased (Trace cs (Cons (Col) e0 et)) tr) ->
    (erased (List (Col)) ct) (erased (Ctr (C0) et ct) cr) (erased (Snoc (Col) et e0 ct) sn))
  (let-match erased tr (MkTrace c _ _ p))
  (let-match erased p (CTLast _ _ _ p1)
    ((CTStep _ _ y _ cs1 _ p1 rest) (ctr-ctrace (C0) c y y e0 cs1 et rest (addc-0l y) (addc-comm c y e0 p1))))
  (let-match erased (addc-fn c c e0 (C0) p1 (addc-ii c)) (Refl _ _))
  (values (Cons _ e0 (Nil _)) (CtrNil (C0)) (SnocNil _ e0)))

(def-fns _ $ (erased ctring-allp : (erased (List (Step)) cp) (erased (Ctree) t) (erased (List (Col)) pre) (subterm erased (CtRing cp t pre) r)
    -> (erased (CtAllP (MkPred (List (Step)) cp CpColR) t pre) a))
  (let-match erased r (CRL _ lf _ et e0 ra c)
    ((CRE _ _) (CAPE _ pre))
    ((CRN _ t1 t2 t3 _ r1 r2 r3)
      (CAPN _ t1 t2 t3 pre (ctring-allp cp t1 (Cons _ (C1) pre) r1) (ctring-allp cp t2 (Cons _ (C2) pre) r2) (ctring-allp cp t3 (Cons _ (C3) pre) r3))))
  (let-match erased c (MkCpCol _ _ _ _ _ _ _ cs _ _ _ _ _ tr))
  (let ((erased ct) (erased cr) (erased sn)) (trace-ctr cs et e0 tr))
  (CAPL _ lf pre et ct ra cr (MkHolds (List (Step)) cp CpColR ct (MkCpColR cp et ct e0 sn c))))
