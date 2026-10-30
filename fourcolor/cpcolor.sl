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
