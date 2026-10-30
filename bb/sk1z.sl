(def-adts
  ((Pa : ((List (Sy)) o) ((Pk) pk) ((Nat) pc) ((Pk) k) ((Nat) a) ((List (Sy)) o2) ((Pk) pk2) ((Nat) pc2) -> Type)
    enum
    (many PaZ : (erased (List (Sy)) o) (erased (Pk) pk k) (erased (Nat) pc) -> (Pa o pk pc k (Zero) o pk pc))
    (many PaS : (erased (List (Sy)) o) (erased (Pk) k) (erased (Nat) pc a s) (erased (Add pc a s) ad) -> (Pa o k pc k a o k s))
    (many PaF : (erased (List (Sy)) o o2 cs) (erased (Pk) pk k) (erased (Nat) pc a1) (erased (KNe pk k) ne) (erased (Push pk pc (Nil (Sy)) cs) pu)
       (erased (Cat (Sy) o cs o2) c) -> (Pa o pk pc k (Succ a1) o2 k (Succ a1)))))

(def-adts
  ((Nb : ((Sy) s) -> Type)
    enum
    (many NbF : (erased (Fx) f) -> (Nb (YF f)))
    (many NbC : -> (Nb (YC)))))

(def-fns _ $ (erased nb-nk : (erased (Pk) k) (erased (Sy) s) (erased (List (Sy)) w) (erased (Nb s) nb) -> (erased (NotK k (Cons (Sy) s w)) nk))
  (match erased nb _ ((NbF f) (NKF k f w)) ((NbC) (NKC k w))))

(def-adts
  ((Fe : ((List (Sy)) o) ((Pk) pk) ((Nat) pc) ((Sy) s) ((List (Sy)) o2) -> Type)
    enum
    (many MkFe : (erased (List (Sy)) o cs o1 o2) (erased (Pk) pk) (erased (Nat) pc) (erased (Sy) s) (erased (Push pk pc (Nil (Sy)) cs) pu)
       (erased (Cat (Sy) o cs o1) c1) (erased (Cat (Sy) o1 (Cons (Sy) s (Nil (Sy))) o2) c2) (erased (Nb s) nb) -> (Fe o pk pc s o2))))

(def-fns _ $ (erased cat-one : (erased (List (Sy)) o o2 w W) (erased (Sy) s) (erased (Cat (Sy) o (Cons (Sy) s (Nil (Sy))) o2) c1) (erased (Cat (Sy) o2 w W) c2)
    -> (erased (Cat (Sy) o (Cons (Sy) s w) W) c))
  (let ((erased wy) (erased c3) (erased c4)) (cat-assoc (Sy) o (Cons (Sy) s (Nil (Sy))) o2 w W c1 c2))
  (let-match erased c3 (CatC _ _ _ _ wy1 c5))
  (let-match erased c5 (CatN _ _))
  c4)

(def-fns _ $ (erased fe-back : (erased (List (Sy)) o o2 w W) (erased (Pk) pk) (erased (Nat) pc) (erased (Sy) s) (erased (Fe o pk pc s o2) fe) (erased (Cat (Sy) o2 w W) c)
    -> (erased (List (Sy)) w2) (erased (Push pk pc (Cons (Sy) s w) w2) pu) (erased (Cat (Sy) o w2 W) c2))
  (let-match erased fe (MkFe _ cs o1 _ _ _ _ pu c1 c2 nb))
  (let ((erased c3)) (cat-one o1 o2 w W s c2 c))
  (match erased pu _
    ((PuZ _ _) (let-match erased (cat-nil (Sy) o o1 c1) (Refl _ _)) (values (Cons (Sy) s w) (PuZ pk _) c3))
    ((PuC _ pc1 _ _) (values (Cons (Sy) (YW pk (MkAm (BFalse) (Succ pc1))) (Cons (Sy) s w)) (PuC pk pc1 (Cons (Sy) s w) (nb-nk pk s w nb)) (cat-one o o1 (Cons (Sy) s w) W _ c1 c3)))))

(def-fns _ $ (erased pw-nk : (erased (Pk) pk k) (erased (Nat) a1) (erased (List (Sy)) w w1) (erased (Push k (Succ a1) w w1) pu) (erased (KNe pk k) ne) -> (erased (NotK pk w1) nk))
  (match erased pu _ ((PuM _ _ _ s t0 _) (NKW pk k _ t0 ne)) ((PuC _ _ _ _) (NKW pk k _ w ne))))

(def-fns _ $ (erased pa-back : (erased (List (Sy)) o o2 w w1 w3 W) (erased (Pk) pk k pk2) (erased (Nat) pc a pc2) (erased (Pa o pk pc k a o2 pk2 pc2) pa)
    (erased (Push pk2 pc2 w w3) p3) (erased (Cat (Sy) o2 w3 W) c3) (erased (Push k a w w1) p1)
    -> (erased (List (Sy)) w2) (erased (Push pk pc w1 w2) p2) (erased (Cat (Sy) o w2 W) c2))
  (match erased pa _
    ((PaZ _ _ _ _) (let-match erased p1 (PuZ _ _)) (values w3 p3 c3))
    ((PaS _ _ _ _ s ad)
      (let ((erased w2) (erased q)) (push-ex k pc w1))
      (let-match erased (push-fn k s w w2 w3 (push-comp k a pc s w w1 w2 p1 q ad) p3) (Refl _ _))
      (values w2 q c3))
    ((PaF _ _ cs _ _ _ a1 ne pu c)
      (let-match erased (push-fn k a w w1 w3 p1 p3) (Refl _ _))
      (match erased pu _
        ((PuZ _ _) (let-match erased (cat-nil (Sy) o o2 c) (Refl _ _)) (values w1 (PuZ pk w1) c3))
        ((PuC _ pc1 _ _)
          (let ((erased wy) (erased c4) (erased c5)) (cat-assoc (Sy) o cs o2 w1 W c c3))
          (let-match erased c4 (CatC _ _ _ _ wy1 c6))
          (let-match erased c6 (CatN _ _))
          (values (Cons (Sy) (YW pk (MkAm (BFalse) (Succ pc1))) w1) (PuC pk pc1 w1 (pw-nk pk k a1 w w1 p1 ne)) c5))))))

(def-adts
  ((Fw : ((List (Sy)) o0) ((Nat) xs0 n0) ((List (Sy)) u0) ((List (Sy)) o) ((Pk) pk) ((Nat) pc) ((Nat) xs n) ((List (Sy)) u) -> Type)
    enum
    (many FwN : (erased (List (Sy)) o) (erased (Nat) xs n) (erased (List (Sy)) u) -> (Fw o xs n u o (KX) (Zero) xs n u))
    (many FwX : (erased (List (Sy)) o0 u0 o u) (erased (Nat) xs0 n0 pc xs n v xs2) (erased (Pk) pk)
       (erased (Fw o0 xs0 n0 u0 o pk pc xs n (Cons (Sy) (YW (KX) (MkAm (BFalse) v)) u)) f) (erased (Add xs v xs2) a) -> (Fw o0 xs0 n0 u0 o pk pc xs2 n u))
    (many FwD : (erased (List (Sy)) o0 u0 o o1 o2 u) (erased (Nat) xs0 n0 pc pc1 xs n) (erased (Pk) pk pk1)
       (erased (Fw o0 xs0 n0 u0 o pk pc xs n (Cons (Sy) iD u)) f) (erased (Pa o pk pc (KX) xs o1 pk1 pc1) pa) (erased (Fe o1 pk1 pc1 iD o2) fe)
       -> (Fw o0 xs0 n0 u0 o2 (KX) (Zero) (Zero) n u))
    (many FwC : (erased (List (Sy)) o0 u0 o o1 o2 o3 u) (erased (Nat) xs0 n0 pc pc1 pc3 xs n d n2 n4) (erased (Pk) pk pk1 pk3)
       (erased (Fw o0 xs0 n0 u0 o pk pc xs n (Cons (Sy) (YC) u)) f) (erased (Add n d xs) a) (erased (Add n n n2) a2) (erased (Add n2 n2 n4) a4)
       (erased (Pa o pk pc (KX) d o1 pk1 pc1) pa) (erased (Fe o1 pk1 pc1 (YC) o2) fe) (erased (Pa o2 (KX) (Zero) (KX) n2 o3 pk3 pc3) pb)
       -> (Fw o0 xs0 n0 u0 o3 pk3 pc3 (Zero) n4 u))
    (many FwG : (erased (List (Sy)) o0 u0 o o1 o2 u) (erased (Nat) xs0 n0 pc pc1 pc2 xs n g) (erased (Pk) pk pk1 pk2)
       (erased (Fw o0 xs0 n0 u0 o pk pc xs n (Cons (Sy) (YW (KG) (MkAm (BFalse) g)) u)) f) (erased (Pa o pk pc (KX) xs o1 pk1 pc1) pa)
       (erased (Pa o1 pk1 pc1 (KG) g o2 pk2 pc2) pb) -> (Fw o0 xs0 n0 u0 o2 pk2 pc2 (Zero) n u))))

(def-fns _ $ (erased fw-swin : (erased (List (Sy)) o0 u0 o u w w2 W) (erased (Nat) xs0 n0 pc xs n m) (erased (Pk) pk)
    (subterm erased (Fw o0 xs0 n0 u0 o pk pc xs n u) f) (erased (Swin xs n u w m) s) (erased (Push pk pc w w2) p) (erased (Cat (Sy) o w2 W) c)
    -> (erased (List (Sy)) W2) (erased (Cat (Sy) o0 W2 W) c2) (erased (Swin xs0 n0 u0 W2 m) s2))
  (match erased f _
    ((FwN _ _ _ _) (let-match erased p (PuZ _ _)) (values w c s))
    ((FwX _ _ _ _ _ _ _ xss _ v _ _ f1 a)
      (fw-swin o0 u0 o _ w w2 W xs0 n0 pc xss n m pk f1 (SwX xss n v xs m u w a s) p c))
    ((FwD _ _ oo o1 _ _ _ _ pcc pc1 xss _ pkk pk1 f1 pa fe)
      (let-match erased p (PuZ _ _))
      (let ((erased w1) (erased q1)) (push-ex (KX) xss (Cons (Sy) iD w)))
      (let ((erased w3) (erased q3) (erased c3)) (fe-back o1 o w W pk1 pc1 iD fe c))
      (let ((erased w4) (erased q4) (erased c4)) (pa-back oo o1 _ w1 w3 W pkk (KX) pk1 pcc xss pc1 pa q3 c3 q1))
      (fw-swin o0 u0 oo _ w1 w4 W xs0 n0 pcc xss n m pkk f1 (SwD xss n m u w w1 s q1) q4 c4))
    ((FwC _ _ oo o1 o2 _ _ _ _ pcc pc1 _ xss nn d n2 _ pkk pk1 _ f1 a a2 a4 pa fe pb)
      (let ((erased wq) (erased pu)) (push-ex (KX) n2 w))
      (let ((erased w5) (erased q5) (erased c5)) (pa-back o2 o w wq w2 W (KX) (KX) pk (Zero) n2 pc pb p c pu))
      (let-match erased q5 (PuZ _ _))
      (let ((erased w6) (erased q6) (erased c6)) (fe-back o1 o2 wq W pk1 pc1 (YC) fe c5))
      (let ((erased w1) (erased pu2)) (push-ex (KX) d (Cons (Sy) (YC) wq)))
      (let ((erased w7) (erased q7) (erased c7)) (pa-back oo o1 _ w1 w6 W pkk (KX) pk1 pcc d pc1 pa q6 c6 pu2))
      (fw-swin o0 u0 oo _ w1 w7 W xs0 n0 pcc xss nn m pkk f1 (SwC xss nn d n2 n m u w wq w1 a a2 a4 s pu pu2) q7 c7))
    ((FwG _ _ oo o1 _ _ _ _ pcc pc1 _ xss _ g pkk pk1 _ f1 pa pb)
      (let ((erased wg) (erased pg)) (push-ex (KG) g w))
      (let ((erased w5) (erased q5) (erased c5)) (pa-back o1 o w wg w2 W pk1 (KG) pk pc1 g pc pb p c pg))
      (let ((erased w1) (erased px)) (push-ex (KX) xss wg))
      (let ((erased w6) (erased q6) (erased c6)) (pa-back oo o1 wg w1 w5 W pkk (KX) pk1 pcc xss pc1 pa q5 c5 px))
      (fw-swin o0 u0 oo _ w1 w6 W xs0 n0 pcc xss n m pkk f1 (SwG xss n g m u w wg w1 s pg px) q6 c6))))

(def-adts
  ((Rv : ((List (Sy)) zs e) -> Type)
    enum
    (many RvN : -> (Rv (Nil (Sy)) (Nil (Sy))))
    (many RvS : (erased (List (Sy)) zs e e2) (erased (Sy) x) (erased (Rv zs e) r) (erased (Cat (Sy) e (Cons (Sy) x (Nil (Sy))) e2) c) -> (Rv (Cons (Sy) x zs) e2))))

(def-adts
  ((Nwf : ((List (Sy)) zs) -> Type)
    enum
    (many NwN : -> (Nwf (Nil (Sy))))
    (many NwB : (erased (Sy) s) (erased (List (Sy)) zs) (erased (Nb s) nb) -> (Nwf (Cons (Sy) s zs)))))

(def-adts
  ((Sc : ((List (Sy)) zs o) ((Pk) pk) ((Nat) pc) -> Type)
    enum
    (many ScZ : (erased (List (Sy)) zs o) (erased (Pk) pk) (erased (Rv zs o) r) (erased (Nwf zs) nw) -> (Sc zs o pk (Zero)))
    (many ScP : (erased (List (Sy)) zs o) (erased (Pk) pk) (erased (Nat) c) (erased (Rv zs o) r)
       -> (Sc (Cons (Sy) (YW pk (MkAm (BFalse) (Succ c))) zs) o pk (Succ c)))))

(def-fns _ $ (erased cat-nr : (erased Type A) (subterm erased (List A) x) -> (erased (Cat A x (Nil A) x) c))
  (let-match erased x (Cons _ a x1) ((Nil _) (CatN A (Nil A))))
  (CatC A a x1 (Nil A) x1 (cat-nr A x1)))

(def-fns _ $ (erased rv-snoc : (erased (List (Sy)) zs e) (erased (Sy) x) (erased (Rv zs e) r) -> (erased (List (Sy)) e2) (erased (Cat (Sy) e (Cons (Sy) x (Nil (Sy))) e2) c) (erased (Rv (Cons (Sy) x zs) e2) r2))
  (let ((erased e2) (erased c)) (cat-ex (Sy) e (Cons (Sy) x (Nil (Sy)))))
  (values e2 c (RvS zs e e2 x r c)))

(def-fns _ $ (erased sc-merge : (erased (List (Sy)) zs o) (erased (Pk) pk k) (erased (Nat) pc c a s) (erased (Sc (Cons (Sy) (YW k (MkAm (BFalse) c)) zs) o pk pc) sc)
    (erased (Add c a s) ad) (erased (Lt (Zero) s) ps)
    -> (erased (Pa o pk pc k a o k s) pa) (erased (Sc (Cons (Sy) (YW k (MkAm (BFalse) s)) zs) o k s) sc2))
  (let-match erased sc (ScP _ _ _ c1 r) (absurd (ScZ _ _ _ _ nw) (let-match erased nw (NwB _ _ nb)) (match erased nb _)))
  (let-match erased ps (LtZ s1))
  (values (PaS o k c a s ad) (ScP zs o k s1 r)))

(def-fns _ $ (erased sc-diff : (erased (List (Sy)) zs o) (erased (Pk) pk k k2) (erased (Nat) pc c a1) (erased (Sc (Cons (Sy) (YW k2 (MkAm (BFalse) c)) zs) o pk pc) sc)
    (erased (KNe k2 k) ne)
    -> (erased (List (Sy)) o2) (erased (Pa o pk pc k (Succ a1) o2 k (Succ a1)) pa)
    (erased (Sc (Cons (Sy) (YW k (MkAm (BFalse) (Succ a1))) (Cons (Sy) (YW k2 (MkAm (BFalse) c)) zs)) o2 k (Succ a1)) sc2))
  (let-match erased sc (ScP _ _ _ c1 r) (absurd (ScZ _ _ _ _ nw) (let-match erased nw (NwB _ _ nb)) (match erased nb _)))
  (let ((erased o2) (erased cc) (erased r2)) (rv-snoc zs o (YW k2 (MkAm (BFalse) c)) r))
  (values o2 (PaF o o2 _ k2 k c a1 ne (PuC k2 c1 (Nil (Sy)) (NKN k2)) cc) (ScP _ o2 k a1 r2)))

(def-fns _ $ (erased sc-new : (erased (List (Sy)) zs o) (erased (Pk) pk k) (erased (Nat) pc a1) (erased (Sc zs o pk pc) sc) (erased (Nwf zs) nw)
    -> (erased (Pa o pk pc k (Succ a1) o k (Succ a1)) pa) (erased (Sc (Cons (Sy) (YW k (MkAm (BFalse) (Succ a1))) zs) o k (Succ a1)) sc2))
  (let-match erased sc (ScZ _ _ _ r _)
    (absurd (ScP _ _ _ _ _) (let-match erased nw (NwB _ _ nb)) (match erased nb _)))
  (values (match erased (pk-cmp pk k) _
            ((PkEq _) (PaS o k (Zero) (Succ a1) (Succ a1) (AddZero (Succ a1))))
            ((PkNe _ _ ne) (PaF o o _ pk k (Zero) a1 ne (PuZ pk (Nil (Sy))) (cat-nr (Sy) o))))
    (ScP zs o k a1 r)))

(def-fns _ $ (erased sc-emit : (erased (List (Sy)) zs o) (erased (Pk) pk) (erased (Nat) pc) (erased (Sy) s) (erased (Sc zs o pk pc) sc) (erased (Nb s) nb)
    -> (erased (List (Sy)) o2) (erased (Fe o pk pc s o2) fe) (erased (Sc (Cons (Sy) s zs) o2 (KX) (Zero)) sc2))
  (match erased sc _
    ((ScZ _ _ _ r _)
      (let ((erased o2) (erased c2) (erased r2)) (rv-snoc zs o s r))
      (values o2 (MkFe o _ o o2 pk (Zero) s (PuZ pk (Nil (Sy))) (cat-nr (Sy) o) c2 nb) (ScZ _ o2 (KX) r2 (NwB s zs nb))))
    ((ScP zs0 _ _ c1 r)
      (let ((erased o1) (erased c1a) (erased r1)) (rv-snoc zs0 o (YW pk (MkAm (BFalse) (Succ c1))) r))
      (let ((erased o2) (erased c2) (erased r2)) (rv-snoc zs o1 s r1))
      (values o2 (MkFe o _ o1 o2 pk pc s (PuC pk c1 (Nil (Sy)) (NKN pk)) c1a c2 nb) (ScZ _ o2 (KX) r2 (NwB s zs nb))))))

(def-fns _ $ (erased sc-end : (erased (List (Sy)) zs o) (erased (Pk) pk) (erased (Nat) pc) (erased (Sc zs o pk pc) sc)
    -> (erased (List (Sy)) W cs) (erased (Push pk pc (Nil (Sy)) cs) pu) (erased (Cat (Sy) o cs W) c) (erased (Rv zs W) r))
  (match erased sc _
    ((ScZ _ _ _ r _) (values o (Nil (Sy)) (PuZ pk (Nil (Sy))) (cat-nr (Sy) o) r))
    ((ScP zs0 _ _ c1 r)
      (let ((erased o1) (erased c1a) (erased r1)) (rv-snoc zs0 o (YW pk (MkAm (BFalse) (Succ c1))) r))
      (values o1 (Cons (Sy) (YW pk (MkAm (BFalse) (Succ c1))) (Nil (Sy))) (PuC pk c1 (Nil (Sy)) (NKN pk)) c1a r1))))
