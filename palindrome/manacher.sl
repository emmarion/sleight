(def-fns _ $ many snoc :
    (subterm many (List (Nat)) l) (many (Nat) x) -> (many (List (Nat)) r) (erased (Concat (Nat) l (Cons (Nat) x (Nil (Nat))) r) c)
  (match many l _
    ((Nil a) (values (Cons (Nat) x (Nil (Nat))) (CatNil (Nat) (Cons (Nat) x (Nil (Nat))))))
    ((Cons a y ys)
      (let (many r1) (erased c1) (snoc ys x))
      (values (Cons (Nat) y r1) (CatCons (Nat) y ys (Cons (Nat) x (Nil (Nat))) r1 c1)))))

(def-fns _ $ erased concat-shift :
    (erased Type A) (erased (List A) p) (erased A e) (erased (List A) q) (erased (List A) w)
    (erased (List A) pe) (erased (Concat A p (Cons A e (Nil A)) pe) snocp)
    (subterm erased (Concat A p (Cons A e q) w) cp) ->
    (erased (Concat A pe q w) result)
  (match erased cp _
    ((CatNil a ys)
      (match erased snocp _
        ((CatNil a2 ys2) (CatCons A e (Nil A) q q (CatNil A q)))))
    ((CatCons a p0 p1 ys w1 cp1)
      (match erased snocp _
        ((CatCons a2 p02 p12 ys2 pe1 snocp1)
          (let (erased result1) (concat-shift A p1 e q w1 pe1 snocp1 cp1))
          (CatCons A p0 pe1 q w1 result1))))))

(def-fns _ $ erased concat-len-eq :
    (erased (List (Nat)) a) (erased (List (Nat)) b) (erased (List (Nat)) c)
    (erased (Nat) ln) (subterm erased (Length (Nat) a ln) lena) (erased (Length (Nat) c ln) lenc)
    (erased (Concat (Nat) a b c) cp) ->
    (erased (Length (Nat) b (Zero)) result)
  (match erased cp _
    ((CatNil a2 ys)
      (match erased lena _
        ((LNil a3) lenc)))
    ((CatCons a2 x0 a1 ys c1 cp1)
      (match erased lena _
        ((LCons a3 x3 rest3 ln1 lena1)
          (match erased lenc _
            ((LCons a4 x4 rest4 ln2 lenc1)
              (concat-len-eq a1 b c1 ln1 lena1 lenc1 cp1))))))))

(def-fns _ $ erased concat-len-diff :
    (erased (List (Nat)) a) (erased (List (Nat)) b) (erased (List (Nat)) c)
    (erased (Nat) la) (erased (Length (Nat) a la) lena)
    (erased (Nat) lc) (erased (Length (Nat) c lc) lenc)
    (subterm erased (Lt la lc) ltp) (erased (Concat (Nat) a b c) cp) ->
    (erased (Nat) lb) (erased (Length (Nat) b (Succ lb)) lenb)
  (match erased cp _
    ((CatNil a2 ys)
      (match erased lena _
        ((LNil a3)
          (match erased ltp _
            ((LtZ b2) (values b2 lenc))))))
    ((CatCons a2 x0 a1 ys c1 cp1)
      (match erased lena _
        ((LCons a3 x3 rest3 la1 lena1)
          (match erased lenc _
            ((LCons a4 x4 rest4 lc1 lenc1)
              (match erased ltp _
                ((LtS la2 lc2 ltp1)
                  (concat-len-diff a1 b c1 la1 lena1 lc1 lenc1 ltp1 cp1))))))))))

(def-fns _ $ erased length-snoc :
    (erased (List (Nat)) a) (erased (Nat) e) (erased (List (Nat)) ae)
    (erased (Nat) la) (subterm erased (Length (Nat) a la) lena) (erased (Concat (Nat) a (Cons (Nat) e (Nil (Nat))) ae) cp) ->
    (erased (Length (Nat) ae (Succ la)) result)
  (match erased lena _
    ((LNil a2)
      (match erased cp _
        ((CatNil a3 ys) (LCons (Nat) e (Nil (Nat)) (Zero) (LNil (Nat))))))
    ((LCons a2 x2 rest2 la1 lena1)
      (match erased cp _
        ((CatCons a3 x0 rest0 ys ae1 cp1)
          (let (erased result1) (length-snoc rest2 e ae1 la1 lena1 cp1))
          (LCons (Nat) x0 ae1 (Succ la1) result1))))))

(def-adts
  (CheckDec : ((List (Nat)) front) ((List (Nat)) remaining) ((Nat) lfa) -> Type
    enum
    (many CheckYes : (erased (List (Nat)) front) (erased (List (Nat)) remaining) (erased (Nat) lfa)
        (erased (List (Nat)) consumed) (erased (Concat (Nat) consumed remaining front) cp)
        (erased (Length (Nat) consumed lfa) lenc) (erased (Palindrome (Nat) consumed) pal) ->
       (CheckDec front remaining lfa))
    (many CheckNo : (erased (List (Nat)) front) (erased (List (Nat)) remaining) (erased (Nat) lfa)
        (erased (List (Nat)) consumed) (erased (Concat (Nat) consumed remaining front) cp)
        (erased (Length (Nat) consumed lfa) lenc) (erased (NotPalindrome consumed) np) ->
       (CheckDec front remaining lfa))))

(def-fns _ $ many check :
    (many (List (Nat)) front) (erased (Nat) lf) (erased (Length (Nat) front lf) lenF)
    (subterm many (List (Nat)) fast) (erased (Nat) lfa) (erased (Length (Nat) fast lfa) lenFa)
    (erased (Lt lfa (Succ lf)) bnd) ->
    (many (List (Nat)) remaining) (many (CheckDec front remaining lfa) d)
  (match many fast _
    ((Nil a)
      (match erased lenFa _
        ((LNil a2)
          (values front
            (CheckYes front front (Zero) (Nil (Nat)) (CatNil (Nat) front) (LNil (Nat)) (PalNil (Nat)))))))
    ((Cons a fx fast1)
      (match many fast1 _
        ((Nil a2)
          (match erased lenFa _
            ((LCons a3 x3 rest3 lfa1 lenFa1)
              (match erased lenFa1 _
                ((LNil a4)
                  (match erased bnd _
                    ((LtS la2 lc2 ltp1)
                      (match erased ltp1 _
                        ((LtZ lf1b)
                      (match erased lenF _
                        ((LCons a5 x5 rest5 lf1 lenF1)
                          (match many front _
                            ((Cons a6 c front1)
                              (values front1
                                (CheckYes front front1 (Succ (Zero)) (Cons (Nat) c (Nil (Nat)))
                                  (CatCons (Nat) c (Nil (Nat)) front1 front1 (CatNil (Nat) front1))
                                  (LCons (Nat) c (Nil (Nat)) (Zero) (LNil (Nat)))
                                  (PalOne (Nat) c))))))))))))))))
        ((Cons a2 fx2 fast2)
          (match erased lenFa _
            ((LCons a3 x3 rest3 lfa1 lenFa1)
              (match erased lenFa1 _
                ((LCons a4 x4 rest4 lfa2 lenFa2)
                  (match erased bnd _
                    ((LtS la2 lc2 ltp1a)
                      (match erased ltp1a _
                        ((LtS la3 lc3 ltp2)
                          (match erased lenF _
                            ((LCons a5 x5 rest5 lf1 lenF1)
                              (match many front _
                                ((Cons a6 x front1)
                                  (let (erased bnd2) (lt-weaken lfa2 lf1 ltp2))
                                  (let (many remaining1) (many d1) (check front1 lf1 lenF1 fast2 lfa2 lenFa2 bnd2))
                                  (match many d1 _
                                    ((CheckYes a7 r7 lfa7 consumed1 cp1 lenc1 pal1)
                                      (let (erased lb) (erased lenRem) (concat-len-diff consumed1 remaining1 front1 lfa2 lenc1 lf1 lenF1 ltp2 cp1))
                                      (match erased lenRem _
                                        ((LCons a9 x9 rest9 lb2 lenb2)
                                      (match many remaining1 _
                                        ((Cons a8 y remaining2)
                                          (let (erased consumed1y) (erased snocp) (snoc consumed1 y))
                                          (let (erased lenc1y) (length-snoc consumed1 y consumed1y lfa2 lenc1 snocp))
                                          (let (erased cpw) (concat-shift (Nat) consumed1 y remaining2 front1 consumed1y snocp cp1))
                                          (match many (nat-cmp x y) _
                                            ((CEq t8 r8 xx8)
                                              (values remaining2
                                                (CheckYes front remaining2 (Succ (Succ lfa2)) (Cons (Nat) x consumed1y)
                                                  (CatCons (Nat) x consumed1y remaining2 front1 cpw)
                                                  (LCons (Nat) x consumed1y (Succ lfa2) lenc1y)
                                                  (PalWrap (Nat) x consumed1 consumed1y pal1 snocp))))
                                            ((CLt t8 r8 xx8 yy8 ltp8)
                                              (values remaining2
                                                (CheckNo front remaining2 (Succ (Succ lfa2)) (Cons (Nat) x consumed1y)
                                                  (CatCons (Nat) x consumed1y remaining2 front1 cpw)
                                                  (LCons (Nat) x consumed1y (Succ lfa2) lenc1y)
                                                  (NotPalEnds x y consumed1 consumed1y snocp (ApartLt x y ltp8)))))
                                            ((CGt t8 r8 xx8 yy8 gtp8)
                                              (values remaining2
                                                (CheckNo front remaining2 (Succ (Succ lfa2)) (Cons (Nat) x consumed1y)
                                                  (CatCons (Nat) x consumed1y remaining2 front1 cpw)
                                                  (LCons (Nat) x consumed1y (Succ lfa2) lenc1y)
                                                  (NotPalEnds x y consumed1 consumed1y snocp (ApartGt x y gtp8)))))))))))
                                    ((CheckNo a7 r7 lfa7 consumed1 cp1 lenc1 np1)
                                      (let (erased lb) (erased lenRem) (concat-len-diff consumed1 remaining1 front1 lfa2 lenc1 lf1 lenF1 ltp2 cp1))
                                      (match erased lenRem _
                                        ((LCons a9 x9 rest9 lb2 lenb2)
                                      (match many remaining1 _
                                        ((Cons a8 y remaining2)
                                          (let (erased consumed1y) (erased snocp) (snoc consumed1 y))
                                          (let (erased lenc1y) (length-snoc consumed1 y consumed1y lfa2 lenc1 snocp))
                                          (let (erased cpw) (concat-shift (Nat) consumed1 y remaining2 front1 consumed1y snocp cp1))
                                          (match many (nat-cmp x y) _
                                            ((CEq t8 r8 xx8)
                                              (values remaining2
                                                (CheckNo front remaining2 (Succ (Succ lfa2)) (Cons (Nat) x consumed1y)
                                                  (CatCons (Nat) x consumed1y remaining2 front1 cpw)
                                                  (LCons (Nat) x consumed1y (Succ lfa2) lenc1y)
                                                  (NotPalInner x consumed1 consumed1y snocp np1))))
                                            ((CLt t8 r8 xx8 yy8 ltp8)
                                              (values remaining2
                                                (CheckNo front remaining2 (Succ (Succ lfa2)) (Cons (Nat) x consumed1y)
                                                  (CatCons (Nat) x consumed1y remaining2 front1 cpw)
                                                  (LCons (Nat) x consumed1y (Succ lfa2) lenc1y)
                                                  (NotPalEnds x y consumed1 consumed1y snocp (ApartLt x y ltp8)))))
                                            ((CGt t8 r8 xx8 yy8 gtp8)
                                              (values remaining2
                                                (CheckNo front remaining2 (Succ (Succ lfa2)) (Cons (Nat) x consumed1y)
                                                  (CatCons (Nat) x consumed1y remaining2 front1 cpw)
                                                  (LCons (Nat) x consumed1y (Succ lfa2) lenc1y)
                                                  (NotPalEnds x y consumed1 consumed1y snocp (ApartGt x y gtp8)))))))))))))))))))))))))))))

(def-fns _ $ many list-len : (subterm many (List (Nat)) xs) -> (many (Nat) n) (erased (Length (Nat) xs n) p)
  (match many xs _
    ((Nil a) (values (Zero) (LNil (Nat))))
    ((Cons a x rest)
      (let (many n1) (erased p1) (list-len rest))
      (values (Succ n1) (LCons (Nat) x rest n1 p1)))))

(def-fns _ $ erased concat-nil-eq :
    (erased (List (Nat)) a) (erased (List (Nat)) c) (subterm erased (Concat (Nat) a (Nil (Nat)) c) cp) ->
    (erased (Eq (List (Nat)) a c) e)
  (match erased cp _
    ((CatNil a2 ys) (Refl (List (Nat)) (Nil (Nat))))
    ((CatCons a2 x0 rest0 ys c1 cp1)
      (let (erased e1) (concat-nil-eq rest0 c1 cp1))
      (match erased e1 _
        ((Refl t r) (Refl (List (Nat)) (Cons (Nat) x0 rest0)))))))

(def-adts
  (PalDec2 : ((List (Nat)) w) -> Type
    enum
    (many PD2Yes : (erased (List (Nat)) w) (erased (Palindrome (Nat) w) pal) -> (PalDec2 w))
    (many PD2No : (erased (List (Nat)) w) (erased (NotPalindrome w) np) -> (PalDec2 w))))

(def-fns _ $ many decide-palindrome-fast : (many (List (Nat)) w) -> (many (PalDec2 w) d)
  (let (many n) (erased lenw) (list-len w))
  (let (erased bnd) (lt-succ n))
  (let (many remaining) (many dc) (check w n lenw w n lenw bnd))
  (match many dc _
    ((CheckYes a1 a2 a3 consumed cp lenc pal)
      (let (erased lenrem) (concat-len-eq consumed remaining w n lenc lenw cp))
      (match erased lenrem _
        ((LNil a7)
          (let (erased eqp) (concat-nil-eq consumed w cp))
          (match erased eqp _
            ((Refl t r) (PD2Yes w pal))))))
    ((CheckNo a1 a2 a3 consumed cp lenc np)
      (let (erased lenrem) (concat-len-eq consumed remaining w n lenc lenw cp))
      (match erased lenrem _
        ((LNil a7)
          (let (erased eqp) (concat-nil-eq consumed w cp))
          (match erased eqp _
            ((Refl t r) (PD2No w np))))))))

