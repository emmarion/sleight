; needs: palindrome_relations palindrome
; expect: (Cons 0 (Cons 1 (Cons 3 (Cons 4 (Cons 3 (Nil))))))

(def-adts
  (Mirror : ((List (Nat)) l) ((List (Nat)) r) ((Nat) k) -> Type
    enum
    (many MirrorZ : (erased (List (Nat)) l) (erased (List (Nat)) r) -> (Mirror l r (Zero)))
    (many MirrorS : (erased (Nat) x) (erased (List (Nat)) l) (erased (List (Nat)) r)
        (erased (Nat) k) (erased (Mirror l r k) m) ->
       (Mirror (Cons (Nat) x l) (Cons (Nat) x r) (Succ k)))))

(def-adts
  (Drop : ((Nat) n) ((List (Nat)) xs) ((List (Nat)) ys) -> Type
    enum
    (many DropZero : (erased (List (Nat)) xs) -> (Drop (Zero) xs xs))
    (many DropSucc : (erased (Nat) n) (erased (Nat) x) (erased (List (Nat)) xs)
        (erased (List (Nat)) ys) (erased (Drop n xs ys) d) ->
       (Drop (Succ n) (Cons (Nat) x xs) ys))))

(def-adts
  (Stop : ((List (Nat)) l) ((List (Nat)) r) -> Type
    enum
    (many StopL : (erased (List (Nat)) r) -> (Stop (Nil (Nat)) r))
    (many StopR : (erased (List (Nat)) l) -> (Stop l (Nil (Nat))))
    (many StopNe : (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) l)
        (erased (List (Nat)) r) (erased (NatApart x y) d) ->
       (Stop (Cons (Nat) x l) (Cons (Nat) y r)))))

(def-fns _ $ many expand : (subterm many (List (Nat)) l) (many (List (Nat)) r) ->
    (many (Nat) k) (erased (Mirror l r k) m)
    (erased (List (Nat)) l2) (erased (List (Nat)) r2)
    (erased (Drop k l l2) dl) (erased (Drop k r r2) dr) (erased (Stop l2 r2) st)
  (match many l _
    ((Nil a)
      (values (Zero) (MirrorZ l r) l r (DropZero l) (DropZero r) (StopL r)))
    ((Cons a x l1)
      (match many r _
        ((Nil b)
          (values (Zero) (MirrorZ l r) l r (DropZero l) (DropZero r) (StopR l)))
        ((Cons b y r1)
          (match many (nat-cmp x y) _
            ((CEq t rr x0)
              (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr)
                   (erased st) (expand l1 r1))
              (values (Succ k) (MirrorS x l1 r1 k m) l2 r2
                      (DropSucc k x l1 l2 dl) (DropSucc k y r1 r2 dr) st))
            ((CLt t rr a0 b0 p0)
              (values (Zero) (MirrorZ l r) l r (DropZero l) (DropZero r)
                      (StopNe x y l1 r1 (ApartLt x y p0))))
            ((CGt t rr a0 b0 p0)
              (values (Zero) (MirrorZ l r) l r (DropZero l) (DropZero r)
                      (StopNe x y l1 r1 (ApartGt x y p0))))))))))

(def-adts
  (RevCat : ((List (Nat)) l) ((List (Nat)) r) ((List (Nat)) xs) -> Type
    enum
    (many RevFlat : (erased (List (Nat)) xs) -> (RevCat (Nil (Nat)) xs xs))
    (many RevStep : (erased (Nat) x) (erased (List (Nat)) l) (erased (List (Nat)) r)
        (erased (List (Nat)) xs) (erased (RevCat l (Cons (Nat) x r) xs) p) ->
       (RevCat (Cons (Nat) x l) r xs))))

(def-fns _ $ erased snoc : (subterm erased (List (Nat)) xs) (erased (Nat) y)
    (erased (Nat) n) (erased (Length (Nat) xs n) ln) ->
    (erased (List (Nat)) zs)
    (erased (Concat (Nat) xs (Cons (Nat) y (Nil (Nat))) zs) c)
    (erased (Length (Nat) zs (Succ n)) lz)
  (match erased xs _
    ((Nil a)
      (match erased ln _
        ((LNil b)
          (values (Cons (Nat) y (Nil (Nat)))
                  (CatNil (Nat) (Cons (Nat) y (Nil (Nat))))
                  (LCons (Nat) y (Nil (Nat)) (Zero) (LNil (Nat)))))))
    ((Cons a hd tl)
      (match erased ln _
        ((LCons b x1 r1 n1 ln1)
          (let (erased zs) (erased c) (erased lz) (snoc tl y n1 ln1))
          (values (Cons (Nat) hd zs)
                  (CatCons (Nat) hd tl (Cons (Nat) y (Nil (Nat))) zs c)
                  (LCons (Nat) hd zs (Succ n1) lz)))))))

(def-fns _ $ erased snoc-shift : (erased (List (Nat)) core) (erased (Nat) y)
    (erased (List (Nat)) ys) (erased (List (Nat)) src) (erased (List (Nat)) cs)
    (subterm erased (Concat (Nat) core (Cons (Nat) y ys) src) p)
    (erased (Concat (Nat) core (Cons (Nat) y (Nil (Nat))) cs) q) ->
    (erased (Concat (Nat) cs ys src) r)
  (match erased p _
    ((CatNil a1 ys1)
      (match erased q _
        ((CatNil a2 ys2)
          (CatCons (Nat) y (Nil (Nat)) ys ys (CatNil (Nat) ys)))))
    ((CatCons a1 h1 t1 ys1 zs1 p1)
      (match erased q _
        ((CatCons a2 h2 t2 ys2 cs1 q1)
          (CatCons (Nat) h1 cs1 ys zs1 (snoc-shift t1 y ys zs1 cs1 p1 q1)))))))

(def-fns _ $ erased add-shift : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c)
    (erased (Add (Succ a) b c) p) -> (erased (Add a (Succ b) c) q)
  (match erased p _
    ((AddSucc a1 b1 c1 q1) (add-succ-right a1 b c1 q1))))

(def-fns _ $ erased mirror-wrap :
    (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (Nat) k)
    (subterm erased (Mirror l r k) m)
    (erased (List (Nat)) core) (erased (Palindrome (Nat) core) pc)
    (erased (Nat) cn) (erased (Length (Nat) core cn) lc)
    (erased (List (Nat)) src) (erased (Concat (Nat) core r src) cc)
    (erased (List (Nat)) xs) (erased (RevCat l src xs) rc) ->
    (erased (List (Nat)) w) (erased (Palindrome (Nat) w) pw)
    (erased (Nat) n) (erased (Length (Nat) w n) lw)
    (erased (Nat) d) (erased (Double k d) dd) (erased (Add cn d n) ad)
    (erased (List (Nat)) src2) (erased (List (Nat)) r2)
    (erased (Concat (Nat) w r2 src2) cc2)
    (erased (List (Nat)) l2) (erased (RevCat l2 src2 xs) rc2)
  (match erased m _
    ((MirrorZ l0 r0)
      (values core pc cn lc (Zero) (D0) (add-zero-right cn) src r cc l rc))
    ((MirrorS x l1 r1 k1 m1)
      (let (erased cs) (erased csc) (erased csl) (snoc core x cn lc))
      (let (erased cc1) (snoc-shift core x r1 src cs cc csc))
      (let (erased rc1)
        (match erased rc (((RevCat l1 (Cons (Nat) x src) xs) q))
          ((RevStep x0 l0 r0 xs0 p0) p0)))
      (let (erased w) (erased pw) (erased n) (erased lw) (erased d1) (erased dd1)
           (erased ad1) (erased src2) (erased r2) (erased cc2) (erased l2) (erased rc2)
        (mirror-wrap l1 r1 k1 m1
                     (Cons (Nat) x cs) (PalWrap (Nat) x core cs pc csc)
                     (Succ (Succ cn)) (LCons (Nat) x cs (Succ cn) csl)
                     (Cons (Nat) x src)
                     (CatCons (Nat) x cs r1 src cc1)
                     xs rc1))
      (values w pw n lw (Succ (Succ d1)) (DS k1 d1 dd1)
              (add-shift cn (Succ d1) n (add-shift (Succ cn) d1 n ad1))
              src2 r2 cc2 l2 rc2))))

(def-fns _ $ erased concat-take : (erased (List (Nat)) w) (erased (List (Nat)) rem)
    (erased (List (Nat)) src) (subterm erased (Concat (Nat) w rem src) c)
    (erased (Nat) n) (erased (Length (Nat) w n) ln) ->
    (erased (Take (Nat) n src w) tk)
  (match erased c _
    ((CatNil a ys) (match erased ln _ ((LNil b) (TakeZero (Nat) src))))
    ((CatCons a x rest ys zs p)
      (match erased ln _
        ((LCons b x1 r1 n1 ln1)
          (TakeSucc (Nat) n1 x zs rest (concat-take rest rem zs p n1 ln1)))))))

(def-fns _ $ erased revcat-has : (erased (List (Nat)) l) (erased (List (Nat)) src)
    (erased (List (Nat)) xs) (subterm erased (RevCat l src xs) rc)
    (erased (Nat) n) (erased (HasPalindromeOfLength src n) h) ->
    (erased (HasPalindromeOfLength xs n) h2)
  (match erased rc _
    ((RevFlat a) h)
    ((RevStep x l1 r1 xs1 p)
      (revcat-has l1 (Cons (Nat) x src) xs p n (HasThere x src n h)))))

(def-fns _ $ erased add-fn : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c1)
    (erased (Nat) c2) (subterm erased (Add a b c1) p) (erased (Add a b c2) q) ->
    (erased (Eq (Nat) c1 c2) e)
  (match erased p _
    ((AddZero b0) (match erased q _ ((AddZero b1) (Refl (Nat) c1)) (absurd AddSucc)))
    ((AddSucc a1 b1 c0 p1)
      (match erased q _
        (absurd AddZero)
        ((AddSucc a2 b2 c3 q1)
          (match erased (add-fn a1 b c0 c3 p1 q1) _ ((Refl t r) (Refl (Nat) c1))))))))

(def-fns _ $ erased fix-length : (erased (List (Nat)) w) (erased (Nat) cn) (erased (Nat) k)
    (erased (Nat) d0) (erased (Nat) n0) (erased (Nat) drt) (erased (Nat) nrt)
    (erased (Double k d0) dd0) (erased (Add cn d0 n0) ad0)
    (erased (Double k drt) ddrt) (erased (Add cn drt nrt) adrt)
    (erased (Length (Nat) w n0) lw) -> (erased (Length (Nat) w nrt) lw2)
  (match erased (double-fn k d0 drt dd0 ddrt) _
    ((Refl t1 r1)
      (match erased (add-fn cn d0 n0 nrt ad0 adrt) _
        ((Refl t2 r2) lw)))))

(def-adts
  (CentreBound : ((List (Nat)) l) ((List (Nat)) r) ((Nat) cn) ((Nat) n) -> Type
    enum
    (many MkCentreBound : (erased (List (Nat)) l) (erased (List (Nat)) r)
        (erased (Nat) cn) (erased (Nat) n)
        (erased (Nat) k) (erased (List (Nat)) l2) (erased (List (Nat)) r2)
        (erased (Drop k l l2) dl) (erased (Drop k r r2) dr) (erased (Stop l2 r2) st)
        (erased (Nat) dk) (erased (Double k dk) ddk)
        (erased (Nat) lc) (erased (Add cn dk lc) adc) (erased (Lt lc (Succ n)) le) ->
       (CentreBound l r cn n))))

(def-fns _ $ many centre-has :
    (many (List (Nat)) l) (many (List (Nat)) rm) (many (Nat) cn)
    (erased (List (Nat)) core) (erased (Palindrome (Nat) core) pc)
    (erased (Length (Nat) core cn) lc)
    (erased (List (Nat)) src) (erased (Concat (Nat) core rm src) cc)
    (erased (List (Nat)) xs) (erased (RevCat l src xs) rc) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
    (erased (CentreBound l rm cn n) cb)
  (let (many k) (erased m) (erased le) (erased re) (erased dl) (erased dr) (erased st)
       (expand l rm))
  (let (erased w) (erased pw) (erased n0) (erased lw) (erased d0) (erased dd0) (erased ad0)
       (erased src2) (erased r2) (erased cc2) (erased l2) (erased rc2)
       (mirror-wrap l rm k m core pc cn lc src cc xs rc))
  (let (many drt) (erased ddrt) (double k))
  (let (many nrt) (erased adrt) (add cn drt))
  (let (erased lw2) (fix-length w cn k d0 n0 drt nrt dd0 ad0 ddrt adrt lw))
  (values nrt (revcat-has l2 src2 xs rc2 nrt
                (HasHere src2 nrt w (concat-take w r2 src2 cc2 nrt lw2) pw))
              (MkCentreBound l rm cn nrt k le re dl dr st drt ddrt nrt adrt
                             (lt-succ nrt))))

(def-fns _ $ many pick : (erased (List (Nat)) xs)
    (many (Nat) n1) (erased (HasPalindromeOfLength xs n1) h1)
    (many (Nat) n2) (erased (HasPalindromeOfLength xs n2) h2) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
    (erased (Lt n1 (Succ n)) b1) (erased (Lt n2 (Succ n)) b2)
  (match many (nat-cmp n1 n2) _
    ((CLt t r a b p) (values n2 h2 (lt-weaken n1 n2 p) (lt-succ n2)))
    ((CEq t r a) (values n1 h1 (lt-succ n1) (lt-succ n1)))
    ((CGt t r a b p) (values n1 h1 (lt-succ n1) (lt-weaken n2 n1 p)))))

(def-fns _ $ erased drop-succ : (erased (Nat) n) (erased (List (Nat)) l) (erased (Nat) x)
    (erased (List (Nat)) rest) (subterm erased (Drop n l (Cons (Nat) x rest)) d) ->
    (erased (Drop (Succ n) l rest) d2)
  (match erased d _
    ((DropZero a) (DropSucc (Zero) x rest rest (DropZero rest)))
    ((DropSucc n1 y ys zs d1)
      (DropSucc (Succ n1) y ys rest (drop-succ n1 ys x rest d1)))))

(def-fns _ $ erased mirror-extend : (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Nat) k) (subterm erased (Mirror l r k) m) (erased (Nat) x)
    (erased (List (Nat)) l1) (erased (List (Nat)) r1)
    (erased (Drop k l (Cons (Nat) x l1)) dl) (erased (Drop k r (Cons (Nat) x r1)) dr) ->
    (erased (Mirror l r (Succ k)) m2)
  (match erased m _
    ((MirrorZ l0 r0)
      (match erased dl _
        ((DropZero a)
          (match erased dr _
            ((DropZero b) (MirrorS x l1 r1 (Zero) (MirrorZ l1 r1)))))))
    ((MirrorS y la ra k1 m1)
      (match erased dl _
        ((DropSucc n1 y1 ys1 zs1 dl1)
          (match erased dr _
            ((DropSucc n2 y2 ys2 zs2 dr1)
              (MirrorS y la ra (Succ k1)
                       (mirror-extend la ra k1 m1 x l1 r1 dl1 dr1)))))))))

(def-fns _ $ erased mirror-stop : (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Nat) j) (erased (Mirror l r j) m)
    (erased (Nat) k) (erased (List (Nat)) l2) (erased (List (Nat)) r2)
    (subterm erased (Drop k l l2) dl) (erased (Drop k r r2) dr)
    (erased (Stop l2 r2) st) -> (erased (Lt j (Succ k)) lt)
  (match erased m _
    ((MirrorZ l0 r0) (LtZ k))
    ((MirrorS x l1 r1 j1 m1)
      (match erased dl _
        ((DropZero a)
          (match erased dr _
            ((DropZero b)
              (match erased st _
                (absurd (StopNe x0 y0 la ra d) (apart-irrefl x d))))))
        ((DropSucc k1 x1 xs1 ys1 dl1)
          (match erased dr _
            ((DropSucc k2 y2 ys2 zs2 dr1)
              (LtS j1 (Succ k1)
                   (mirror-stop l1 r1 j1 m1 k1 l2 r2 dl1 dr1 st)))))))))

(def-adts
  (Walk : ((List (Nat)) l0) ((List (Nat)) r0) ((List (Nat)) l) ((List (Nat)) r)
          ((Nat) cn) -> Type
    enum
    (many WalkHere : (erased (List (Nat)) l) (erased (List (Nat)) r) ->
       (Walk l r l r (Zero)))
    (many WalkOdd : (erased (List (Nat)) l) (erased (Nat) c) (erased (List (Nat)) r1) ->
       (Walk l (Cons (Nat) c r1) l r1 (Succ (Zero))))
    (many WalkNext : (erased (List (Nat)) l) (erased (Nat) c) (erased (List (Nat)) r1)
        (erased (List (Nat)) l2) (erased (List (Nat)) r2) (erased (Nat) cn)
        (erased (Walk (Cons (Nat) c l) r1 l2 r2 cn) p) ->
       (Walk l (Cons (Nat) c r1) l2 r2 cn))))

(def-adts
  (AllBounded : ((List (Nat)) l) ((List (Nat)) r) ((Nat) n) -> Type
    enum
    (many AllBEnd : (erased (List (Nat)) l) (erased (Nat) n)
        (erased (CentreBound l (Nil (Nat)) (Zero) n) cb) ->
       (AllBounded l (Nil (Nat)) n))
    (many AllBStep : (erased (List (Nat)) l) (erased (Nat) c) (erased (List (Nat)) r1)
        (erased (Nat) n)
        (erased (CentreBound l (Cons (Nat) c r1) (Zero) n) cbe)
        (erased (CentreBound l r1 (Succ (Zero)) n) cbo)
        (erased (AllBounded (Cons (Nat) c l) r1 n) rest) ->
       (AllBounded l (Cons (Nat) c r1) n))))

(def-fns _ $ erased find-bound : (erased (List (Nat)) l0) (erased (List (Nat)) r0)
    (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (Nat) cn) (erased (Nat) n)
    (subterm erased (Walk l0 r0 l r cn) wk) (erased (AllBounded l0 r0 n) ab) ->
    (erased (CentreBound l r cn n) cb)
  (match erased wk _
    ((WalkHere la ra)
      (match erased ab _
        ((AllBEnd l1 k1 cb) cb)
        ((AllBStep l1 c1 r1 k1 cbe cbo rest) cbe)))
    ((WalkOdd la c1 r1)
      (match erased ab _
        (absurd AllBEnd)
        ((AllBStep l2 c2 r2 k2 cbe cbo rest) cbo)))
    ((WalkNext la c1 r1 l2 r2 cn2 pw)
      (match erased ab _
        (absurd AllBEnd)
        ((AllBStep l3 c3 r3 k3 cbe cbo rest)
          (find-bound (Cons (Nat) c1 la) r1 l r cn n pw rest))))))

(def-fns _ $ erased cat-assoc2 : (erased (List (Nat)) a) (erased (Nat) x)
    (erased (List (Nat)) ab) (erased (List (Nat)) c) (erased (List (Nat)) abc)
    (subterm erased (Concat (Nat) a (Cons (Nat) x (Nil (Nat))) ab) p)
    (erased (Concat (Nat) ab c abc) q) ->
    (erased (Concat (Nat) a (Cons (Nat) x c) abc) r)
  (match erased p _
    ((CatNil a1 ys1)
      (match erased q _
        ((CatCons a2 h2 t2 ys2 zs2 q2)
          (match erased q2 _
            ((CatNil a3 ys3) (CatNil (Nat) (Cons (Nat) x c)))))))
    ((CatCons a1 h1 t1 ys1 zs1 p1)
      (match erased q _
        ((CatCons a2 h2 t2 ys2 zs2 q2)
          (CatCons (Nat) h1 t1 (Cons (Nat) x c) zs2
                   (cat-assoc2 t1 x zs1 c zs2 p1 q2)))))))

(def-fns _ $ erased snoc-len : (erased (List (Nat)) a) (erased (Nat) x)
    (erased (List (Nat)) ab) (subterm erased (Concat (Nat) a (Cons (Nat) x (Nil (Nat))) ab) p)
    (erased (Nat) n) (erased (Length (Nat) a n) ln) ->
    (erased (Length (Nat) ab (Succ n)) lab)
  (match erased p _
    ((CatNil a1 ys1)
      (match erased ln _
        ((LNil b1) (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat))))))
    ((CatCons a1 h1 t1 ys1 zs1 p1)
      (match erased ln _
        ((LCons b1 x1 r1 n1 ln1)
          (LCons (Nat) h1 zs1 (Succ n1) (snoc-len t1 x zs1 p1 n1 ln1)))))))

(def-fns _ $ erased length-fn : (erased (List (Nat)) xs) (erased (Nat) n1) (erased (Nat) n2)
    (subterm erased (Length (Nat) xs n1) p) (erased (Length (Nat) xs n2) q) ->
    (erased (Eq (Nat) n1 n2) e)
  (match erased p _
    ((LNil a) (match erased q _ ((LNil b) (Refl (Nat) n1)) (absurd LCons)))
    ((LCons a x rest k p1)
      (match erased q _
        (absurd LNil)
        ((LCons b y rest2 k2 q1)
          (match erased (length-fn rest k k2 p1 q1) _
            ((Refl t r) (Refl (Nat) n1))))))))

(def-fns _ $ erased pal-mirror :
    (erased (List (Nat)) w) (subterm erased (Palindrome (Nat) w) p)
    (erased (List (Nat)) lcur) (erased (List (Nat)) rcur) (erased (List (Nat)) src)
    (erased (Concat (Nat) w rcur src) cw) ->
    (erased (List (Nat)) l2) (erased (List (Nat)) r2) (erased (Nat) h)
    (erased (Mirror l2 r2 h) mm)
    (erased (Drop h l2 lcur) dl) (erased (Drop h r2 rcur) dr)
    (erased (Nat) cn) (erased (Walk lcur src l2 r2 cn) wk)
    (erased (Nat) m2) (erased (Length (Nat) w m2) lw2)
    (erased (Nat) dh) (erased (Double h dh) ddh) (erased (Add cn dh m2) adm)
  (match erased p _
    ((PalNil a1)
      (match erased cw _
        ((CatNil a2 ys2)
          (values lcur rcur (Zero) (MirrorZ lcur rcur)
                  (DropZero lcur) (DropZero rcur)
                  (Zero) (WalkHere lcur rcur)
                  (Zero) (LNil (Nat)) (Zero) (D0) (AddZero (Zero))))))
    ((PalOne a1 x)
      (match erased cw _
        ((CatCons a2 h2 t2 ys2 zs2 q2)
          (match erased q2 _
            ((CatNil a3 ys3)
              (values lcur rcur (Zero) (MirrorZ lcur rcur)
                      (DropZero lcur) (DropZero rcur)
                      (Succ (Zero)) (WalkOdd lcur x rcur)
                      (Succ (Zero))
                      (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat)))
                      (Zero) (D0)
                      (AddSucc (Zero) (Zero) (Zero) (AddZero (Zero)))))))))
    ((PalWrap a1 x inner withx pi q)
      (match erased cw _
        ((CatCons a2 h2 t2 ys2 zs2 cwz)
          (let (erased ci) (cat-assoc2 inner x withx rcur zs2 q cwz))
          (let (erased l2) (erased r2) (erased h1) (erased mm1) (erased dl1) (erased dr1)
               (erased cn) (erased wk1) (erased mi) (erased lwi) (erased dh1)
               (erased ddh1) (erased adm1)
            (pal-mirror inner pi (Cons (Nat) x lcur) (Cons (Nat) x rcur) zs2 ci))
          (values l2 r2 (Succ h1)
                  (mirror-extend l2 r2 h1 mm1 x lcur rcur dl1 dr1)
                  (drop-succ h1 l2 x lcur dl1) (drop-succ h1 r2 x rcur dr1)
                  cn (WalkNext lcur x zs2 l2 r2 cn wk1)
                  (Succ (Succ mi))
                  (LCons (Nat) x withx (Succ mi) (snoc-len inner x withx q mi lwi))
                  (Succ (Succ dh1)) (DS h1 dh1 ddh1)
                  (add-succ-right cn (Succ dh1) (Succ mi)
                    (add-succ-right cn dh1 mi adm1))))))))

(def-fns _ $ erased le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c)
    (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r)
  (match erased p _
    ((LtZ b1) (LtZ c))
    ((LtS a1 b1 p1) (LtS a1 c (lt-le-trans a1 b c p1 q)))))

(def-fns _ $ erased double-mono : (erased (Nat) h) (erased (Nat) k)
    (erased (Nat) dh) (erased (Nat) dk)
    (subterm erased (Double h dh) dd1) (erased (Double k dk) dd2)
    (erased (Lt h (Succ k)) le) -> (erased (Lt dh (Succ dk)) r)
  (match erased dd1 _
    ((D0) (LtZ dk))
    ((DS h1 d1 dd1a)
      (match erased le _
        ((LtS a1 b1 le1)
          (match erased dd2 _
            (absurd (D0) (match erased le1 (((False) f))))
            ((DS k1 dk1 dd2a)
              (LtS (Succ d1) (Succ (Succ dk1))
                   (LtS d1 (Succ dk1)
                        (double-mono h1 k1 d1 dk1 dd1a dd2a le1))))))))))

(def-fns _ $ erased add-mono : (erased (Nat) cn) (erased (Nat) d1) (erased (Nat) d2)
    (erased (Nat) m1) (erased (Nat) m2)
    (subterm erased (Add cn d1 m1) p) (erased (Add cn d2 m2) q)
    (erased (Lt d1 (Succ d2)) le) -> (erased (Lt m1 (Succ m2)) r)
  (match erased p _
    ((AddZero b1) (match erased q _ ((AddZero b2) le) (absurd AddSucc)))
    ((AddSucc a1 b1 c1 p1)
      (match erased q _
        (absurd AddZero)
        ((AddSucc a2 b2 c2 q1)
          (LtS c1 (Succ c2) (add-mono a1 d1 d2 c1 c2 p1 q1 le)))))))

(def-fns _ $ erased take-concat : (erased (Nat) n) (erased (List (Nat)) src)
    (erased (List (Nat)) w) (subterm erased (Take (Nat) n src w) tk) ->
    (erased (List (Nat)) rem) (erased (Concat (Nat) w rem src) c)
  (match erased tk _
    ((TakeZero a xs) (values src (CatNil (Nat) src)))
    ((TakeSucc a n1 x xs1 w1 tk1)
      (let (erased rem) (erased c) (take-concat n1 xs1 w1 tk1))
      (values rem (CatCons (Nat) x w1 rem xs1 c)))))

(def-fns _ $ erased revcat-walk : (erased (List (Nat)) lcur) (erased (List (Nat)) src)
    (erased (List (Nat)) xs) (subterm erased (RevCat lcur src xs) rc)
    (erased (List (Nat)) l2) (erased (List (Nat)) r2) (erased (Nat) cn)
    (erased (Walk lcur src l2 r2 cn) wk) ->
    (erased (Walk (Nil (Nat)) xs l2 r2 cn) wk2)
  (match erased rc _
    ((RevFlat a) wk)
    ((RevStep x l1 r1 xs1 pr)
      (revcat-walk l1 (Cons (Nat) x src) xs pr l2 r2 cn
                   (WalkNext l1 x src l2 r2 cn wk)))))

(def-fns _ $ erased too-long : (erased (List (Nat)) xs) (erased (Nat) n)
    (erased (AllBounded (Nil (Nat)) xs n) ab)
    (erased (List (Nat)) lcur) (erased (List (Nat)) src)
    (erased (RevCat lcur src xs) rc)
    (erased (List (Nat)) w) (erased (Palindrome (Nat) w) pw)
    (erased (Nat) m) (erased (Length (Nat) w m) lw)
    (erased (List (Nat)) rem) (erased (Concat (Nat) w rem src) cw)
    (erased (Lt n m) big) -> (erased (False) f)
  (let (erased l2) (erased r2) (erased h) (erased mm) (erased dl) (erased dr)
       (erased cn) (erased wk) (erased m2) (erased lw2) (erased dh) (erased ddh)
       (erased adm)
    (pal-mirror w pw lcur rem src cw))
  (match erased (length-fn w m m2 lw lw2) _
    ((Refl t0 r0)
      (match erased (find-bound (Nil (Nat)) xs l2 r2 cn n
                                (revcat-walk lcur src xs rc l2 r2 cn wk) ab) _
        ((MkCentreBound bl br bcn bn k l3 r3 dl3 dr3 st dk ddk lc adc le)
          (lt-asym n m big
            (le-trans m lc n
              (add-mono cn dh dk m lc adm adc
                (double-mono h k dh dk ddh ddk
                  (mirror-stop l2 r2 h mm k l3 r3 dl3 dr3 st)))
              le)))))))

(def-fns _ $ erased cb-weaken : (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Nat) cn) (erased (Nat) n1) (erased (Nat) n2)
    (erased (CentreBound l r cn n1) cb) (erased (Lt n1 (Succ n2)) le) ->
    (erased (CentreBound l r cn n2) cb2)
  (match erased cb _
    ((MkCentreBound bl br bcn bn k l2 r2 dl dr st dk ddk lc adc le0)
      (MkCentreBound l r cn n2 k l2 r2 dl dr st dk ddk lc adc
                     (le-trans lc n1 n2 le0 le)))))

(def-fns _ $ erased allb-weaken : (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Nat) n1) (erased (Nat) n2) (subterm erased (AllBounded l r n1) ab)
    (erased (Lt n1 (Succ n2)) le) -> (erased (AllBounded l r n2) ab2)
  (match erased ab _
    ((AllBEnd l1 k1 cb)
      (AllBEnd l n2 (cb-weaken l (Nil (Nat)) (Zero) n1 n2 cb le)))
    ((AllBStep l1 c1 r1 k1 cbe cbo rest)
      (AllBStep l c1 r1 n2
        (cb-weaken l r (Zero) n1 n2 cbe le)
        (cb-weaken l r1 (Succ (Zero)) n1 n2 cbo le)
        (allb-weaken (Cons (Nat) c1 l) r1 n1 n2 rest le)))))

(def-fns _ $ many best-from : (many (List (Nat)) l) (subterm many (List (Nat)) r)
    (erased (List (Nat)) xs) (erased (RevCat l r xs) rc) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
    (erased (AllBounded l r n) ab)
  (match many r _
    ((Nil a)
      (let (many ne) (erased he) (erased cbe)
        (centre-has l r (Zero) (Nil (Nat)) (PalNil (Nat)) (LNil (Nat))
                    r (CatNil (Nat) r) xs rc))
      (values ne he (AllBEnd l ne cbe)))
    ((Cons a c r1)
      (let (many ne) (erased he) (erased cbe)
        (centre-has l r (Zero) (Nil (Nat)) (PalNil (Nat)) (LNil (Nat))
                    r (CatNil (Nat) r) xs rc))
      (let (many no) (erased ho) (erased cbo)
        (centre-has l r1 (Succ (Zero))
                    (Cons (Nat) c (Nil (Nat))) (PalOne (Nat) c)
                    (LCons (Nat) c (Nil (Nat)) (Zero) (LNil (Nat)))
                    r (CatCons (Nat) c (Nil (Nat)) r1 r1 (CatNil (Nat) r1))
                    xs rc))
      (let (many nr) (erased hr) (erased abr)
        (best-from (Cons (Nat) c l) r1 xs (RevStep c l r1 xs rc)))
      (let (many n1) (erased h1) (erased be1) (erased be2) (pick xs ne he no ho))
      (let (many n) (erased h) (erased be3) (erased be4) (pick xs n1 h1 nr hr))
      (values n h
        (AllBStep l c r1 n
          (cb-weaken l r (Zero) ne n cbe (le-trans ne n1 n be1 be3))
          (cb-weaken l r1 (Succ (Zero)) no n cbo (le-trans no n1 n be2 be3))
          (allb-weaken (Cons (Nat) c l) r1 nr n abr be4))))))

(def-fns _ $ erased take-len : (erased (Nat) n) (erased (List (Nat)) src)
    (erased (List (Nat)) w) (subterm erased (Take (Nat) n src w) tk) ->
    (erased (Length (Nat) w n) lw)
  (match erased tk _
    ((TakeZero a xs) (LNil (Nat)))
    ((TakeSucc a n1 x xs1 w1 tk1) (LCons (Nat) x w1 n1 (take-len n1 xs1 w1 tk1)))))

(def-fns _ $ erased add-unshift : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c)
    (erased (Add a (Succ b) c) p) -> (erased (Add (Succ a) b c) q)
  (let (erased c1) (erased e) (erased q1) (add-succ-right-inv a b c p))
  (match erased e _ ((Refl t r) (AddSucc a b c1 q1))))

(def-fns _ $ erased no-pal : (erased (List (Nat)) xs0) (erased (Nat) n)
    (erased (AllBounded (Nil (Nat)) xs0 n) ab)
    (erased (List (Nat)) lcur) (subterm erased (List (Nat)) src)
    (erased (RevCat lcur src xs0) rc)
    (erased (Nat) m) (erased (Lt n m) big) ->
    (erased (NoPalindromeOfLengthF src m) np)
  (match erased (take-dec m src) _
    ((TakeNo n0 xs1 len l short) (SlideShort src m len l short))
    ((TakeYes n0 xs1 w tk)
      (match erased (pal-dec m w (take-len m src w tk)) _
        ((InL s0 s1 pww)
          (let (erased rem) (erased cw) (take-concat m src w tk))
          (match erased
            (too-long xs0 n ab lcur src rc w pww m (take-len m src w tk) rem cw big) _))
        ((InR s0 s1 npw)
          (match erased src _
            ((Nil a2)
              (match erased tk _ ((TakeZero a3 xs3) (match erased big _))))
            ((Cons a2 x xs2)
              (SlideStep m x xs2 w tk npw
                (no-pal xs0 n ab (Cons (Nat) x lcur) xs2
                        (RevStep x lcur xs2 xs0 rc) m big)))))))))

(def-fns _ $ erased no-larger : (erased (List (Nat)) xs) (erased (Nat) n)
    (erased (AllBounded (Nil (Nat)) xs n) ab)
    (erased (Nat) len) (erased (Length (Nat) xs len) lxs)
    (erased (Nat) m) (subterm erased (Nat) c) (erased (Add m c len) adc)
    (erased (Lt n (Succ m)) ge) -> (erased (NoLargerPalindromeF xs m) nl)
  (match erased c _
    ((Zero)
      (match erased (add-fn m (Zero) len m adc (add-zero-right m)) _
        ((Refl t r) (NoLargerDoneF xs m len lxs (lt-succ len)))))
    ((Succ c1)
      (NoLargerStepF xs m
        (no-pal xs n ab (Nil (Nat)) xs (RevFlat xs) (Succ m) ge)
        (no-larger xs n ab len lxs (Succ m) c1 (add-unshift m c1 len adc)
                   (lt-weaken n (Succ m) ge))))))

(def-fns _ $ many longest-fast : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (LongestPalindrome xs n) p)
  (let (many n) (erased h) (erased ab) (best-from (Nil (Nat)) xs xs (RevFlat xs)))
  (let (many len) (erased lxs) (list-length xs))
  (let (erased nle)
    (match many (lt-dec len n) (((Lt n (Succ len)) z))
      (absurd (Yes a b p) (has-short-absurd xs n h len lxs p))
      ((No a b q) q)))
  (let (many c) (erased adc) (sub len n nle))
  (let (erased nl) (no-larger xs n ab len lxs n c adc (lt-succ n)))
  (let (erased xss) (erased ww) (erased ee) (has-windows xs n h))
  (values n (IsLongest xs n xss ww ee (nolarger-spec xs n nl))))

(def-fns _ $ many radius : (many (List (Nat)) l) (many (List (Nat)) r) -> (many (Nat) k)
  (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr) (erased st)
       (expand l r))
  k)

(def-fns _ $ many lpc : (many (List (Nat)) xs) -> (many (Nat) n)
  (let (many n) (erased p) (longest-fast xs))
  n)

(Cons (Nat) (lpc (Nil (Nat)))
  $ Cons (Nat) (lpc $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Nil (Nat))
  $ Cons (Nat) (lpc $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 2 $ Cons (Nat) 5 $ Nil (Nat))
  $ Cons (Nat) (lpc $ Cons (Nat) 9 $ Cons (Nat) 4 $ Cons (Nat) 5 $ Cons (Nat) 5 $ Cons (Nat) 4 $ Cons (Nat) 8 $ Nil (Nat))
  $ Cons (Nat) (lpc $ Cons (Nat) 7 $ Cons (Nat) 7 $ Cons (Nat) 7 $ Nil (Nat))
  $ Nil (Nat))
