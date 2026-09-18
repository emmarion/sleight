; needs: palindrome_relations
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

(def-fns _ $ many centre-has :
    (many (List (Nat)) l) (many (List (Nat)) rm) (many (Nat) cn)
    (erased (List (Nat)) core) (erased (Palindrome (Nat) core) pc)
    (erased (Length (Nat) core cn) lc)
    (erased (List (Nat)) src) (erased (Concat (Nat) core rm src) cc)
    (erased (List (Nat)) xs) (erased (RevCat l src xs) rc) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
  (let (many k) (erased m) (erased le) (erased re) (erased dl) (erased dr) (erased st)
       (expand l rm))
  (let (erased w) (erased pw) (erased n0) (erased lw) (erased d0) (erased dd0) (erased ad0)
       (erased src2) (erased r2) (erased cc2) (erased l2) (erased rc2)
       (mirror-wrap l rm k m core pc cn lc src cc xs rc))
  (let (many drt) (erased ddrt) (double k))
  (let (many nrt) (erased adrt) (add cn drt))
  (let (erased lw2) (fix-length w cn k d0 n0 drt nrt dd0 ad0 ddrt adrt lw))
  (values nrt (revcat-has l2 src2 xs rc2 nrt
                (HasHere src2 nrt w (concat-take w r2 src2 cc2 nrt lw2) pw))))

(def-fns _ $ many pick : (erased (List (Nat)) xs)
    (many (Nat) n1) (erased (HasPalindromeOfLength xs n1) h1)
    (many (Nat) n2) (erased (HasPalindromeOfLength xs n2) h2) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
  (match many (nat-cmp n1 n2) _
    ((CLt t r a b p) (values n2 h2))
    ((CEq t r a) (values n1 h1))
    ((CGt t r a b p) (values n1 h1))))

(def-fns _ $ many best-from : (many (List (Nat)) l) (subterm many (List (Nat)) r)
    (erased (List (Nat)) xs) (erased (RevCat l r xs) rc) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
  (match many r _
    ((Nil a)
      (values (Zero)
              (revcat-has l r xs rc (Zero)
                (HasHere r (Zero) (Nil (Nat)) (TakeZero (Nat) r) (PalNil (Nat))))))
    ((Cons a c r1)
      (let (many ne) (erased he)
        (centre-has l r (Zero) (Nil (Nat)) (PalNil (Nat)) (LNil (Nat))
                    r (CatNil (Nat) r) xs rc))
      (let (many no) (erased ho)
        (centre-has l r1 (Succ (Zero))
                    (Cons (Nat) c (Nil (Nat))) (PalOne (Nat) c)
                    (LCons (Nat) c (Nil (Nat)) (Zero) (LNil (Nat)))
                    r (CatCons (Nat) c (Nil (Nat)) r1 r1 (CatNil (Nat) r1))
                    xs rc))
      (let (many nr) (erased hr)
        (best-from (Cons (Nat) c l) r1 xs (RevStep c l r1 xs rc)))
      (let (many n1) (erased h1) (pick xs ne he no ho))
      (pick xs n1 h1 nr hr))))

(def-fns _ $ many longest-has : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
  (best-from (Nil (Nat)) xs xs (RevFlat xs)))

(def-fns _ $ many radius : (many (List (Nat)) l) (many (List (Nat)) r) -> (many (Nat) k)
  (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr) (erased st)
       (expand l r))
  k)

(def-fns _ $ many lp : (many (List (Nat)) xs) -> (many (Nat) n)
  (let (many n) (erased h) (longest-has xs))
  n)

(Cons (Nat) (lp (Nil (Nat)))
  $ Cons (Nat) (lp $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Nil (Nat))
  $ Cons (Nat) (lp $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 2 $ Cons (Nat) 5 $ Nil (Nat))
  $ Cons (Nat) (lp $ Cons (Nat) 9 $ Cons (Nat) 4 $ Cons (Nat) 5 $ Cons (Nat) 5 $ Cons (Nat) 4 $ Cons (Nat) 8 $ Nil (Nat))
  $ Cons (Nat) (lp $ Cons (Nat) 7 $ Cons (Nat) 7 $ Cons (Nat) 7 $ Nil (Nat))
  $ Nil (Nat))
