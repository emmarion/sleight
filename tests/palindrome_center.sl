; needs: palindrome_relations
; expect: (Cons 0 (Cons 2 (Cons 1 (Cons 3 (Nil)))))

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
    (erased (List (Nat)) src) (erased (Concat (Nat) core r src) cc) ->
    (erased (List (Nat)) w) (erased (Palindrome (Nat) w) pw)
    (erased (Nat) n) (erased (Length (Nat) w n) lw)
    (erased (Nat) d) (erased (Double k d) dd) (erased (Add cn d n) ad)
    (erased (List (Nat)) src2) (erased (List (Nat)) r2)
    (erased (Concat (Nat) w r2 src2) cc2)
  (match erased m _
    ((MirrorZ l0 r0)
      (values core pc cn lc (Zero) (D0) (add-zero-right cn) src r cc))
    ((MirrorS x l1 r1 k1 m1)
      (let (erased cs) (erased csc) (erased csl) (snoc core x cn lc))
      (let (erased cc1) (snoc-shift core x r1 src cs cc csc))
      (let (erased w) (erased pw) (erased n) (erased lw) (erased d1) (erased dd1)
           (erased ad1) (erased src2) (erased r2) (erased cc2)
        (mirror-wrap l1 r1 k1 m1
                     (Cons (Nat) x cs) (PalWrap (Nat) x core cs pc csc)
                     (Succ (Succ cn)) (LCons (Nat) x cs (Succ cn) csl)
                     (Cons (Nat) x src)
                     (CatCons (Nat) x cs r1 src cc1)))
      (values w pw n lw (Succ (Succ d1)) (DS k1 d1 dd1)
              (add-shift cn (Succ d1) n (add-shift (Succ cn) d1 n ad1))
              src2 r2 cc2))))

(def-fns _ $ many radius : (many (List (Nat)) l) (many (List (Nat)) r) -> (many (Nat) k)
  (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr) (erased st)
       (expand l r))
  k)

(let (many la) (Cons (Nat) 2 (Cons (Nat) 1 (Nil (Nat)))))
(let (many ra) (Cons (Nat) 2 (Cons (Nat) 1 (Cons (Nat) 9 (Nil (Nat))))))
(Cons (Nat) (radius (Nil (Nat)) ra)
  $ Cons (Nat) (radius la ra)
  $ Cons (Nat) (radius la (Cons (Nat) 2 (Cons (Nat) 7 (Nil (Nat)))))
  $ Cons (Nat) (radius (Cons (Nat) 3 la) (Cons (Nat) 3 ra))
  $ Nil (Nat))
