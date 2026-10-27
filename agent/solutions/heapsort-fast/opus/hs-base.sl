; Element type, order, and the glue between the spec's Nat lists and the sort's U62 lists.

(let ((erased Elt)) (Copy (U62)))

(def-adts
  ((ULe : (Elt a) (Elt b) -> Type)
    enum
    (many MkULe : (erased (Nat) x) (erased (Lt x u62-modulus) px) (erased (Nat) y) (erased (Lt y u62-modulus) py)
        (erased (NatLe x y) le) -> (ULe (MkCopy (U62) (MkU62 x px)) (MkCopy (U62) (MkU62 y py))))))

(def-adts
  ((Wr : ((List (Nat)) xs) ((List Elt) ds) -> Type)
    enum
    (many WrNil : -> (Wr (Nil (Nat)) (Nil Elt)))
    (many WrCons : (erased (Nat) x) (erased (Lt x u62-modulus) p) (erased (List (Nat)) xs) (erased (List Elt) ds)
        (erased (Wr xs ds) w) -> (Wr (Cons (Nat) x xs) (Cons Elt (MkCopy (U62) (MkU62 x p)) ds)))))

(def-fns _ $ (erased to-u62 : (erased (List (Nat)) xs) (erased (AllTo (Nat) Lt xs u62-modulus) small)
    (erased (List (Copy (Nat))) cs) (subterm erased (Copies (Nat) xs cs) rel) (erased (Array (Copy (Nat)) cs) a) ->
    (erased (List Elt) ds) (erased (Wr xs ds) w) (erased (Array Elt ds) b)
    (erased (Coercible (Unique) (Array (Copy (Nat)) cs) a (Unique) (Array Elt ds) b) c))
  (let-match erased rel (CopiesCons _ x xs1 cs1 rel1)
    ((CopiesNil _)
      (let-match erased a (ANil _))
      (values (Nil Elt) (WrNil) (ANil Elt) (coercible-ctor _ ANil (Copy (Nat)) Elt))))
  (let-match erased small (AllToCons _ _ _ _ _ p small1))
  (let-match erased a (ACons _ _ _ a1))
  (let ((erased ds1) (erased w1) (erased b1) (erased c1)) (to-u62 xs1 small1 cs1 rel1 a1))
  (values (Cons Elt (MkCopy (U62) (MkU62 x p)) ds1) (WrCons x p xs1 ds1 w1)
    (ACons Elt ds1 (MkCopy (U62) (MkU62 x p)) b1)
    (coercible-ctor _ ACons (Copy (Nat)) Elt cs1 ds1
      (coercible-ctor _ MkCopy (Nat) (U62) (coercible-wrap (Shared) MkU62 x p))
      c1)))

(def-fns _ $ (erased from-u62 : (erased (List (Nat)) ys) (erased (List Elt) ds) (subterm erased (Wr ys ds) w)
    (erased (Array Elt ds) b) ->
    (erased (List (Copy (Nat))) cs) (erased (Copies (Nat) ys cs) rel) (erased (Array (Copy (Nat)) cs) a)
    (erased (Coercible (Unique) (Array Elt ds) b (Unique) (Array (Copy (Nat)) cs) a) c))
  (let-match erased w (WrCons y p ys1 ds1 w1)
    ((WrNil)
      (let-match erased b (ANil _))
      (values (Nil (Copy (Nat))) (CopiesNil (Nat)) (ANil (Copy (Nat))) (coercible-ctor _ ANil Elt (Copy (Nat))))))
  (let-match erased b (ACons _ _ _ b1))
  (let ((erased cs1) (erased rel1) (erased a1) (erased c1)) (from-u62 ys1 ds1 w1 b1))
  (values (Cons (Copy (Nat)) (MkCopy (Nat) y) cs1) (CopiesCons (Nat) y ys1 cs1 rel1)
    (ACons (Copy (Nat)) cs1 (MkCopy (Nat) y) a1)
    (coercible-ctor _ ACons Elt (Copy (Nat)) ds1 cs1
      (coercible-ctor _ MkCopy (U62) (Nat) (coercible-sym (coercible-wrap (Shared) MkU62 y p)))
      c1)))

(def-fns _ $ (erased perm-from-u62 : (erased (List (Nat)) xs) (erased (List Elt) ds) (erased (List Elt) es)
    (erased (Wr xs ds) w) (subterm erased (Permutation Elt ds es) pm) ->
    (erased (List (Nat)) ys) (erased (Wr ys es) w2) (erased (Permutation (Nat) xs ys) pm2))
  (match erased pm _
    ((PNil _) (let-match erased w (WrNil)) (values (Nil (Nat)) (WrNil) (PNil (Nat))))
    ((PSkip _ e ds1 es1 p)
      (let-match erased w (WrCons x px xs1 _ w1))
      (let ((erased ys1) (erased w3) (erased p3)) (perm-from-u62 xs1 ds1 es1 w1 p))
      (values (Cons (Nat) x ys1) (WrCons x px ys1 es1 w3) (PSkip (Nat) x xs1 ys1 p3)))
    ((PSwap _ e f l)
      (let-match erased w (WrCons x px xs1 _ w1))
      (let-match erased w1 (WrCons y py xs2 _ w2))
      (values (Cons (Nat) y (Cons (Nat) x xs2)) (WrCons y py (Cons (Nat) x xs2) (Cons Elt e l) (WrCons x px xs2 l w2))
        (PSwap (Nat) x y xs2)))
    ((PTrans _ _ ms _ p q)
      (let ((erased ys1) (erased w3) (erased p3)) (perm-from-u62 xs ds ms w p))
      (let ((erased ys2) (erased w4) (erased p4)) (perm-from-u62 ys1 ms es w3 q))
      (values ys2 w4 (PTrans (Nat) xs ys1 ys2 p3 p4)))))

(def-fns _ $ (erased asc-from-u62 : (erased (List (Nat)) ys) (erased (List Elt) es)
    (erased (Wr ys es) w) (subterm erased (Ascending Elt ULe es) asc) -> (erased (Ascending (Nat) NatLe ys) asc2))
  (match erased asc _
    ((AscNil _ _) (let-match erased w (WrNil)) (AscNil (Nat) NatLe))
    ((AscOne _ _ e)
      (let-match erased w (WrCons y py ys1 _ w1))
      (let-match erased w1 (WrNil))
      (AscOne (Nat) NatLe y))
    ((AscCons _ _ e f rest le a)
      (let-match erased w (WrCons y py ys1 _ w1))
      (let-match erased w1 (WrCons z pz ys2 _ w2))
      (let-match erased le (MkULe _ _ _ _ yz))
      (AscCons (Nat) NatLe y z ys2 yz (asc-from-u62 ys1 (Cons Elt f rest) w1 a)))))

; Swapping two entries is a permutation.
(def-fns _ $ (erased perm-set-front : (erased (List Elt) rest) (erased (Nat) k) (erased Elt x y) (erased (List Elt) rest2)
    (subterm erased (Nth Elt rest k y) nth) (erased (SetNth Elt rest k x rest2) st) ->
    (erased (Permutation Elt (Cons Elt x rest) (Cons Elt y rest2)) pm))
  (match erased nth _
    ((NthHere _ _ t)
      (let-match erased st (SetHere _ _ _ _))
      (PSwap Elt x y t))
    ((NthThere _ b t k1 _ nth1)
      (let-match erased st (SetThere _ _ _ _ _ t2 st1))
      (let ((erased ih)) (perm-set-front t k1 x y t2 nth1 st1))
      (PTrans Elt (Cons Elt x (Cons Elt b t)) (Cons Elt b (Cons Elt x t)) (Cons Elt y (Cons Elt b t2))
        (PSwap Elt x b t)
        (PTrans Elt (Cons Elt b (Cons Elt x t)) (Cons Elt b (Cons Elt y t2)) (Cons Elt y (Cons Elt b t2))
          (PSkip Elt b (Cons Elt x t) (Cons Elt y t2) ih)
          (PSwap Elt b y t2))))))

(def-fns _ $ (erased perm-swap : (erased (List Elt) xs) (erased (Nat) i) (erased (Nat) j) (erased Elt x) (erased Elt y)
    (erased (List Elt) zs) (erased (List Elt) ys)
    (subterm erased (Nth Elt xs i x) ni) (erased (Nth Elt xs j y) nj) (erased (Lt i j) lt)
    (erased (SetNth Elt xs i y zs) s1) (erased (SetNth Elt zs j x ys) s2) -> (erased (Permutation Elt xs ys) pm))
  (match erased ni _
    ((NthHere _ _ rest)
      (let-match erased s1 (SetHere _ _ _ _))
      (let-match erased lt (LtZ j1))
      (let-match erased s2 (SetThere _ _ _ _ _ rest2 s21))
      (let-match erased nj (NthThere _ _ _ _ _ nj1))
      (perm-set-front rest j1 x y rest2 nj1 s21))
    ((NthThere _ b t i1 _ ni1)
      (let-match erased lt (LtS _ j1 lt1))
      (let-match erased s1 (SetThere _ _ _ _ _ t2 s11))
      (let-match erased s2 (SetThere _ _ _ _ _ t3 s21))
      (let-match erased nj (NthThere _ _ _ _ _ nj1))
      (PSkip Elt b t t3 (perm-swap t i1 j1 x y t2 t3 ni1 nj1 lt1 s11 s21)))))

(def-adts
  ((NeN : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many NeL : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (NeN a b))
    (many NeG : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) p) -> (NeN a b))))

(def-fns _ $ (erased nth-set-ne : (erased (List Elt) xs) (erased (Nat) i) (erased Elt y) (erased (List Elt) ys)
    (erased (SetNth Elt xs i y ys) st) (erased (Nat) k) (erased Elt z) (erased (Nth Elt xs k z) nk) (erased (NeN k i) ne)
    -> (erased (Nth Elt ys k z) r))
  (match erased ne _
    ((NeL _ _ p) (setnth-nth-lt Elt xs i k y z ys st nk p))
    ((NeG _ _ p) (setnth-nth-gt Elt xs i k y z ys st nk p))))

; A swap of positions i < j: xs[i] = x, xs[j] = y, and ys has them exchanged.
(def-adts
  ((Swap : ((List Elt) xs) ((Nat) i) ((Nat) j) ((List Elt) ys) -> Type)
    enum
    (many MkSwap : (erased (List Elt) xs) (erased (Nat) i) (erased (Nat) j) (erased Elt x) (erased Elt y)
        (erased (List Elt) zs) (erased (List Elt) ys)
        (erased (Nth Elt xs i x) ni) (erased (Nth Elt xs j y) nj) (erased (Lt i j) lt)
        (erased (SetNth Elt xs i y zs) s1) (erased (SetNth Elt zs j x ys) s2) -> (Swap xs i j ys))))

(def-fns _ $ (erased swap-perm : (erased (List Elt) xs) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys)
    (erased (Swap xs i j ys) sw) -> (erased (Permutation Elt xs ys) pm))
  (let-match erased sw (MkSwap _ _ _ x y zs _ ni nj lt s1 s2))
  (perm-swap xs i j x y zs ys ni nj lt s1 s2))

; Reading a swapped list: at i it holds xs[j], at j it holds xs[i], elsewhere it agrees.
(def-fns _ $ (erased swap-at-i : (erased (List Elt) xs) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys)
    (erased (Swap xs i j ys) sw) (erased Elt y) (erased (Nth Elt xs j y) nj) -> (erased (Nth Elt ys i y) r))
  (let-match erased sw (MkSwap _ _ _ x y0 zs _ ni nj0 lt s1 s2))
  (let-match erased (nth-fn Elt xs j y0 y nj0 nj) (Refl _ _))
  (setnth-nth-lt Elt zs j i x y ys s2 (setnth-nth Elt xs i y zs s1) lt))

(def-fns _ $ (erased swap-at-j : (erased (List Elt) xs) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys)
    (erased (Swap xs i j ys) sw) (erased Elt x) (erased (Nth Elt xs i x) ni) -> (erased (Nth Elt ys j x) r))
  (let-match erased sw (MkSwap _ _ _ x0 y zs _ ni0 nj lt s1 s2))
  (let-match erased (nth-fn Elt xs i x0 x ni0 ni) (Refl _ _))
  (setnth-nth Elt zs j x ys s2))

(def-fns _ $ (erased swap-other : (erased (List Elt) xs) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys)
    (erased (Swap xs i j ys) sw) (erased (Nat) k) (erased Elt z) (erased (Nth Elt xs k z) nk)
    (erased (NeN k i) ki) (erased (NeN k j) kj) -> (erased (Nth Elt ys k z) r))
  (let-match erased sw (MkSwap _ _ _ x y zs _ ni nj lt s1 s2))
  (nth-set-ne zs j x ys s2 k z (nth-set-ne xs i y zs s1 k z nk ki) kj))

(def-fns _ $ (erased swap-length : (erased (List Elt) xs) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys)
    (erased (Swap xs i j ys) sw) (erased (Nat) n) (erased (Length Elt xs n) len) -> (erased (Length Elt ys n) r))
  (let-match erased sw (MkSwap _ _ _ x y zs _ ni nj lt s1 s2))
  (setnth-length Elt zs j n x ys s2 (setnth-length Elt xs i n y zs s1 len)))

(def-fns _ $ (erased perm-refl : (subterm erased (List Elt) xs) -> (erased (Permutation Elt xs xs) pm))
  (match erased xs _
    ((Nil _) (PNil Elt))
    ((Cons _ x rest) (PSkip Elt x rest rest (perm-refl rest)))))
