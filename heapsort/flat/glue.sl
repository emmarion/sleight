(def-adts
  ((Rel : ((List (Nat)) xs) ((List (Copy (U62))) us) -> Type)
    enum
    (many RNil : -> (Rel (Nil (Nat)) (Nil (Copy (U62)))))
    (many RCons : (erased (Nat) x) (erased (Lt x u62-modulus) p) (erased (List (Nat)) xs) (erased (List (Copy (U62))) us)
       (erased (Rel xs us) r) -> (Rel (Cons (Nat) x xs) (Cons (Copy (U62)) (MkCopy (U62) (MkU62 x p)) us)))))

(def-fns _ $ (erased to-u62 : (erased (List (Nat)) xs) (erased (List (Copy (Nat))) cs) (subterm erased (Copies (Nat) xs cs) rel)
    (erased (AllTo (Nat) Lt xs u62-modulus) small) (erased (Array (Copy (Nat)) cs) a) ->
    (erased (List (Copy (U62))) us) (erased (Rel xs us) r) (erased (Array (Copy (U62)) us) b)
    (erased (Coercible (Unique) (Array (Copy (Nat)) cs) a (Unique) (Array (Copy (U62)) us) b) c))
  (let-match erased rel (CopiesCons _ x rest cs1 rel1)
    ((CopiesNil _)
      (let-match erased a (ANil _))
      (values (Nil _) (RNil) (ANil _) (coercible-ctor _ ANil (Copy (Nat)) (Copy (U62))))))
  (let-match erased small (AllToCons _ _ _ _ _ p small1))
  (let-match erased a (ACons _ _ hd tl))
  (let ((erased us1) (erased r1) (erased b1) (erased c1)) (to-u62 rest cs1 rel1 small1 tl))
  (values (Cons _ (MkCopy _ (MkU62 x p)) us1) (RCons x p rest us1 r1) (ACons _ _ (MkCopy _ (MkU62 x p)) b1)
    (coercible-ctor _ ACons (Copy (Nat)) (Copy (U62)) cs1 us1
      (coercible-ctor _ MkCopy (Nat) (U62) (coercible-wrap _ MkU62 x p)) c1)))

(def-fns _ $ (erased from-u62 : (erased (List (Nat)) ys) (erased (List (Copy (U62))) us) (subterm erased (Rel ys us) rel)
    (erased (Array (Copy (U62)) us) b) ->
    (erased (List (Copy (Nat))) ds) (erased (Copies (Nat) ys ds) cp) (erased (Array (Copy (Nat)) ds) a)
    (erased (Coercible (Unique) (Array (Copy (U62)) us) b (Unique) (Array (Copy (Nat)) ds) a) c))
  (let-match erased rel (RCons x p rest us1 r1)
    ((RNil)
      (let-match erased b (ANil _))
      (values (Nil _) (CopiesNil _) (ANil _) (coercible-ctor _ ANil (Copy (U62)) (Copy (Nat))))))
  (let-match erased b (ACons _ _ hd tl))
  (let ((erased ds1) (erased cp1) (erased a1) (erased c1)) (from-u62 rest us1 r1 tl))
  (values (Cons _ (MkCopy _ x) ds1) (CopiesCons _ x rest ds1 cp1) (ACons _ _ (MkCopy _ x) a1)
    (coercible-ctor _ ACons (Copy (U62)) (Copy (Nat)) us1 ds1
      (coercible-sym (coercible-ctor _ MkCopy (Nat) (U62) (coercible-wrap _ MkU62 x p))) c1)))

(def-fns _ $ (erased rel-nth : (erased (List (Nat)) xs) (erased (List (Copy (U62))) us) (erased (Rel xs us) rel)
    (erased (Nat) i x) (subterm erased (Nth (Nat) xs i x) nth) ->
    (erased (Lt x u62-modulus) p) (erased (Nth (Copy (U62)) us i (MkCopy (U62) (MkU62 x p))) n))
  (let-match erased rel (RCons y p rest us1 r1) (absurd (RNil) nth))
  (let-match erased nth (NthThere _ _ _ i1 _ nth1) ((NthHere _ _ _) (values p (NthHere _ _ us1))))
  (let ((erased q) (erased n1)) (rel-nth rest us1 r1 i1 x nth1))
  (values q (NthThere _ _ _ i1 _ n1)))

(def-fns _ $ (erased rel-set : (erased (List (Nat)) xs) (erased (List (Copy (U62))) us) (erased (Rel xs us) rel)
    (erased (Nat) i y) (erased (Lt y u62-modulus) q) (erased (List (Copy (U62))) us2)
    (subterm erased (SetNth (Copy (U62)) us i (MkCopy (U62) (MkU62 y q)) us2) s) ->
    (erased (List (Nat)) xs2) (erased (SetNth (Nat) xs i y xs2) s2) (erased (Rel xs2 us2) r2))
  (let-match erased rel (RCons x p rest us1 r1) (absurd (RNil) s))
  (let-match erased s (SetThere _ _ _ i1 _ us3 s1)
    ((SetHere _ _ _ _) (values (Cons _ y rest) (SetHere _ x y rest) (RCons y q rest us1 r1))))
  (let ((erased xs3) (erased s3) (erased r3)) (rel-set rest us1 r1 i1 y q us3 s1))
  (values (Cons _ x xs3) (SetThere _ x rest i1 y xs3 s3) (RCons x p xs3 us3 r3)))

(def-fns _ $ (many get : (erased (List (Nat)) xs) (erased (List (Copy (U62))) us) (erased (Rel xs us) rel)
    (erased (Nat) n) (erased (Length (Nat) xs n) len) (unique (Array (Copy (U62)) us) a) (many (Nat) i) (erased (Lt i n) lt) ->
    (many (Nat) v) (erased (Nth (Nat) xs i v) nth) (erased (Lt v u62-modulus) pv) (unique a is r at a))
  (let ((erased x) (erased nx)) (nth-exists _ _ _ _ len lt))
  (let ((erased p) (erased nu)) (rel-nth _ _ rel _ _ nx))
  (let ((many w) (unique r)) (array-get _ _ a i _ nu))
  (let-match many w (MkU62 v _))
  (values v nx p r))

(def-fns _ $ (many swap : (erased (List (Nat)) xs) (erased (List (Copy (U62))) us) (erased (Rel xs us) rel)
    (erased (Nat) n) (erased (Length (Nat) xs n) len) (unique (Array (Copy (U62)) us) a)
    (many (Nat) i j) (erased (Lt i j) ij) (many (Nat) x y) (erased (Nth (Nat) xs i x) nx) (erased (Nth (Nat) xs j y) ny) ->
    (erased (List (Nat)) ys) (erased (List (Copy (U62))) us2) (erased (Swap xs i j ys) sw) (erased (Rel ys us2) rel2)
    (erased (Length (Nat) ys n) len2) (unique (Array (Copy (U62)) us2) r at a))
  (let ((erased pi) (erased nui)) (rel-nth _ _ rel _ _ nx))
  (let ((erased pj) (erased nuj)) (rel-nth _ _ rel _ _ ny))
  (let ((erased us1) (unique a1) (erased t1))
    (array-place-imm _ _ a i (MkCopy (U62) (MkU62 y pj)) _ nui (ImmCopy (U62) (ImmU62))))
  (let ((erased zs) (erased s1) (erased rel1)) (rel-set _ _ rel _ _ _ _ t1))
  (let ((erased us2) (unique a2) (erased t2))
    (array-place-imm _ _ a1 j (MkCopy (U62) (MkU62 x pi)) _ (setnth-nth-gt _ _ _ _ _ _ _ t1 nuj ij) (ImmCopy (U62) (ImmU62))))
  (let ((erased ys) (erased s2) (erased rel2)) (rel-set _ _ rel1 _ _ _ _ t2))
  (values ys us2 (MkSwap _ i j x y zs ys nx ny s1 s2) rel2
    (setnth-length _ _ _ _ _ _ s2 (setnth-length _ _ _ _ _ _ s1 len)) a2))

(def-fns _ $ (erased rel-length : (erased (List (Nat)) xs) (erased (List (Copy (U62))) us) (subterm erased (Rel xs us) rel)
    (erased (Nat) n) (erased (Length (Copy (U62)) us n) len) -> (erased (Length (Nat) xs n) r))
  (let-match erased rel (RCons x p rest us1 r1) ((RNil) (let-match erased len (LengthNil _)) (LengthNil _)))
  (let-match erased len (LengthCons _ _ _ n1 len1))
  (LengthCons _ x rest n1 (rel-length rest us1 r1 n1 len1)))
