(def-fns _ $ (many and : (many (Bool) a) (many (Bool) b) -> (many (Bool) r))
  (match many a _ ((BTrue) b) ((BFalse) (BFalse))))

(def-fns _ $ (many not : (many (Bool) b) -> (many (Bool) r))
  (match many b _ ((BTrue) (BFalse)) ((BFalse) (BTrue))))

(def-fns _ $ (many cmp-is : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) (many (Nat) i) -> (many (Bool) r))
  (match many c _
    ((CLt _ _ _ _ _) (match many i _ ((Zero) (BTrue)) (else (BFalse))))
    ((CEq _ _ _) (match many i _ ((Succ _) (BTrue)) (else (BFalse))))
    ((CGt _ _ _ _ _) (BFalse))))

(def-fns _ $ (many nat-lt : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (cmp-is _ _ _ _ (nat-cmp a b) 0))

(def-fns _ $ (many nat-eq : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (cmp-is _ _ _ _ (nat-cmp a b) 1))

(def-fns _ $ (many nat-min : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many (nat-lt a b) _ ((BTrue) a) ((BFalse) b)))

(def-fns _ $ (many char-code : (many (Char) c) -> (many (Nat) n))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k _))
  k)

(def-fns _ $ (many char-lower-code : (many (Char) c) -> (many (Nat) r))
  (let ((many n)) (char-code c))
  (match many (and (not $ nat-lt n 65) (not $ nat-lt 90 n)) _ ((BTrue) (nat-add n 32)) ((BFalse) n)))

(def-fns _ $ (many char-eq-nocase : (many (Char) a) (many (Char) b) -> (many (Bool) r))
  (nat-eq (char-lower-code a) (char-lower-code b)))

(def-fns _ $ (many distance-first-row : (subterm many (String) bs) (many (Nat) j) -> (many (List $ Nat) r))
  (Cons _ j $ match many bs (((List $ Nat) _)) ((SNil) (Nil _)) ((SCons _ rest) (notail $ distance-first-row rest $ Succ j))))

(def-fns _ $ (many distance-swap : (many (Char) c) (many (Maybe $ Char) cp) (many (Char) bc) (many (Maybe $ Char) bp) (many (List $ Nat) up2) -> (many (Maybe $ Nat) r))
  (let-match many cp (Some _ ap) ((None _) (None _)))
  (let-match many bp (Some _ bq) ((None _) (None _)))
  (let-match many up2 (Cons _ q _) ((Nil _) (None _)))
  (match many (and (char-eq-nocase c bq) $ char-eq-nocase ap bc) _ ((BTrue) (Some _ q)) ((BFalse) (None _))))

(def-fns _ $ (many distance-row : (many (Char) c) (many (Maybe $ Char) cp) (subterm many (String) bs) (many (Maybe $ Char) bp)
    (many (List $ Nat) up) (many (List $ Nat) up2) (many (Nat) left) -> (many (List $ Nat) r))
  (let-match many bs (SCons bc rest) ((SNil) (Nil _)))
  (let-match many up (Cons _ diag up-rest) ((Nil _) (Nil _)))
  (let-match many up-rest (Cons _ above _) ((Nil _) (Nil _)))
  (let ((many best)) (nat-min (Succ $ nat-min above left) $ match many (char-eq-nocase c bc) (((Nat) _)) ((BTrue) diag) ((BFalse) (Succ diag))))
  (let ((many here)) (match many (distance-swap c cp bc bp up2) (((Nat) _)) ((Some _ q) (nat-min best $ Succ q)) ((None _) best)))
  (let ((many up2-next)) (match many bp (((List $ Nat) _)) ((None _) up2) ((Some _ _) (match many up2 (((List $ Nat) _)) ((Nil _) up2) ((Cons _ _ r2) r2)))))
  (Cons _ here $ notail $ distance-row c cp rest (Some _ bc) up-rest up2-next here))

(def-fns _ $ (many distance-rows : (subterm many (String) xs) (many (Maybe $ Char) cp) (many (String) b) (many (Nat) i) (many (List $ Nat) up) (many (List $ Nat) up2) -> (many (List $ Nat) r))
  (let-match many xs (SCons c rest) ((SNil) up))
  (let ((many row)) (Cons _ (Succ i) $ distance-row c cp b (None _) up up2 (Succ i)))
  (tail $ distance-rows rest (Some _ c) b (Succ i) row up))

(def-fns _ $ (many last : (subterm many (List $ Nat) xs) -> (many (Nat) r))
  (let-match many xs (Cons _ x rest) ((Nil _) 0))
  (match many rest _ ((Nil _) x) ((Cons _ _ _) (tail $ last rest))))

(def-fns _ $ (many distance : (many (String) a) (many (String) b) -> (many (Nat) d))
  (let ((many first)) (distance-first-row b 0))
  (last $ distance-rows a (None _) b 0 first first))

(def-fns _ $ (many nearest-names : (many (String) name) (subterm many (List $ String) xs) -> (many (Maybe $ Nat) best) (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (None _) (Nil _))))
  (let ((many best) (many ties)) (notail $ nearest-names name rest))
  (let ((many d)) (distance name x))
  (let-match many best (Some _ b) ((None _) (values (Some _ d) (Cons _ x $ Nil _))))
  (match many (nat-lt d b) _
    ((BTrue) (values (Some _ d) (Cons _ x $ Nil _)))
    ((BFalse) (values best $ match many (nat-eq d b) (((List $ String) _)) ((BTrue) (Cons _ x ties)) ((BFalse) ties)))))
