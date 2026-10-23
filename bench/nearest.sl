(def-fns _ $ (many not : (many (Bool) b) -> (many (Bool) r))
  (match many b _ ((BTrue) (BFalse)) ((BFalse) (BTrue))))

(def-fns _ $ (many and : (many (Bool) a) (many (Bool) b) -> (many (Bool) r))
  (match many a _ ((BTrue) b) ((BFalse) (BFalse))))

(def-fns _ $ (many cmp-is-eq : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Bool) r))
  (match many c _ ((CEq _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many cmp-is-lt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Bool) r))
  (match many c _ ((CLt _ _ _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many nat-lt : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (cmp-is-lt _ _ _ _ $ nat-cmp a b))

(def-fns _ $ (many nat-eq : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (cmp-is-eq _ _ _ _ $ nat-cmp a b))

(def-fns _ $ (many char-code : (many (Char) c) -> (many (Nat) n))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k _))
  k)

(def-fns _ $ (many char-of-code : (many (Nat) n) -> (many (Char) c))
  (match many (lt-dec n u8-modulus) _
    ((Yes _ _ p) (MkChar $ MkU8 n p))
    ((No _ _ _) #\x00)))

(def-fns _ $ (many char-eq : (many (Char) a) (many (Char) b) -> (many (Bool) r))
  (cmp-is-eq _ _ _ _ $ char-cmp a b))

(def-fns _ $ (many char-is : (many (Char) c) (many (Nat) code) -> (many (Bool) r))
  (nat-eq (char-code c) code))

(def-fns _ $ (many char-between : (many (Char) c) (many (Nat) lo) (many (Nat) hi) -> (many (Bool) r))
  (let ((many n)) $ char-code c)
  (and (not $ nat-lt n lo) $ not $ nat-lt hi n))

(def-fns _ $ (many rope-str at flatten : (many (Rope) r) -> (many (String) s))
  (let ((many s) (erased _)) (delegate (flatten r)))
  s)

(def-fns _ $ (many str-is-empty : (many (String) s) -> (many (Bool) r))
  (match many s _ ((SNil) (BTrue)) ((SCons _ _) (BFalse))))

(def-fns _ $ (many str-cat : (many (String) a) (many (String) b) -> (many (String) c))
  (str-append a b))

(def-fns _ $ (many str-cat3 : (many (String) a) (many (String) b) (many (String) c) -> (many (String) d))
  (str-append a $ str-append b c))

(def-fns _ $ (many str-until-onto : (many (Rope) acc) (subterm many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after))
  (let-match many s (SCons c rest) ((SNil) (values (rope-str acc) (None _))))
  (match many (char-is c code) _
    ((BTrue) (values (rope-str acc) (Some _ rest)))
    ((BFalse) (tail (str-until-onto (RCat acc $ RChar c) rest code)))))

(def-fns _ $ (many str-until : (many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after))
  (str-until-onto (REmpty) s code))

(def-fns _ $ (many str-split-fuel : (subterm many (Nat) fuel) (many (String) s) (many (Nat) code) -> (many (List $ String) r))
  (let ((many b) (many a)) (str-until s code))
  (let-match many a (Some _ rest) ((None _) (Cons _ b $ Nil _)))
  (match many fuel _
    ((Zero) (Cons _ b $ Nil _))
    ((Succ f) (Cons _ b $ notail $ str-split-fuel f rest code))))

(def-fns _ $ (many split-on : (many (String) s) (many (Nat) code) -> (many (List $ String) r))
  (let ((many n) (erased _)) (str-length s))
  (str-split-fuel n s code))

(def-fns _ $ (many list-rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) r))
  (match many xs _
    ((Nil _) acc)
    ((Cons _ x rest) (tail $ list-rev-onto _ rest $ Cons _ x acc))))

(def-fns _ $ (many list-rev : (erased Type A) (many (List A) xs) -> (many (List A) r))
  (list-rev-onto _ xs $ Nil _))

(def-fns _ $ (many list1 : (erased Type A) (many A x) -> (many (List A) r))
  (Cons _ x $ Nil _))

(def-fns _ $ (many join-strs : (subterm many (List $ String) xs) (many (String) sep) -> (many (String) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) ""))
  (match many rest _ ((Nil _) x) ((Cons _ _ _) (str-cat3 x sep $ notail $ join-strs rest sep))))

(def-fns _ $ (many nat-min : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many (nat-lt a b) _ ((BTrue) a) ((BFalse) b)))

(def-fns _ $ (many char-lower : (many (Char) c) -> (many (Char) r))
  (match many (char-between c 65 90) _ ((BTrue) (char-of-code $ nat-add (char-code c) 32)) ((BFalse) c)))

(def-fns _ $ (many char-eq-nocase : (many (Char) a) (many (Char) b) -> (many (Bool) r))
  (char-eq (char-lower a) (char-lower b)))

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

(def-fns _ $ (many distance : (many (String) a) (many (String) b) -> (many (Nat) d))
  (let ((many first)) (distance-first-row b 0))
  (let-match many (list-rev _ $ distance-rows a (None _) b 0 first first) (Cons _ d _) ((Nil _) 0))
  d)

(def-fns _ $ (many nearest-names : (many (String) name) (subterm many (List $ String) xs) -> (many (Maybe $ Nat) best) (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (None _) (Nil _))))
  (let ((many best) (many ties)) (notail $ nearest-names name rest))
  (let ((many d)) (distance name x))
  (let-match many best (Some _ b) ((None _) (values (Some _ d) $ list1 _ x)))
  (match many (nat-lt d b) _
    ((BTrue) (values (Some _ d) $ list1 _ x))
    ((BFalse) (values best $ match many (nat-eq d b) (((List $ String) _)) ((BTrue) (Cons _ x ties)) ((BFalse) ties)))))

(def-fns _ $ (many drop-empty : (subterm many (List $ String) xs) -> (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (match many (str-is-empty x) _ ((BTrue) (tail $ drop-empty rest)) ((BFalse) (Cons _ x $ notail $ drop-empty rest))))

(def-fns _ $ (many nearest-line : (many (String) word-text) (many (String) names-text) -> (many (String) r))
  (let-match many (split-on word-text 10) (Cons _ word _) ((Nil _) ""))
  (let ((many _) (many ties)) $ nearest-names word $ drop-empty $ split-on names-text 10)
  (match many ties _ ((Nil _) "") ((Cons _ _ _) (str-cat (join-strs ties " ") "\n"))))

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))
(let ((many d2)) (lt-dec 2 u8-modulus))
(comptime-match many d2 (Yes za2 zb2 zp2))
(let ((many code2)) (MkU8 2 zp2))

(def-fns _ $ (many fail : (erased (Level) Q) (unique (World) w) (many (String) m) (many (U8) code) -> (unique (World) w2 at w) (unique (Program Q) p))
  (let ((unique w1) (many _)) (world-do _ w (WriteErr m)))
  (values w1 (Exit Q code)))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let-match many args (Cons _ names-path rest) ((Nil _) (fail P w1 "usage: nearest NAMES-FILE WORD-FILE\n" code2)))
  (let-match many rest (Cons _ word-path _) ((Nil _) (fail P w1 "usage: nearest NAMES-FILE WORD-FILE\n" code2)))
  (let ((unique w2) (many names)) (world-do _ w1 (ReadFile names-path)))
  (let-match many names (Ok _ names-text) ((Fail _ m) (fail P w2 (str-cat m "\n") code1)))
  (let ((unique w3) (many word)) (world-do _ w2 (ReadFile word-path)))
  (let-match many word (Ok _ word-text) ((Fail _ m) (fail P w3 (str-cat m "\n") code1)))
  (let ((unique w4) (many _)) (world-do _ w3 (WriteOut $ nearest-line word-text names-text)))
  (values w4 (Exit P code0)))

(Continue P start)
