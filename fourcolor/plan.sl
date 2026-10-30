(def-adts $ (Mem : (Type A) ((List A) xs) (A x) -> Type)
  enum
  (many MemHere : (erased Type A) (erased A x) (erased (List A) xs) -> (Mem A (Cons A x xs) x))
  (many MemThere : (erased Type A) (erased A x y) (erased (List A) xs) (erased (Mem A xs x) p) -> (Mem A (Cons A y xs) x)))

; R relates x to every entry of ys.
(def-adts $ (AllR : (Type A) (Type B) ((TyCtor (A x) (B y) -> Type) R) (A x) ((List B) ys) -> Type)
  enum
  (many ARNil : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) -> (AllR A B R x (Nil B)))
  (many ARCons : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List B) ys)
      (erased (R x y) h) (erased (AllR A B R x ys) rest) -> (AllR A B R x (Cons B y ys))))

; R relates each entry of xs to every later one.
(def-adts $ (PW : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) -> Type)
  enum
  (many PWNil : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) -> (PW A R (Nil A)))
  (many PWCons : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x) (erased (List A) xs)
      (erased (AllR A A R x xs) h) (erased (PW A R xs) rest) -> (PW A R (Cons A x xs))))

; R relates each entry of xs to each entry of ys.
(def-adts $ (Cross : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) ((List A) ys) -> Type)
  enum
  (many CrNil : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased (List A) ys) -> (Cross A R (Nil A) ys))
  (many CrCons : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x) (erased (List A) xs ys)
      (erased (AllR A A R x ys) h) (erased (Cross A R xs ys) rest) -> (Cross A R (Cons A x xs) ys)))

; zs is ys with x put somewhere.
(def-adts $ (Ins : (Type A) (A x) ((List A) ys) ((List A) zs) -> Type)
  enum
  (many InsH : (erased Type A) (erased A x) (erased (List A) ys) -> (Ins A x ys (Cons A x ys)))
  (many InsT : (erased Type A) (erased A x y) (erased (List A) ys zs) (erased (Ins A x ys zs) p) -> (Ins A x (Cons A y ys) (Cons A y zs))))

(def-fns _ $ (erased allr-mem : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List B) ys)
    (subterm erased (AllR A B R x ys) h) (erased (Mem B ys y) m) -> (erased (R x y) r))
  (let-match erased h (ARCons _ _ _ _ z zs hz h1) (absurd (ARNil _ _ _ _) m))
  (let-match erased m (MemThere _ _ _ _ m1) ((MemHere _ _ _) hz))
  (allr-mem A B R x y zs h1 m1))

(def-fns _ $ (erased allr-split : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased (List B) xs ys zs)
    (subterm erased (LApp B xs ys zs) a) (erased (AllR A B R x zs) h) -> (erased (AllR A B R x xs) h1) (erased (AllR A B R x ys) h2))
  (let-match erased a (LAppCons _ y xs1 _ zs1 a1) ((LAppNil _ _) (values (ARNil A B R x) h)))
  (let-match erased h (ARCons _ _ _ _ _ _ hy h3))
  (let ((erased h4) (erased h5)) (allr-split A B R x xs1 ys zs1 a1 h3))
  (values (ARCons A B R x y xs1 hy h4) h5))

(def-fns _ $ (erased allr-join : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased (List B) xs ys zs)
    (subterm erased (LApp B xs ys zs) a) (erased (AllR A B R x xs) h1) (erased (AllR A B R x ys) h2) -> (erased (AllR A B R x zs) h))
  (let-match erased a (LAppCons _ y xs1 _ zs1 a1) ((LAppNil _ _) h2))
  (let-match erased h1 (ARCons _ _ _ _ _ _ hy h3))
  (ARCons A B R x y zs1 hy (allr-join A B R x xs1 ys zs1 a1 h3 h2)))

(def-fns _ $ (erased allr-ins : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List B) ys zs)
    (subterm erased (Ins B y ys zs) p) (erased (R x y) hy) (erased (AllR A B R x ys) h) -> (erased (AllR A B R x zs) r))
  (let-match erased p (InsT _ _ z ys1 zs1 p1) ((InsH _ _ _) (ARCons A B R x y ys hy h)))
  (let-match erased h (ARCons _ _ _ _ _ _ hz h1))
  (ARCons A B R x z zs1 hz (allr-ins A B R x y ys1 zs1 p1 hy h1)))

(def-fns _ $ (erased cross-split : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased (List A) xs ys zs ws)
    (subterm erased (Cross A R ws zs) c) (erased (LApp A xs ys ws) a) -> (erased (Cross A R xs zs) c1) (erased (Cross A R ys zs) c2))
  (let-match erased a (LAppCons _ x xs1 _ ws1 a1) ((LAppNil _ _) (values (CrNil A R zs) c)))
  (let-match erased c (CrCons _ _ _ _ _ h c3))
  (let ((erased c4) (erased c5)) (cross-split A R xs1 ys zs ws1 c3 a1))
  (values (CrCons A R x xs1 zs h c4) c5))

(def-fns _ $ (erased cross-join : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased (List A) xs ys zs ws)
    (subterm erased (LApp A xs ys ws) a) (erased (Cross A R xs zs) c1) (erased (Cross A R ys zs) c2) -> (erased (Cross A R ws zs) c))
  (let-match erased a (LAppCons _ x xs1 _ ws1 a1) ((LAppNil _ _) c2))
  (let-match erased c1 (CrCons _ _ _ _ _ h c3))
  (CrCons A R x ws1 zs h (cross-join A R xs1 ys zs ws1 a1 c3 c2)))

(def-fns _ $ (erased pw-split : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased (List A) xs ys zs)
    (subterm erased (LApp A xs ys zs) a) (erased (PW A R zs) p) ->
    (erased (PW A R xs) p1) (erased (PW A R ys) p2) (erased (Cross A R xs ys) c))
  (let-match erased a (LAppCons _ x xs1 _ zs1 a1) ((LAppNil _ _) (values (PWNil A R) p (CrNil A R ys))))
  (let-match erased p (PWCons _ _ _ _ h p3))
  (let ((erased h1) (erased h2)) (allr-split A A R x xs1 ys zs1 a1 h))
  (let ((erased p4) (erased p5) (erased c1)) (pw-split A R xs1 ys zs1 a1 p3))
  (values (PWCons A R x xs1 h1 p4) p5 (CrCons A R x xs1 ys h2 c1)))

(def-fns _ $ (erased pw-join : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased (List A) xs ys zs)
    (subterm erased (LApp A xs ys zs) a) (erased (PW A R xs) p1) (erased (PW A R ys) p2) (erased (Cross A R xs ys) c) -> (erased (PW A R zs) p))
  (let-match erased a (LAppCons _ x xs1 _ zs1 a1) ((LAppNil _ _) p2))
  (let-match erased p1 (PWCons _ _ _ _ h p3))
  (let-match erased c (CrCons _ _ _ _ _ h2 c1))
  (PWCons A R x zs1 (allr-join A A R x xs1 ys zs1 a1 h h2) (pw-join A R xs1 ys zs1 a1 p3 p2 c1)))

(def-fns _ $ (erased mem-split : (erased Type A) (erased A x) (erased (List A) xs ys zs)
    (subterm erased (LApp A xs ys zs) a) (erased (Mem A zs x) m) -> (erased (Or (Mem A xs x) (Mem A ys x)) r))
  (let-match erased a (LAppCons _ y xs1 _ zs1 a1) ((LAppNil _ _) (OrR _ _ m)))
  (let-match erased m (MemThere _ _ _ _ m1) ((MemHere _ _ _) (OrL _ _ (MemHere A x xs1))))
  (let-match erased (mem-split A x xs1 ys zs1 a1 m1) (OrL _ _ m2) ((OrR _ _ m3) (OrR _ _ m3)))
  (OrL _ _ (MemThere A x y xs1 m2)))

(def-fns _ $ (erased mem-left : (erased Type A) (erased A x) (erased (List A) xs ys zs)
    (subterm erased (LApp A xs ys zs) a) (erased (Mem A xs x) m) -> (erased (Mem A zs x) r))
  (let-match erased a (LAppCons _ y xs1 _ zs1 a1) (absurd (LAppNil _ _) m))
  (let-match erased m (MemThere _ _ _ _ m1) ((MemHere _ _ _) (MemHere A x zs1)))
  (MemThere A x y zs1 (mem-left A x xs1 ys zs1 a1 m1)))

(def-fns _ $ (erased mem-right : (erased Type A) (erased A x) (erased (List A) xs ys zs)
    (subterm erased (LApp A xs ys zs) a) (erased (Mem A ys x) m) -> (erased (Mem A zs x) r))
  (let-match erased a (LAppCons _ y xs1 _ zs1 a1) ((LAppNil _ _) m))
  (MemThere A x y zs1 (mem-right A x xs1 ys zs1 a1 m)))

(def-fns _ $ (erased mem-ins : (erased Type A) (erased A x y) (erased (List A) ys zs)
    (subterm erased (Ins A y ys zs) p) (erased (Or (Eq A x y) (Mem A ys x)) m) -> (erased (Mem A zs x) r))
  (let-match erased p (InsT _ _ z ys1 zs1 p1)
    ((InsH _ _ _)
      (let-match erased m (OrR _ _ m1) ((OrL _ _ e) (let-match erased e (Refl _ _)) (MemHere A x ys)))
      (MemThere A x y ys m1)))
  (let-match erased m (OrR _ _ m1) ((OrL _ _ e) (MemThere A x z zs1 (mem-ins A x y ys1 zs1 p1 (OrL _ _ e)))))
  (let-match erased m1 (MemThere _ _ _ _ m2) ((MemHere _ _ _) (MemHere A x zs1)))
  (MemThere A x z zs1 (mem-ins A x y ys1 zs1 p1 (OrR _ _ m2))))

(def-fns _ $ (erased lex-cmp : (erased (Point) p q) -> (erased (Cmp (Point) LexLt p q) c))
  (let-match erased p (MkPoint px py))
  (let-match erased q (MkPoint qx qy))
  (let-match erased (nat-cmp px qx) (CEq _ _ _)
    ((CLt _ _ _ _ l) (CLt _ _ p q (LexX px py qx qy l)))
    ((CGt _ _ _ _ l) (CGt _ _ p q (LexX qx qy px py l))))
  (match erased (nat-cmp py qy) _
    ((CLt _ _ _ _ l) (CLt _ _ p q (LexY px py qy l)))
    ((CGt _ _ _ _ l) (CGt _ _ p q (LexY px qy py l)))
    ((CEq _ _ _) (CEq _ _ p))))

(def-fns _ $ (erased absurd apart-pt-irrefl : (erased (Point) p) (erased (Apart (Point) LexLt p p) d) -> (erased (False) f))
  (match erased d _
    (absurd (ApLt _ _ _ _ l) (lex-irrefl p l))
    (absurd (ApGt _ _ _ _ l) (lex-irrefl p l))))

(def-fns _ $ (erased nth-mem : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A x) (subterm erased (Nth A xs i x) n) -> (erased (Mem A xs x) m))
  (let-match erased n (NthThere _ y ys k1 _ n1) ((NthHere _ _ ys) (MemHere A x ys)))
  (MemThere A x y ys (nth-mem A ys k1 x n1)))

(def-fns _ $ (erased pw-nth : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased (List A) xs) (erased (Nat) i j) (erased A x y)
    (subterm erased (PW A R xs) p) (erased (Nth A xs i x) nx) (erased (Nth A xs j y) ny) (erased (Lt i j) l) -> (erased (R x y) r))
  (let-match erased p (PWCons _ _ z zs h p1) (absurd (PWNil _ _) nx))
  (let-match erased ny (NthThere _ _ _ j1 _ ny1) (absurd (NthHere _ _ _) l))
  (let-match erased nx (NthThere _ _ _ k1 _ nx1) ((NthHere _ _ _) (allr-mem A A R x y zs h (nth-mem A zs j1 y ny1))))
  (let-match erased l (LtS _ _ l1))
  (pw-nth A R zs k1 j1 x y p1 nx1 ny1 l1))

