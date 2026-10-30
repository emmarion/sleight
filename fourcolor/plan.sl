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


(def-fns _ $ (erased off-swap : (erased (Point) a b r) (erased (OffLine a b r) o) -> (erased (OffLine b a r) o2))
  (match erased o _ ((OffLeft _ _ _ l) (OffRight b a r l)) ((OffRight _ _ _ l) (OffLeft b a r l))))

(def-fns _ $ (erased off-rot : (erased (Point) a b r) (erased (OffLine a b r) o) -> (erased (OffLine b r a) o2))
  (match erased o _
    ((OffLeft _ _ _ l) (OffLeft b r a (left-rot a b r l)))
    ((OffRight _ _ _ l) (OffRight b r a (left-rot a r b $ left-rot b a r l)))))

(def-fns _ $ (erased ss-swap : (erased (Point) a b c d) (erased (SameSide a b c d) s) -> (erased (SameSide b a c d) s2))
  (match erased s _ ((BothLeft _ _ _ _ l m) (BothRight b a c d l m)) ((BothRight _ _ _ _ l m) (BothLeft b a c d l m))))

(def-fns _ $ (erased ss-flip : (erased (Point) a b c d) (erased (SameSide a b c d) s) -> (erased (SameSide a b d c) s2))
  (match erased s _ ((BothLeft _ _ _ _ l m) (BothLeft a b d c m l)) ((BothRight _ _ _ _ l m) (BothRight a b d c m l))))

(def-fns _ $ (erased ss-off : (erased (Point) a b c d) (erased (SameSide a b c d) s) -> (erased (OffLine a b c) o))
  (match erased s _ ((BothLeft _ _ _ _ l _) (OffLeft a b c l)) ((BothRight _ _ _ _ l _) (OffRight a b c l))))

(def-fns _ $ (erased compat-flip : (erased (Point) a b c d) (erased (Compatible a b c d) h) -> (erased (Compatible b a c d) r))
  (match erased h _
    ((ShareCA _ _ _ o) (ShareCB b a d (off-swap a b d o)))
    ((ShareCB _ _ _ o) (ShareCA b a d (off-swap a b d o)))
    ((ShareDA _ _ _ o) (ShareDB b a c (off-swap a b c o)))
    ((ShareDB _ _ _ o) (ShareDA b a c (off-swap a b c o)))
    ((SplitByAB _ _ _ _ s oa ob) (SplitByAB b a c d (ss-swap a b c d s) ob oa))
    ((SplitByCD _ _ _ _ oc od s) (SplitByCD b a c d (off-swap a b c oc) (off-swap a b d od) (ss-flip c d a b s)))))

(def-fns _ $ (erased compat-sym : (erased (Point) a b c d) (erased (Compatible a b c d) h) -> (erased (Compatible c d a b) r))
  (match erased h _
    ((ShareCA _ _ _ o) (ShareCA a d b (off-swap d a b $ off-rot b d a $ off-rot a b d o)))
    ((ShareCB _ _ _ o) (ShareDA b d a (off-rot a b d o)))
    ((ShareDA _ _ _ o) (ShareCB c a b (off-rot b c a $ off-rot a b c o)))
    ((ShareDB _ _ _ o) (ShareDB c b a (off-rot a c b $ off-rot b a c $ off-swap a b c o)))
    ((SplitByAB _ _ _ _ s oa ob) (SplitByCD c d a b oa ob s))
    ((SplitByCD _ _ _ _ oc od s) (SplitByAB c d a b s oc od))))

(def-fns _ $ (erased compat-off : (erased (Point) a b c d) (erased (Compatible a b c d) h)
    (erased (Apart (Point) LexLt c a) na) (erased (Apart (Point) LexLt c b) nb) -> (erased (OffLine a b c) o))
  (match erased h _
    (absurd (ShareCA _ _ _ _) (apart-pt-irrefl a na))
    (absurd (ShareCB _ _ _ _) (apart-pt-irrefl b nb))
    ((ShareDA _ _ _ o) o)
    ((ShareDB _ _ _ o) o)
    ((SplitByAB _ _ _ _ s _ _) (ss-off a b c d s))
    ((SplitByCD _ _ _ _ oc _ _) oc)))

(def-fns _ $ (erased compat-all-nth : (erased (Point) a b c d) (erased (List (Edge)) es) (erased (Nat) j)
    (subterm erased (CompatibleAll a b es) h) (erased (Nth (Edge) es j (MkEdge c d)) n) -> (erased (Compatible a b c d) r))
  (let-match erased h (CACons _ _ c1 d1 es1 h1 rest) (absurd (CANil _ _) n))
  (let-match erased n (NthThere _ _ _ j1 _ n1) ((NthHere _ _ _) h1))
  (compat-all-nth a b c d es1 j1 rest n1))

(def-fns _ $ (erased compat-at : (erased (Point) a b c d) (erased (List (Edge)) es) (erased (Nat) i j) (subterm erased (Drawing es) dr)
    (erased (Nth (Edge) es i (MkEdge a b)) ni) (erased (Nth (Edge) es j (MkEdge c d)) nj) (erased (Lt i j) l) -> (erased (Compatible a b c d) r))
  (let-match erased dr (DrawCons a1 b1 es1 _ ca rest) (absurd (DrawNil) ni))
  (let-match erased nj (NthThere _ _ _ j1 _ nj1) (absurd (NthHere _ _ _) l))
  (let-match erased ni (NthThere _ _ _ u2 _ ni1) ((NthHere _ _ _) (compat-all-nth a b c d es1 j1 ca nj1)))
  (let-match erased l (LtS _ _ l1))
  (compat-at a b c d es1 u2 j1 rest ni1 nj1 l1))

; The edge at position m of es joins a and b, written either way round.
(def-adts $ (EdgeIn : ((List (Edge)) es) ((Nat) m) ((Point) a) ((Point) b) -> Type)
  enum
  (many EIFwd : (erased (List (Edge)) es) (erased (Nat) m) (erased (Point) a b) (erased (Nth (Edge) es m (MkEdge a b)) n) -> (EdgeIn es m a b))
  (many EIRev : (erased (List (Edge)) es) (erased (Nat) m) (erased (Point) a b) (erased (Nth (Edge) es m (MkEdge b a)) n) -> (EdgeIn es m a b)))

(def-fns _ $ (erased compat-in-lt : (erased (List (Edge)) es) (erased (Nat) m k) (erased (Point) a b c d) (erased (Drawing es) dr)
    (erased (EdgeIn es m a b) e1) (erased (EdgeIn es k c d) e2) (erased (Lt m k) l) -> (erased (Compatible a b c d) r))
  (match erased e1 _
    ((EIFwd _ _ _ _ n1)
      (match erased e2 _
        ((EIFwd _ _ _ _ n2) (compat-at a b c d es m k dr n1 n2 l))
        ((EIRev _ _ _ _ n2) (compat-sym c d a b $ compat-flip d c a b $ compat-sym a b d c (compat-at a b d c es m k dr n1 n2 l)))))
    ((EIRev _ _ _ _ n1)
      (match erased e2 _
        ((EIFwd _ _ _ _ n2) (compat-flip b a c d (compat-at b a c d es m k dr n1 n2 l)))
        ((EIRev _ _ _ _ n2)
          (compat-sym c d a b $ compat-flip d c a b $ compat-sym a b d c $ compat-flip b a d c (compat-at b a d c es m k dr n1 n2 l)))))))

(def-fns _ $ (erased compat-in : (erased (List (Edge)) es) (erased (Nat) m k) (erased (Point) a b c d) (erased (Drawing es) dr)
    (erased (EdgeIn es m a b) e1) (erased (EdgeIn es k c d) e2) (erased (Apart (Nat) Lt m k) ne) -> (erased (Compatible a b c d) r))
  (match erased ne _
    ((ApLt _ _ _ _ l) (compat-in-lt es m k a b c d dr e1 e2 l))
    ((ApGt _ _ _ _ l) (compat-sym c d a b (compat-in-lt es k m c d a b dr e2 e1 l)))))

(def-fns _ $ (erased nth-inj : (erased (List (Point)) pts) (erased (Nat) i j) (erased (Point) x) (erased (PW (Point) LexLt pts) sp)
    (erased (Nth (Point) pts i x) ni) (erased (Nth (Point) pts j x) nj) -> (erased (Eq (Nat) i j) e))
  (match erased (nat-cmp i j) _
    (absurd (CLt _ _ _ _ l) (lex-irrefl x (pw-nth _ _ pts i j x x sp ni nj l)))
    ((CEq _ _ _) (Refl _ i))
    (absurd (CGt _ _ _ _ l) (lex-irrefl x (pw-nth _ _ pts j i x x sp nj ni l)))))

(def-fns _ $ (erased ei-same : (erased (List (Edge)) es) (erased (Nat) m) (erased (Point) a b p q)
    (erased (EdgeIn es m a b) e1) (erased (EdgeIn es m p q) e2) -> (erased (Or (Eq (Point) p a) (Eq (Point) p b)) r))
  (match erased e1 _
    ((EIFwd _ _ _ _ n1)
      (match erased e2 _
        ((EIFwd _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (OrL _ _ (Refl _ p)))
        ((EIRev _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (OrR _ _ (Refl _ p)))))
    ((EIRev _ _ _ _ n1)
      (match erased e2 _
        ((EIFwd _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (OrR _ _ (Refl _ p)))
        ((EIRev _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (OrL _ _ (Refl _ p)))))))

; A drawn point strictly inside the span of a drawn edge is off its line.
(def-fns _ $ (erased offline-at : (erased (List (Edge)) es) (erased (Drawing es) dr) (erased (Nat) m mp) (erased (Point) a b p q)
    (erased (EdgeIn es m a b) e1) (erased (EdgeIn es mp p q) e2) (erased (LexLt a p) lap) (erased (LexLt p b) lpb) -> (erased (OffLine a b p) o))
  (match erased (cmp-eq _ _ _ _ (nat-cmp m mp)) _
    ((Unequal _ _ _ _ ne) (compat-off a b p q (compat-in es m mp a b p q dr e1 e2 ne) (ApGt _ _ p a lap) (ApLt _ _ p b lpb)))
    (absurd (Equal _ _ _)
      (match erased (ei-same es m a b p q e1 e2) _
        (absurd (OrL _ _ e) (let-match erased e (Refl _ _)) (lex-irrefl p lap))
        (absurd (OrR _ _ e) (let-match erased e (Refl _ _)) (lex-irrefl p lpb))))))

; The sweep is at point p, number k of pts, an end of the edge mp of es.
(def-adts $ (Here : ((List (Edge)) es) ((List (Point)) pts) ((Nat) k) ((Point) p) -> Type)
  enum
  (many MkHere : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
      (erased (Drawing es) dr) (erased (PW (Point) LexLt pts) sp) (erased (Nth (Point) pts k p) np)
      (erased (Nat) mp) (erased (Point) q) (erased (EdgeIn es mp p q) ep) -> (Here es pts k p)))

(def-adts $ (Ctx : -> Type)
  enum
  (many MkCtx : (many (List (Edge)) es) (many (List (Point)) pts) (many (Nat) k) -> (Ctx)))

; The edge ab, with a before b, is crossed by the sweep between points k-1 and k.
(def-adts $ (Act : ((Ctx) c) ((Edge) e) -> Type)
  enum
  (many MkAct : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) a b)
      (erased (Nat) i j m) (erased (EdgeIn es m a b) ei) (erased (Nth (Point) pts i a) na) (erased (Nth (Point) pts j b) nb)
      (erased (Lt i k) lik) (erased (Lt k (Succ j)) lkj) -> (Act (MkCtx es pts k) (MkEdge a b))))

(def-adts $ (Abv : ((Point) p) ((Edge) e) -> Type)
  enum
  (many MkAbv : (erased (Point) a b p) (erased (LexLt a p) l1) (erased (LexLt p b) l2) (erased (Left a b p) h) -> (Abv p (MkEdge a b))))

(def-adts $ (AtP : ((Point) p) ((Edge) e) -> Type)
  enum
  (many MkAtP : (erased (Point) a p) (erased (LexLt a p) l1) -> (AtP p (MkEdge a p))))

(def-adts $ (Und : ((Point) p) ((Edge) e) -> Type)
  enum
  (many MkUnd : (erased (Point) a b p) (erased (LexLt a p) l1) (erased (LexLt p b) l2) (erased (Left b a p) h) -> (Und p (MkEdge a b))))

(def-adts $ (Side : ((Point) p) ((Edge) e) -> Type)
  enum
  (many StA : (erased (Point) p) (erased (Edge) e) (erased (Abv p e) s) -> (Side p e))
  (many StT : (erased (Point) p) (erased (Edge) e) (erased (AtP p e) s) -> (Side p e))
  (many StU : (erased (Point) p) (erased (Edge) e) (erased (Und p e) s) -> (Side p e)))

(def-fns _ $ (erased stat-of : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
    (erased (Edge) e) (erased (Here es pts k p) hr) (erased (Act (MkCtx es pts k) e) ac) -> (erased (Side p e) s))
  (let-match erased hr (MkHere _ _ _ _ dr sp np mp q ep))
  (let-match erased ac (MkAct _ _ _ a b i j m ei na nb lik lkj))
  (let ((erased lap)) (pw-nth _ _ pts i k a p sp na np lik))
  (match erased (nat-cmp k j) _
    ((CEq _ _ _) (let-match erased (nth-fn _ pts k p b np nb) (Refl _ _)) (StT p e (MkAtP a p lap)))
    ((CLt _ _ _ _ lt)
      (let ((erased lpb)) (pw-nth _ _ pts k j p b sp np nb lt))
      (match erased (offline-at es dr m mp a b p q ei ep lap lpb) _
        ((OffLeft _ _ _ h) (StA p e (MkAbv a b p lap lpb h)))
        ((OffRight _ _ _ h) (StU p e (MkUnd a b p lap lpb h)))))
    (absurd (CGt _ _ _ _ gt) (lt-asym j k gt lkj))))

(def-adts $ (SB : ((Edge) e) ((Edge) f) -> Type)
  enum
  (many MkSB : (erased (Point) a b c d) (erased (Below (MkEdge a b) (MkEdge c d)) bl) (erased (Compatible a b c d) cp)
      -> (SB (MkEdge a b) (MkEdge c d))))

(def-adts $ (TU : ((Point) p) ((Edge) e) -> Type)
  enum
  (many TUT : (erased (Point) p) (erased (Edge) e) (erased (AtP p e) s) -> (TU p e))
  (many TUU : (erased (Point) p) (erased (Edge) e) (erased (Und p e) s) -> (TU p e)))

(def-fns _ $ (erased under-tail : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
    (erased (Edge) x) (erased (List (Edge)) ys) (erased (Here es pts k p) hr) (erased (Und p x) ux)
    (subterm erased (AllR (Edge) (Edge) SB x ys) sb) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) ys) acts) ->
    (erased (AllR (Point) (Edge) Und p ys) r))
  (let-match erased sb (ARCons _ _ _ _ y ys1 sxy sb1) ((ARNil _ _ _ _) (ARNil _ _ _ p)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ay acts1))
  (let-match erased ux (MkUnd a b _ lap lpb hu))
  (let-match erased sxy (MkSB _ _ c d bl cp))
  (let ((erased lab)) (lex-trans a p b lap lpb))
  (ARCons _ _ _ p y ys1
    (match erased (stat-of es pts k p y hr ay) _
      (absurd (StA _ _ s) (let-match erased s (MkAbv _ _ _ lcp lpd ho))
        (sweep-under-over a b c d p bl cp lab (lex-trans c p d lcp lpd) lap lpb lcp lpd hu ho))
      (absurd (StT _ _ s) (let-match erased s (MkAtP _ _ lcp)) (sweep-end-under a b c p bl cp lcp lap lpb hu))
      ((StU _ _ s) s))
    (under-tail es pts k p x ys1 hr ux sb1 acts1)))

(def-fns _ $ (erased at-tail : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
    (erased (Edge) x) (erased (List (Edge)) ys) (erased (Here es pts k p) hr) (erased (AtP p x) tx)
    (subterm erased (AllR (Edge) (Edge) SB x ys) sb) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) ys) acts) ->
    (erased (AllR (Point) (Edge) TU p ys) r))
  (let-match erased sb (ARCons _ _ _ _ y ys1 sxy sb1) ((ARNil _ _ _ _) (ARNil _ _ _ p)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ay acts1))
  (let-match erased tx (MkAtP a _ lap))
  (let-match erased sxy (MkSB _ _ c d bl cp))
  (ARCons _ _ _ p y ys1
    (match erased (stat-of es pts k p y hr ay) _
      (absurd (StA _ _ s) (let-match erased s (MkAbv _ _ _ lcp lpd ho)) (sweep-end-over a p c d bl cp lap lcp lpd ho))
      ((StT _ _ s) (TUT p y s))
      ((StU _ _ s) (TUU p y s)))
    (at-tail es pts k p x ys1 hr tx sb1 acts1)))

(def-fns _ $ (erased split-t : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
    (erased (List (Edge)) xs) (erased (Here es pts k p) hr) (subterm erased (AllR (Point) (Edge) TU p xs) tus)
    (erased (PW (Edge) SB xs) pw) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) xs) acts) ->
    (erased (List (Edge)) r q) (erased (LApp (Edge) r q xs) a) (erased (AllR (Point) (Edge) AtP p r) ats) (erased (AllR (Point) (Edge) Und p q) uns))
  (let-match erased tus (ARCons _ _ _ _ x xs1 tx tus1)
    ((ARNil _ _ _ _) (values (Nil _) (Nil _) (LAppNil _ (Nil _)) (ARNil _ _ _ p) (ARNil _ _ _ p))))
  (let-match erased pw (PWCons _ _ _ _ h pw1))
  (let-match erased acts (ARCons _ _ _ _ _ _ ax acts1))
  (let-match erased tx (TUT _ _ s)
    ((TUU _ _ s) (values (Nil _) xs (LAppNil _ xs) (ARNil _ _ _ p) (ARCons _ _ _ p x xs1 s (under-tail es pts k p x xs1 hr s h acts1)))))
  (let ((erased r1) (erased q) (erased a) (erased ats) (erased uns)) (split-t es pts k p xs1 hr tus1 pw1 acts1))
  (values (Cons _ x r1) q (LAppCons _ x r1 q xs1 a) (ARCons _ _ _ p x r1 s ats) uns))

; The active edges, bottom to top, are those p is above, then those ending at p, then those p is below.
(def-fns _ $ (erased split-a : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
    (erased (List (Edge)) xs) (erased (Here es pts k p) hr) (subterm erased (PW (Edge) SB xs) pw)
    (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) xs) acts) ->
    (erased (List (Edge)) pp r q pr) (erased (LApp (Edge) pp r pr) a1) (erased (LApp (Edge) pr q xs) a2)
    (erased (AllR (Point) (Edge) Abv p pp) abs) (erased (AllR (Point) (Edge) AtP p r) ats) (erased (AllR (Point) (Edge) Und p q) uns))
  (let-match erased pw (PWCons _ _ x xs1 h pw1)
    ((PWNil _ _) (values (Nil _) (Nil _) (Nil _) (Nil _) (LAppNil _ (Nil _)) (LAppNil _ (Nil _)) (ARNil _ _ _ p) (ARNil _ _ _ p) (ARNil _ _ _ p))))
  (let-match erased acts (ARCons _ _ _ _ _ _ ax acts1))
  (match erased (stat-of es pts k p x hr ax) _
    ((StA _ _ s)
      (let ((erased p1) (erased r) (erased q) (erased pr1) (erased a1) (erased a2) (erased abs) (erased ats) (erased uns))
        (split-a es pts k p xs1 hr pw1 acts1))
      (values (Cons _ x p1) r q (Cons _ x pr1) (LAppCons _ x p1 r pr1 a1) (LAppCons _ x pr1 q xs1 a2) (ARCons _ _ _ p x p1 s abs) ats uns))
    ((StT _ _ s)
      (let ((erased r1) (erased q) (erased a) (erased ats) (erased uns))
        (split-t es pts k p xs1 hr (at-tail es pts k p x xs1 hr s h acts1) pw1 acts1))
      (values (Nil _) (Cons _ x r1) q (Cons _ x r1) (LAppNil _ (Cons _ x r1)) (LAppCons _ x r1 q xs1 a) (ARNil _ _ _ p)
        (ARCons _ _ _ p x r1 s ats) uns))
    ((StU _ _ s)
      (values (Nil _) (Nil _) xs (Nil _) (LAppNil _ (Nil _)) (LAppNil _ xs) (ARNil _ _ _ p) (ARNil _ _ _ p)
        (ARCons _ _ _ p x xs1 s (under-tail es pts k p x xs1 hr s h acts1))))))

(def-fns _ $ (erased lapp-nth : (erased Type A) (erased (List A) pre r xs) (erased A e) (erased (Nat) m)
    (subterm erased (LApp A pre (Cons A e r) xs) ap) (erased (Length A pre m) lm) -> (erased (Nth A xs m e) n))
  (let-match erased ap (LAppCons _ x pre1 _ xs1 a1) ((LAppNil _ _) (let-match erased lm (LengthNil _)) (NthHere A e r)))
  (let-match erased lm (LengthCons _ _ _ m1 l1))
  (NthThere A x xs1 m1 e (lapp-nth A pre1 r xs1 e m1 a1 l1)))

(def-fns _ $ (erased lapp-shift : (erased Type A) (erased (List A) pre r xs) (erased A e) (erased (Nat) m)
    (subterm erased (LApp A pre (Cons A e r) xs) ap) (erased (Length A pre m) lm) ->
    (erased (List A) pre2) (erased (LApp A pre2 r xs) ap2) (erased (Length A pre2 (Succ m)) lm2))
  (let-match erased ap (LAppCons _ x pre1 _ xs1 a1)
    ((LAppNil _ _) (let-match erased lm (LengthNil _))
      (values (Cons A e (Nil A)) (LAppCons A e (Nil A) r r (LAppNil A r)) (LengthCons A e (Nil A) (Zero) (LengthNil A)))))
  (let-match erased lm (LengthCons _ _ _ m1 l1))
  (let ((erased pre3) (erased a3) (erased l3)) (lapp-shift A pre1 r xs1 e m1 a1 l1))
  (values (Cons A x pre3) (LAppCons A x pre3 r xs1 a3) (LengthCons A x pre3 (Succ m1) l3)))

; e is ab with a before b in pts, at i and j.
(def-adts $ (Nrm : ((List (Point)) pts) ((Edge) e) ((Point) a) ((Point) b) ((Nat) i) ((Nat) j) -> Type)
  enum
  (many NmF : (erased (List (Point)) pts) (erased (Point) a b) (erased (Nat) i j) (erased (Nth (Point) pts i a) na) (erased (Nth (Point) pts j b) nb)
      (erased (Lt i j) l) -> (Nrm pts (MkEdge a b) a b i j))
  (many NmR : (erased (List (Point)) pts) (erased (Point) a b) (erased (Nat) i j) (erased (Nth (Point) pts i a) na) (erased (Nth (Point) pts j b) nb)
      (erased (Lt i j) l) -> (Nrm pts (MkEdge b a) a b i j)))

(def-adts $ (Pre : ((List (Point)) pts) ((Edge) e) -> Type)
  enum
  (many MkPre : (erased (List (Point)) pts) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j) (erased (Nrm pts e a b i j) nm) -> (Pre pts e)))

(def-fns _ $ (erased norm-ei : (erased (List (Point)) pts) (erased (List (Edge)) es) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j m)
    (erased (Nrm pts e a b i j) nm) (erased (Nth (Edge) es m e) n) -> (erased (EdgeIn es m a b) ei))
  (match erased nm _ ((NmF _ _ _ _ _ _ _ _) (EIFwd es m a b n)) ((NmR _ _ _ _ _ _ _ _) (EIRev es m a b n))))

(def-adts $ (Starts : ((Point) p) ((Edge) e) -> Type)
  enum
  (many MkStarts : (erased (Point) p q) (erased (LexLt p q) l) -> (Starts p (MkEdge p q))))

(def-adts $ (CE : ((Edge) e) ((Edge) f) -> Type)
  enum
  (many MkCE : (erased (Point) a b c d) (erased (Compatible a b c d) h) -> (CE (MkEdge a b) (MkEdge c d))))

; The edge ab is at a position of es at least m.
(def-adts $ (InFrom : ((Ctx) c) ((Edge) e) -> Type)
  enum
  (many MkInFrom : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) m m2) (erased (Point) a b)
      (erased (Lt m (Succ m2)) l) (erased (EdgeIn es m2 a b) ei) -> (InFrom (MkCtx es pts m) (MkEdge a b))))

(def-fns _ $ (erased inf-weaken : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) m) (erased (List (Edge)) xs)
    (subterm erased (AllR (Ctx) (Edge) InFrom (MkCtx es pts (Succ m)) xs) h) -> (erased (AllR (Ctx) (Edge) InFrom (MkCtx es pts m) xs) r))
  (let-match erased h (ARCons _ _ _ _ x xs1 hx h1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased hx (MkInFrom _ _ _ m2 a b l ei))
  (ARCons _ _ _ _ x xs1 (MkInFrom es pts m m2 a b (lt-weaken m m2 (lt-pred m m2 l)) ei) (inf-weaken es pts m xs1 h1)))

(def-fns _ $ (erased ce-from : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Drawing es) dr) (erased (Nat) m) (erased (Point) a b)
    (erased (EdgeIn es m a b) ei) (erased (List (Edge)) xs) (subterm erased (AllR (Ctx) (Edge) InFrom (MkCtx es pts (Succ m)) xs) h) ->
    (erased (AllR (Edge) (Edge) CE (MkEdge a b) xs) r))
  (let-match erased h (ARCons _ _ _ _ x xs1 hx h1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased hx (MkInFrom _ _ _ m2 c d l ej))
  (ARCons _ _ _ _ x xs1 (MkCE a b c d (compat-in es m m2 a b c d dr ei ej (ApLt _ _ m m2 (lt-pred m m2 l)))) (ce-from es pts dr m a b ei xs1 h1)))

(def-fns _ $ (erased below-fan : (erased (Point) p q r) (erased (Below (MkEdge p q) (MkEdge p r)) bl) -> (erased (Left p q r) l))
  (match erased bl _
    (absurd (BelowL _ _ _ _ lt _) (lex-irrefl p lt))
    (absurd (BelowR _ _ _ _ lt _) (lex-irrefl p lt))
    ((BelowS _ _ _ h) h)))

(def-fns _ $ (erased fan-dir : (erased (Point) p q r) (erased (Compatible p q p r) h) (erased (LexLt p q) lq) (erased (LexLt p r) lr) ->
    (erased (OffLine p q r) o))
  (match erased h _
    ((ShareCA _ _ _ o) o)
    (absurd (ShareCB _ _ _ _) (lex-irrefl p lq))
    (absurd (ShareDA _ _ _ _) (lex-irrefl p lr))
    (absurd (ShareDB _ _ _ o) (offline-coll p q p o (coll-same p q)))
    (absurd (SplitByAB _ _ _ _ s _ _) (offline-coll p q p (ss-off p q p r s) (coll-same p q)))
    (absurd (SplitByCD _ _ _ _ o _ _) (offline-coll p q p o (coll-same p q)))))

(def-fns _ $ (erased allr-turn : (erased (Point) p q r) (erased (LexLt p q) lq) (erased (LexLt p r) lr) (erased (Left p q r) h)
    (erased (List (Edge)) xs) (subterm erased (AllR (Edge) (Edge) SB (MkEdge p r) xs) sb) (erased (AllR (Point) (Edge) Starts p xs) st)
    (erased (AllR (Edge) (Edge) CE (MkEdge p q) xs) ce) -> (erased (AllR (Edge) (Edge) SB (MkEdge p q) xs) res))
  (let-match erased sb (ARCons _ _ _ _ y ys sy sb1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased st (ARCons _ _ _ _ _ _ sty st1))
  (let-match erased ce (ARCons _ _ _ _ _ _ cey ce1))
  (let-match erased sty (MkStarts _ z lz))
  (let-match erased sy (MkSB _ _ _ _ bl _))
  (let-match erased cey (MkCE _ _ _ _ cp))
  (ARCons _ _ _ _ y ys (MkSB p q p z (BelowS p q z (left-turn p q r z lq (lex-xle p r lr) (lex-xle p z lz) h (below-fan p r z bl))) cp)
    (allr-turn p q r lq lr h ys sb1 st1 ce1)))

; Inserting an edge from p among edges from p sorted by direction.
(def-fns _ $ (erased ins-fan : (erased (Point) p q) (erased (LexLt p q) lq) (erased (List (Edge)) xs) (subterm erased (PW (Edge) SB xs) pw)
    (erased (AllR (Point) (Edge) Starts p xs) st) (erased (AllR (Edge) (Edge) CE (MkEdge p q) xs) ce) ->
    (erased (List (Edge)) ys) (erased (Ins (Edge) (MkEdge p q) xs ys) ins) (erased (PW (Edge) SB ys) pw2))
  (let ((erased x)) (MkEdge p q))
  (let-match erased pw (PWCons _ _ y xs1 hy pw1)
    ((PWNil _ _) (values (Cons _ x (Nil _)) (InsH _ x (Nil _)) (PWCons _ _ x (Nil _) (ARNil _ _ _ x) (PWNil _ _)))))
  (let-match erased st (ARCons _ _ _ _ _ _ sty st1))
  (let-match erased ce (ARCons _ _ _ _ _ _ cey ce1))
  (let-match erased sty (MkStarts _ r lr))
  (let-match erased cey (MkCE _ _ _ _ cp))
  (let-match erased (fan-dir p q r cp lq lr) (OffRight _ _ _ h)
    ((OffLeft _ _ _ h)
      (values (Cons _ x xs) (InsH _ x xs)
        (PWCons _ _ x xs (ARCons _ _ _ x y xs1 (MkSB p q p r (BelowS p q r h) cp) (allr-turn p q r lq lr h xs1 hy st1 ce1)) pw))))
  (let ((erased ys1) (erased ins1) (erased pw3)) (ins-fan p q lq xs1 pw1 st1 ce1))
  (values (Cons _ y ys1) (InsT _ x y xs1 ys1 ins1)
    (PWCons _ _ y ys1 (allr-ins _ _ _ y x xs1 ys1 ins1 (MkSB p r p q (BelowS p r q (left-rot q p r h)) (compat-sym p q p r cp)) hy) pw3)))

(def-fns _ $ (erased nrm-parts : (erased (List (Point)) pts) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j) (erased (Nrm pts e a b i j) nm) ->
    (erased (Nth (Point) pts i a) na) (erased (Nth (Point) pts j b) nb) (erased (Lt i j) l))
  (match erased nm _ ((NmF _ _ _ _ _ na nb l) (values na nb l)) ((NmR _ _ _ _ _ na nb l) (values na nb l))))

(def-adts $ (LCtx : -> Type)
  enum
  (many MkLCtx : (many (List (Point)) pts) (many (Nat) k) (many (List (Edge)) l) -> (LCtx)))

; Whether the drawn edge e starts at point k, and if so that its normal form is in n.
(def-adts $ (NewC : ((LCtx) c) ((Edge) e) -> Type)
  enum
  (many NcNo : (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Edge)) n) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j)
      (erased (Nrm pts e a b i j) nm) (erased (Apart (Nat) Lt i k) d) -> (NewC (MkLCtx pts k n) e))
  (many NcYes : (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Edge)) n) (erased (Edge) e) (erased (Point) a b) (erased (Nat) j)
      (erased (Nrm pts e a b k j) nm) (erased (Mem (Edge) n (MkEdge a b)) mb) -> (NewC (MkLCtx pts k n) e)))

(def-fns _ $ (erased newc-lift : (erased (List (Point)) pts) (erased (Nat) k) (erased (Edge) x) (erased (List (Edge)) n1 n2 es2)
    (erased (Ins (Edge) x n1 n2) ins) (subterm erased (AllR (LCtx) (Edge) NewC (MkLCtx pts k n1) es2) h) ->
    (erased (AllR (LCtx) (Edge) NewC (MkLCtx pts k n2) es2) r))
  (let-match erased h (ARCons _ _ _ _ e r1 he h1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (ARCons _ _ _ _ e r1
    (match erased he _
      ((NcNo _ _ _ _ a b i j nm d) (NcNo pts k n2 e a b i j nm d))
      ((NcYes _ _ _ _ a b j nm mb) (NcYes pts k n2 e a b j nm (mem-ins _ _ x n1 n2 ins (OrR _ _ mb)))))
    (newc-lift pts k x n1 n2 r1 ins h1)))

; The edges of es2, a suffix of es from position m on, that start at point k, sorted by direction.
(def-fns _ $ (erased scan-new : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p) (erased (Here es pts k p) hr)
    (erased (List (Edge)) pre es2) (erased (Nat) m) (erased (LApp (Edge) pre es2 es) ap) (erased (Length (Edge) pre m) lm)
    (subterm erased (AllR (List (Point)) (Edge) Pre pts es2) prs) ->
    (erased (List (Edge)) n) (erased (PW (Edge) SB n) pw) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts (Succ k)) n) acts)
    (erased (AllR (Point) (Edge) Starts p n) st) (erased (AllR (Ctx) (Edge) InFrom (MkCtx es pts m) n) inf)
    (erased (AllR (LCtx) (Edge) NewC (MkLCtx pts k n) es2) nc))
  (let-match erased hr (MkHere _ _ _ _ dr sp np _ _ _))
  (let-match erased prs (ARCons _ _ _ _ e r pe prs1)
    ((ARNil _ _ _ _) (values (Nil _) (PWNil _ _) (ARNil _ _ _ _) (ARNil _ _ _ _) (ARNil _ _ _ _) (ARNil _ _ _ _))))
  (let ((erased pre2) (erased ap2) (erased lm2)) (lapp-shift _ pre r es e m ap lm))
  (let ((erased n1) (erased pw1) (erased acts1) (erased st1) (erased inf1) (erased nc1)) (scan-new es pts k p hr pre2 r (Succ m) ap2 lm2 prs1))
  (let-match erased pe (MkPre _ _ a b i j nm))
  (let ((erased ei)) (norm-ei pts es e a b i j m nm (lapp-nth _ pre r es e m ap lm)))
  (let ((erased na) (erased nb) (erased l)) (nrm-parts pts e a b i j nm))
  (let ((erased inf2)) (inf-weaken es pts m n1 inf1))
  (let-match erased (cmp-eq _ _ _ _ (nat-cmp i k)) (Equal _ _ _)
    ((Unequal _ _ _ _ d) (values n1 pw1 acts1 st1 inf2 (ARCons _ _ _ _ e r (NcNo pts k n1 e a b i j nm d) nc1))))
  (let-match erased (nth-fn _ pts k a p na np) (Refl _ _))
  (let ((erased lq)) (pw-nth _ _ pts k j p b sp na nb l))
  (let ((erased x)) (MkEdge p b))
  (let ((erased n2) (erased ins) (erased pw2)) (ins-fan p b lq n1 pw1 st1 (ce-from es pts dr m p b ei n1 inf1)))
  (values n2 pw2
    (allr-ins _ _ _ _ x n1 n2 ins (MkAct es pts (Succ k) p b k j m ei na nb (lt-succ k) (LtS k j l)) acts1)
    (allr-ins _ _ _ _ x n1 n2 ins (MkStarts p b lq) st1)
    (allr-ins _ _ _ _ x n1 n2 ins (MkInFrom es pts m m p b (lt-succ m) ei) inf2)
    (ARCons _ _ _ _ e r (NcYes pts k n2 e p b j nm (mem-ins _ x x n1 n2 ins (OrL _ _ (Refl _ x)))) (newc-lift pts k x n1 n2 r ins nc1))))

; ls lists the labels of the starts of the edges of l.
(def-adts $ (Labels : ((List (Point)) pts) ((List (Edge)) l) ((List (Nat)) ls) -> Type)
  enum
  (many LbNil : (erased (List (Point)) pts) -> (Labels pts (Nil (Edge)) (Nil (Nat))))
  (many LbCons : (erased (List (Point)) pts) (erased (Point) a b) (erased (Nat) i) (erased (Nth (Point) pts i a) na)
      (erased (List (Edge)) l) (erased (List (Nat)) ls) (erased (Labels pts l ls) rest)
      -> (Labels pts (Cons (Edge) (MkEdge a b) l) (Cons (Nat) (Succ i) ls))))

(def-fns _ $ (erased labels-split : (erased (List (Point)) pts) (erased (List (Edge)) xs ys zs) (erased (List (Nat)) lz)
    (subterm erased (LApp (Edge) xs ys zs) ap) (erased (Labels pts zs lz) lab) ->
    (erased (List (Nat)) lx ly) (erased (Labels pts xs lx) l1) (erased (Labels pts ys ly) l2) (erased (LApp (Nat) lx ly lz) a))
  (let-match erased ap (LAppCons _ _ xs1 _ zs1 a1) ((LAppNil _ _) (values (Nil _) lz (LbNil pts) lab (LAppNil _ lz))))
  (let-match erased lab (LbCons _ a b i na _ lz1 lab1))
  (let ((erased lx1) (erased ly) (erased l1) (erased l2) (erased a2)) (labels-split pts xs1 ys zs1 lz1 a1 lab1))
  (values (Cons _ (Succ i) lx1) ly (LbCons pts a b i na xs1 lx1 l1) l2 (LAppCons _ (Succ i) lx1 ly lz1 a2)))

(def-fns _ $ (erased labels-join : (erased (List (Point)) pts) (erased (List (Edge)) xs ys zs) (erased (List (Nat)) lx ly)
    (subterm erased (LApp (Edge) xs ys zs) ap) (erased (Labels pts xs lx) l1) (erased (Labels pts ys ly) l2) ->
    (erased (List (Nat)) lz) (erased (Labels pts zs lz) lab) (erased (LApp (Nat) lx ly lz) a))
  (let-match erased ap (LAppCons _ _ xs1 _ zs1 a1) ((LAppNil _ _) (let-match erased l1 (LbNil _)) (values ly l2 (LAppNil _ ly))))
  (let-match erased l1 (LbCons _ a b i na _ lx1 l3))
  (let ((erased lz1) (erased lab1) (erased a2)) (labels-join pts xs1 ys zs1 lx1 ly a1 l3 l2))
  (values (Cons _ (Succ i) lz1) (LbCons pts a b i na zs1 lz1 lab1) (LAppCons _ (Succ i) lx1 ly lz1 a2)))

(def-fns _ $ (erased labels-mem : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (List (Edge)) l) (erased (List (Nat)) ls)
    (erased (Point) a b) (erased (Nat) i) (subterm erased (Labels pts l ls) lab) (erased (Mem (Edge) l (MkEdge a b)) m) (erased (Nth (Point) pts i a) na) ->
    (erased (In (Succ i) ls) r))
  (let-match erased lab (LbCons _ a1 b1 u1 na1 l1 ls1 lab1) (absurd (LbNil _) m))
  (let-match erased m (MemThere _ _ _ _ m1)
    ((MemHere _ _ _) (let-match erased (nth-inj pts i u1 a sp na na1) (Refl _ _)) (InHere (Succ i) ls1)))
  (InThere (Succ i) (Succ u1) ls1 (labels-mem pts sp l1 ls1 a b i lab1 m1 na)))

(def-fns _ $ (erased labels-act : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Edge)) l)
    (subterm erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) l) acts) -> (erased (List (Nat)) ls) (erased (Labels pts l ls) lab))
  (let-match erased acts (ARCons _ _ _ _ x l1 ax acts1) ((ARNil _ _ _ _) (values (Nil _) (LbNil pts))))
  (let-match erased ax (MkAct _ _ _ a b i _ _ _ na _ _ _))
  (let ((erased ls1) (erased lab1)) (labels-act es pts k l1 acts1))
  (values (Cons _ (Succ i) ls1) (LbCons pts a b i na l1 ls1 lab1)))

(def-fns _ $ (erased labels-fan : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Point) p) (erased (Nat) k)
    (erased (Nth (Point) pts k p) np) (erased (List (Edge)) n) (erased (List (Nat)) ln) (erased (AllR (Point) (Edge) Starts p n) st)
    (subterm erased (Labels pts n ln) lab) -> (erased (Nat) c) (erased (Repeat (Nat) c (Succ k) ln) rp))
  (let-match erased lab (LbCons _ a b i na n1 ln1 lab1) ((LbNil _) (values (Zero) (RepeatNil _ (Succ k)))))
  (let-match erased st (ARCons _ _ _ _ _ _ s st1))
  (let-match erased s (MkStarts _ _ _))
  (let-match erased (nth-inj pts i k p sp na np) (Refl _ _))
  (let ((erased c) (erased rp)) (labels-fan pts sp p k np n1 ln1 st1 lab1))
  (values (Succ c) (RepeatCons _ c (Succ k) ln1 rp)))

(def-fns _ $ (erased absurd sb-irrefl : (erased (Point) a b) (erased (SB (MkEdge a b) (MkEdge a b)) s) -> (erased (False) f))
  (let-match erased s (MkSB _ _ _ _ bl _))
  (match erased bl _
    (absurd (BelowL _ _ _ _ lt _) (lex-irrefl a lt))
    (absurd (BelowR _ _ _ _ lt _) (lex-irrefl a lt))
    (absurd (BelowS _ _ _ h) (collinear-left a b b (coll-rot b a b (coll-same b a)) h))))

(def-fns _ $ (erased apart-succ : (erased (Nat) i j) (erased (Apart (Nat) Lt i j) d) -> (erased (Apart (Nat) Lt (Succ i) (Succ j)) r))
  (match erased d _
    ((ApLt _ _ _ _ l) (ApLt _ _ (Succ i) (Succ j) (LtS i j l)))
    ((ApGt _ _ _ _ l) (ApGt _ _ (Succ i) (Succ j) (LtS j i l)))))

(def-fns _ $ (erased notin-lab : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Point) a p) (erased (Nat) i)
    (erased (Nth (Point) pts i a) na) (erased (List (Edge)) r) (erased (List (Nat)) lr) (subterm erased (AllR (Edge) (Edge) SB (MkEdge a p) r) sb)
    (erased (AllR (Point) (Edge) AtP p r) ats) (erased (Labels pts r lr) lab) -> (erased (NotIn (Succ i) lr) ni))
  (let-match erased sb (ARCons _ _ _ _ y r1 sy sb1) ((ARNil _ _ _ _) (let-match erased lab (LbNil _)) (NotInNil (Succ i))))
  (let-match erased ats (ARCons _ _ _ _ _ _ ay ats1))
  (let-match erased ay (MkAtP c _ _))
  (let-match erased lab (LbCons _ _ _ u2 nc _ lr1 lab1))
  (let ((erased rest)) (notin-lab pts sp a p i na r1 lr1 sb1 ats1 lab1))
  (match erased (cmp-eq _ _ _ _ (nat-cmp i u2)) _
    ((Unequal _ _ _ _ d) (NotInCons (Succ i) (Succ u2) lr1 (apart-succ i u2 d) rest))
    (absurd (Equal _ _ _) (let-match erased (nth-fn _ pts i a c na nc) (Refl _ _)) (sb-irrefl a p sy))))

(def-fns _ $ (erased labels-distinct : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Point) p) (erased (List (Edge)) r)
    (erased (List (Nat)) lr) (subterm erased (PW (Edge) SB r) pw) (erased (AllR (Point) (Edge) AtP p r) ats) (erased (Labels pts r lr) lab) ->
    (erased (Distinct lr) d))
  (let-match erased pw (PWCons _ _ x r1 h pw1) ((PWNil _ _) (let-match erased lab (LbNil _)) (DistNil)))
  (let-match erased ats (ARCons _ _ _ _ _ _ ax ats1))
  (let-match erased ax (MkAtP a _ _))
  (let-match erased lab (LbCons _ _ _ i na _ lr1 lab1))
  (DistCons (Succ i) lr1 (notin-lab pts sp a p i na r1 lr1 h ats1 lab1) (labels-distinct pts sp p r1 lr1 pw1 ats1 lab1)))

(def-fns _ $ (erased nrm-fn : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Edge) e) (erased (Point) a b a2 b2)
    (erased (Nat) i j u2 j2) (erased (Nrm pts e a b i j) n1) (erased (Nrm pts e a2 b2 u2 j2) n2) ->
    (erased (Eq (Point) a a2) ea) (erased (Eq (Point) b b2) eb) (erased (Eq (Nat) i u2) ei) (erased (Eq (Nat) j j2) ej))
  (let ((erased na) (erased nb) (erased l)) (nrm-parts pts e a b i j n1))
  (match erased n1 _
    ((NmF _ _ _ _ _ _ _ _)
      (match erased n2 _
        ((NmF _ _ _ _ _ na2 nb2 _)
          (let-match erased (nth-inj pts i u2 a sp na na2) (Refl _ _))
          (let-match erased (nth-inj pts j j2 b sp nb nb2) (Refl _ _))
          (values (Refl _ a) (Refl _ b) (Refl _ i) (Refl _ j)))
        (absurd (NmR _ _ _ _ _ na2 nb2 l2)
          (let-match erased (nth-inj pts i j2 a sp na nb2) (Refl _ _))
          (let-match erased (nth-inj pts j u2 b sp nb na2) (Refl _ _))
          (lt-asym i j l (lt-weaken j i l2)))))
    ((NmR _ _ _ _ _ _ _ _)
      (match erased n2 _
        (absurd (NmF _ _ _ _ _ na2 nb2 l2)
          (let-match erased (nth-inj pts i j2 a sp na nb2) (Refl _ _))
          (let-match erased (nth-inj pts j u2 b sp nb na2) (Refl _ _))
          (lt-asym i j l (lt-weaken j i l2)))
        ((NmR _ _ _ _ _ na2 nb2 _)
          (let-match erased (nth-inj pts i u2 a sp na na2) (Refl _ _))
          (let-match erased (nth-inj pts j j2 b sp nb nb2) (Refl _ _))
          (values (Refl _ a) (Refl _ b) (Refl _ i) (Refl _ j)))))))

; Where the drawn edge e stands against the sweep at point k, with l the active edges.
(def-adts $ (Live : ((LCtx) c) ((Edge) e) -> Type)
  enum
  (many LvBefore : (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Edge)) l) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j)
      (erased (Nrm pts e a b i j) nm) (erased (Lt k (Succ i)) lt) -> (Live (MkLCtx pts k l) e))
  (many LvAfter : (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Edge)) l) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j)
      (erased (Nrm pts e a b i j) nm) (erased (Lt j k) lt) -> (Live (MkLCtx pts k l) e))
  (many LvIn : (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Edge)) l) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j)
      (erased (Nrm pts e a b i j) nm) (erased (Lt i k) lik) (erased (Lt k (Succ j)) lkj) (erased (Mem (Edge) l (MkEdge a b)) m)
      -> (Live (MkLCtx pts k l) e)))

(def-adts $ (DCtx : -> Type)
  enum
  (many MkDCtx : (many (List (Point)) pts) (many (Nat) k) (many (List (Closed)) cs) -> (DCtx)))

; The drawn edge e closed before step k+1, or some step of cs closes it.
(def-adts $ (Done : ((DCtx) c) ((Edge) e) -> Type)
  enum
  (many DnOld : (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Closed)) cs) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j)
      (erased (Nrm pts e a b i j) nm) (erased (Lt j k) lt) -> (Done (MkDCtx pts k cs) e))
  (many DnNew : (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Closed)) cs) (erased (Edge) e) (erased (Point) a b) (erased (Nat) i j)
      (erased (Nrm pts e a b i j) nm) (erased (Closes cs (Succ i) (Succ j)) c) -> (Done (MkDCtx pts k cs) e)))

(def-fns _ $ (erased live-step : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Nat) k) (erased (Point) p)
    (erased (Nth (Point) pts k p) np) (erased (List (Edge)) lst pp r q pr n pn l2)
    (erased (LApp (Edge) pp r pr) a1) (erased (LApp (Edge) pr q lst) a2) (erased (LApp (Edge) pp n pn) b1) (erased (LApp (Edge) pn q l2) b2)
    (erased (AllR (Point) (Edge) AtP p r) ats) (erased (List (Edge)) es2) (subterm erased (AllR (LCtx) (Edge) Live (MkLCtx pts k lst) es2) lv)
    (erased (AllR (LCtx) (Edge) NewC (MkLCtx pts k n) es2) nc) -> (erased (AllR (LCtx) (Edge) Live (MkLCtx pts (Succ k) l2) es2) r2))
  (let-match erased lv (ARCons _ _ _ _ e es3 hl lv1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased nc (ARCons _ _ _ _ _ _ hn nc1))
  (ARCons _ _ _ _ e es3
    (match erased hl _
      ((LvBefore _ _ _ _ a b i j nm lki)
        (let ((erased na) (erased nb) (erased lij)) (nrm-parts pts e a b i j nm))
        (match erased hn _
          ((NcNo _ _ _ _ c2 d2 u2 j2 nm2 d)
            (let ((erased e1) (erased e2) (erased e3) (erased e4)) (nrm-fn pts sp e a b c2 d2 i j u2 j2 nm nm2))
            (let-match erased e1 (Refl _ _))
            (let-match erased e2 (Refl _ _))
            (let-match erased e3 (Refl _ _))
            (let-match erased e4 (Refl _ _))
            (let-match erased d (ApGt _ _ _ _ lt) (absurd (ApLt _ _ _ _ lt) (lt-asym i k lt lki)))
            (LvBefore pts (Succ k) l2 e a b i j nm (LtS k i lt)))
          ((NcYes _ _ _ _ c2 d2 j2 nm2 mb)
            (let ((erased e1) (erased e2) (erased e3) (erased e4)) (nrm-fn pts sp e a b c2 d2 i j k j2 nm nm2))
            (let-match erased e1 (Refl _ _))
            (let-match erased e2 (Refl _ _))
            (let-match erased e3 (Refl _ _))
            (let-match erased e4 (Refl _ _))
            (LvIn pts (Succ k) l2 e a b k j nm (lt-succ k) (LtS k j lij) (mem-left _ _ pn q l2 b2 (mem-right _ _ pp n pn b1 mb))))))
      ((LvAfter _ _ _ _ a b i j nm ljk) (LvAfter pts (Succ k) l2 e a b i j nm (lt-weaken j k ljk)))
      ((LvIn _ _ _ _ a b i j nm lik lkj m)
        (let ((erased na) (erased nb) (erased lij)) (nrm-parts pts e a b i j nm))
        (match erased (nat-cmp k j) _
          ((CEq _ _ _) (LvAfter pts (Succ k) l2 e a b i k nm (lt-succ k)))
          ((CLt _ _ _ _ lt)
            (LvIn pts (Succ k) l2 e a b i j nm (lt-weaken i k lik) (LtS k j lt)
              (match erased (mem-split _ _ pr q lst a2 m) _
                ((OrR _ _ mq) (mem-right _ _ pn q l2 b2 mq))
                ((OrL _ _ mpr)
                  (match erased (mem-split _ _ pp r pr a1 mpr) _
                    ((OrL _ _ mp) (mem-left _ _ pn q l2 b2 (mem-left _ _ pp n pn b1 mp)))
                    (absurd (OrR _ _ mr)
                      (let-match erased (allr-mem _ _ _ p _ r ats mr) (MkAtP _ _ _))
                      (let-match erased (nth-inj pts j k p sp nb np) (Refl _ _))
                      (lt-irrefl k lt)))))))
          (absurd (CGt _ _ _ _ gt) (lt-asym j k gt lkj)))))
    (live-step pts sp k p np lst pp r q pr n pn l2 a1 a2 b1 b2 ats es3 lv1 nc1)))

(def-fns _ $ (erased done-step : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Nat) k) (erased (Point) p)
    (erased (Nth (Point) pts k p) np) (erased (List (Edge)) lst pp r q pr) (erased (LApp (Edge) pp r pr) a1) (erased (LApp (Edge) pr q lst) a2)
    (erased (AllR (Point) (Edge) Abv p pp) abs) (erased (AllR (Point) (Edge) Und p q) uns) (erased (List (Nat)) lr) (erased (Labels pts r lr) labr)
    (erased (List (Closed)) cs) (erased (List (Edge)) es2) (subterm erased (AllR (LCtx) (Edge) Live (MkLCtx pts k lst) es2) lv)
    (erased (AllR (DCtx) (Edge) Done (MkDCtx pts (Succ k) cs) es2) dn) ->
    (erased (AllR (DCtx) (Edge) Done (MkDCtx pts k (Cons (Closed) (MkClosed (Succ k) lr) cs)) es2) r2))
  (let ((erased cs2)) (Cons (Closed) (MkClosed (Succ k) lr) cs))
  (let-match erased lv (ARCons _ _ _ _ e es3 hl lv1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased dn (ARCons _ _ _ _ _ _ hd dn1))
  (ARCons _ _ _ _ e es3
    (match erased hd _
      ((DnNew _ _ _ _ a b i j nm c) (DnNew pts k cs2 e a b i j nm (ClosesThere cs (MkClosed (Succ k) lr) (Succ i) (Succ j) c)))
      ((DnOld _ _ _ _ a b i j nm ljk)
        (let ((erased na) (erased nb) (erased lij)) (nrm-parts pts e a b i j nm))
        (let-match erased (nat-cmp j k) (CEq _ _ _)
          ((CLt _ _ _ _ lt) (DnOld pts k cs2 e a b i j nm lt))
          (absurd (CGt _ _ _ _ gt) (lt-asym k j gt ljk)))
        (let-match erased (nth-fn _ pts j b p nb np) (Refl _ _))
        (match erased hl _
          (absurd (LvBefore _ _ _ _ c2 d2 u2 j2 nm2 lki)
            (let ((erased e1) (erased e2) (erased e3) (erased e4)) (nrm-fn pts sp e a b c2 d2 i j u2 j2 nm nm2))
            (let-match erased e3 (Refl _ _))
            (lt-asym i j lij lki))
          (absurd (LvAfter _ _ _ _ c2 d2 u2 j2 nm2 ljk2)
            (let ((erased e1) (erased e2) (erased e3) (erased e4)) (nrm-fn pts sp e a b c2 d2 i j u2 j2 nm nm2))
            (let-match erased e4 (Refl _ _))
            (lt-irrefl j ljk2))
          ((LvIn _ _ _ _ c2 d2 u2 j2 nm2 _ _ m)
            (let ((erased e1) (erased e2) (erased e3) (erased e4)) (nrm-fn pts sp e a b c2 d2 i j u2 j2 nm nm2))
            (let-match erased e1 (Refl _ _))
            (let-match erased e2 (Refl _ _))
            (let-match erased (mem-split _ _ pr q lst a2 m) (OrL _ _ mpr)
              (absurd (OrR _ _ mq) (let-match erased (allr-mem _ _ _ p _ q uns mq) (MkUnd _ _ _ _ lpp _)) (lex-irrefl p lpp)))
            (let-match erased (mem-split _ _ pp r pr a1 mpr) (OrR _ _ mr)
              (absurd (OrL _ _ mp) (let-match erased (allr-mem _ _ _ p _ pp abs mp) (MkAbv _ _ _ _ lpp _)) (lex-irrefl p lpp)))
            (DnNew pts k cs2 e a p i j nm (ClosesHere cs lr (Succ i) (Succ j) (labels-mem pts sp r lr a p i labr mr na)))))))
    (done-step pts sp k p np lst pp r q pr a1 a2 abs uns lr labr cs es3 lv1 dn1)))

(def-fns _ $ (erased compat-lo : (erased (List (Edge)) es) (erased (Drawing es) dr) (erased (Nat) m m2) (erased (Point) a b c d)
    (erased (EdgeIn es m a b) e1) (erased (EdgeIn es m2 c d) e2) (erased (LexLt a b) lab) (erased (LexLt c d) lcd) (erased (LexLt a c) lac) ->
    (erased (Compatible a b c d) r))
  (let-match erased (cmp-eq _ _ _ _ (nat-cmp m m2)) (Equal _ _ _) ((Unequal _ _ _ _ ne) (compat-in es m m2 a b c d dr e1 e2 ne)))
  (match erased e1 _
    (absurd (EIFwd _ _ _ _ n1)
      (match erased e2 _
        (absurd (EIFwd _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (lex-irrefl a lac))
        (absurd (EIRev _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (lex-cycle a b lab lcd))))
    (absurd (EIRev _ _ _ _ n1)
      (match erased e2 _
        (absurd (EIFwd _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (lex-cycle a b lab lcd))
        (absurd (EIRev _ _ _ _ n2) (let-match erased (nth-fn _ es m _ _ n1 n2) (Refl _ _)) (lex-irrefl a lac))))))

(def-fns _ $ (erased idx-lt : (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Nat) i j) (erased (Point) x y)
    (erased (Nth (Point) pts i x) nx) (erased (Nth (Point) pts j y) ny) (erased (LexLt x y) l) -> (erased (Lt i j) r))
  (match erased (nat-cmp i j) _
    ((CLt _ _ _ _ lt) lt)
    (absurd (CEq _ _ _) (let-match erased (nth-fn _ pts i x y nx ny) (Refl _ _)) (lex-irrefl x l))
    (absurd (CGt _ _ _ _ gt) (lex-cycle x y l (pw-nth _ _ pts j i y x sp ny nx gt)))))

(def-fns _ $ (erased act-up : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Nat) k)
    (erased (Point) p) (erased (Nth (Point) pts k p) np) (erased (Point) a b) (erased (LexLt p b) lpb) (erased (Act (MkCtx es pts k) (MkEdge a b)) ac) ->
    (erased (Act (MkCtx es pts (Succ k)) (MkEdge a b)) r))
  (let-match erased ac (MkAct _ _ _ _ _ i j m ei na nb lik _))
  (MkAct es pts (Succ k) a b i j m ei na nb (lt-weaken i k lik) (LtS k j (idx-lt pts sp k j p b np nb lpb))))

(def-fns _ $ (erased acts-up-abv : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Nat) k)
    (erased (Point) p) (erased (Nth (Point) pts k p) np) (erased (List (Edge)) xs) (subterm erased (AllR (Point) (Edge) Abv p xs) st)
    (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) xs) acts) -> (erased (AllR (Ctx) (Edge) Act (MkCtx es pts (Succ k)) xs) r))
  (let-match erased st (ARCons _ _ _ _ x xs1 sx st1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ax acts1))
  (let-match erased sx (MkAbv a b _ _ lpb _))
  (ARCons _ _ _ _ x xs1 (act-up es pts sp k p np a b lpb ax) (acts-up-abv es pts sp k p np xs1 st1 acts1)))

(def-fns _ $ (erased acts-up-und : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp) (erased (Nat) k)
    (erased (Point) p) (erased (Nth (Point) pts k p) np) (erased (List (Edge)) xs) (subterm erased (AllR (Point) (Edge) Und p xs) st)
    (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) xs) acts) -> (erased (AllR (Ctx) (Edge) Act (MkCtx es pts (Succ k)) xs) r))
  (let-match erased st (ARCons _ _ _ _ x xs1 sx st1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ax acts1))
  (let-match erased sx (MkUnd a b _ _ lpb _))
  (ARCons _ _ _ _ x xs1 (act-up es pts sp k p np a b lpb ax) (acts-up-und es pts sp k p np xs1 st1 acts1)))

(def-fns _ $ (erased allr-pn : (erased (List (Edge)) es) (erased (Drawing es) dr) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p a b)
    (erased (Abv p (MkEdge a b)) sx) (erased (Act (MkCtx es pts k) (MkEdge a b)) ax) (erased (List (Edge)) n)
    (subterm erased (AllR (Point) (Edge) Starts p n) st) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts (Succ k)) n) acts) ->
    (erased (AllR (Edge) (Edge) SB (MkEdge a b) n) r))
  (let-match erased st (ARCons _ _ _ _ y n1 sy st1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ay acts1))
  (let-match erased sx (MkAbv _ _ _ lap lpb h))
  (let-match erased sy (MkStarts _ q lpq))
  (let-match erased ax (MkAct _ _ _ _ _ _ _ m ei _ _ _ _))
  (let-match erased ay (MkAct _ _ _ _ _ _ _ m2 ei2 _ _ _ _))
  (ARCons _ _ _ _ y n1 (MkSB a b p q (BelowL a b p q lap h) (compat-lo es dr m m2 a b p q ei ei2 (lex-trans a p b lap lpb) lpq lap))
    (allr-pn es dr pts k p a b sx ax n1 st1 acts1)))

(def-fns _ $ (erased cross-pn : (erased (List (Edge)) es) (erased (Drawing es) dr) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
    (erased (List (Edge)) xs n) (subterm erased (AllR (Point) (Edge) Abv p xs) sx) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) xs) ax)
    (erased (AllR (Point) (Edge) Starts p n) st) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts (Succ k)) n) acts) -> (erased (Cross (Edge) SB xs n) r))
  (let-match erased sx (ARCons _ _ _ _ x xs1 s1 sx1) ((ARNil _ _ _ _) (CrNil _ _ n)))
  (let-match erased ax (ARCons _ _ _ _ _ _ a1 ax1))
  (let-match erased s1 (MkAbv a b _ _ _ _))
  (CrCons _ _ x xs1 n (allr-pn es dr pts k p a b s1 a1 n st acts) (cross-pn es dr pts k p xs1 n sx1 ax1 st acts)))

(def-fns _ $ (erased allr-nq : (erased (List (Edge)) es) (erased (Drawing es) dr) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p q)
    (erased (LexLt p q) lpq) (erased (Act (MkCtx es pts (Succ k)) (MkEdge p q)) ax) (erased (List (Edge)) ys)
    (subterm erased (AllR (Point) (Edge) Und p ys) su) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) ys) acts) ->
    (erased (AllR (Edge) (Edge) SB (MkEdge p q) ys) r))
  (let-match erased su (ARCons _ _ _ _ y ys1 sy su1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ay acts1))
  (let-match erased sy (MkUnd c d _ lcp lpd h))
  (let-match erased ax (MkAct _ _ _ _ _ _ _ m ei _ _ _ _))
  (let-match erased ay (MkAct _ _ _ _ _ _ _ m2 ei2 _ _ _ _))
  (ARCons _ _ _ _ y ys1
    (MkSB p q c d (BelowR p q c d lcp h) (compat-sym c d p q (compat-lo es dr m2 m c d p q ei2 ei (lex-trans c p d lcp lpd) lpq lcp)))
    (allr-nq es dr pts k p q lpq ax ys1 su1 acts1)))

(def-fns _ $ (erased cross-nq : (erased (List (Edge)) es) (erased (Drawing es) dr) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p)
    (erased (List (Edge)) n ys) (subterm erased (AllR (Point) (Edge) Starts p n) st) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts (Succ k)) n) acts)
    (erased (AllR (Point) (Edge) Und p ys) su) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) ys) ay) -> (erased (Cross (Edge) SB n ys) r))
  (let-match erased st (ARCons _ _ _ _ x n1 s1 st1) ((ARNil _ _ _ _) (CrNil _ _ ys)))
  (let-match erased acts (ARCons _ _ _ _ _ _ a1 acts1))
  (let-match erased s1 (MkStarts _ q lpq))
  (CrCons _ _ x n1 ys (allr-nq es dr pts k p q lpq a1 ys su ay) (cross-nq es dr pts k p n1 ys st1 acts1 su ay)))

(def-fns _ $ (erased lapp-make : (erased Type A) (subterm erased (List A) xs) (erased (List A) ys) -> (erased (List A) zs) (erased (LApp A xs ys zs) a))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values ys (LAppNil A ys))))
  (let ((erased zs1) (erased a1)) (lapp-make A xs1 ys))
  (values (Cons A x zs1) (LAppCons A x xs1 ys zs1 a1)))

(def-fns _ $ (erased done-end : (erased (List (Point)) pts) (erased (Nat) k) (erased (Length (Point) pts k) ln) (erased (List (Edge)) l es2)
    (subterm erased (AllR (LCtx) (Edge) Live (MkLCtx pts k l) es2) lv) -> (erased (AllR (DCtx) (Edge) Done (MkDCtx pts k (Nil (Closed))) es2) r))
  (let-match erased lv (ARCons _ _ _ _ e es3 hl lv1) ((ARNil _ _ _ _) (ARNil _ _ _ _)))
  (let ((erased dn))
    (match erased hl (((Done (MkDCtx pts k (Nil (Closed))) e) d))
      ((LvBefore _ _ _ _ a b i j nm _)
        (let ((erased na) (erased nb) (erased lij)) (nrm-parts pts e a b i j nm))
        (DnOld pts k (Nil _) e a b i j nm (nth-lt-length _ pts j k b nb ln)))
      ((LvAfter _ _ _ _ a b i j nm _)
        (let ((erased na) (erased nb) (erased lij)) (nrm-parts pts e a b i j nm))
        (DnOld pts k (Nil _) e a b i j nm (nth-lt-length _ pts j k b nb ln)))
      ((LvIn _ _ _ _ a b i j nm _ _ _)
        (let ((erased na) (erased nb) (erased lij)) (nrm-parts pts e a b i j nm))
        (DnOld pts k (Nil _) e a b i j nm (nth-lt-length _ pts j k b nb ln)))))
  (ARCons _ _ _ _ e es3 dn (done-end pts k ln l es3 lv1)))

(def-fns _ $ (erased done-cov : (erased (List (Point)) pts) (erased (List (Closed)) cs) (erased (List (Edge)) es2)
    (subterm erased (AllR (DCtx) (Edge) Done (MkDCtx pts (Zero) cs) es2) dn) -> (erased (Covered pts cs es2) r))
  (let-match erased dn (ARCons _ _ _ _ e es3 hd dn1) ((ARNil _ _ _ _) (CovNil pts cs)))
  (let-match erased hd (DnNew _ _ _ _ a b i j nm c) (absurd (DnOld _ _ _ _ _ _ _ _ _ lt) lt))
  (let ((erased rest)) (done-cov pts cs es3 dn1))
  (match erased nm _
    ((NmF _ _ _ _ _ na nb _) (CovCons pts cs es3 a b i j na nb (OrL _ _ c) rest))
    ((NmR _ _ _ _ _ na nb _) (CovCons pts cs es3 b a j i nb na (OrR _ _ c) rest))))

(def-adts $ (Vert : ((List (Edge)) es) ((Point) p) -> Type)
  enum
  (many MkVert : (erased (List (Edge)) es) (erased (Point) p) (erased (Nat) m) (erased (Point) q) (erased (EdgeIn es m p q) ei) -> (Vert es p)))

(def-fns _ $ (erased add-shift : (erased (Nat) a b c) (erased (Add a (Succ b) c) p) -> (erased (Add (Succ a) b c) q))
  (let ((erased c1) (erased e) (erased q1)) (add-succ-right-inv a b c p))
  (let-match erased e (Refl _ _))
  (AddSucc a b c1 q1))

; The sweep from point k on, with l the edges active there, bottom to top, and ls their labels.
(def-fns _ $ (erased sweep : (erased (List (Edge)) es) (erased (Drawing es) dr) (erased (List (Point)) pts) (erased (PW (Point) LexLt pts) sp)
    (erased (AllR (List (Edge)) (Point) Vert es pts) vs) (erased (AllR (List (Point)) (Edge) Pre pts es) prs)
    (erased (Nat) n) (erased (Length (Point) pts n) len) (erased (Nat) k) (subterm erased (Nat) f) (erased (Add k f n) akf)
    (erased (List (Edge)) l) (erased (List (Nat)) ls) (erased (Labels pts l ls) lab) (erased (PW (Edge) SB l) pw)
    (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k) l) acts) (erased (AllR (LCtx) (Edge) Live (MkLCtx pts k l) es) lv) ->
    (erased (List (Closed)) cs) (erased (Trace (Succ k) ls cs) tr) (erased (AllR (DCtx) (Edge) Done (MkDCtx pts k cs) es) dn))
  (let-match erased f (Succ f1)
    ((Zero)
      (let-match erased (add-fn k (Zero) n k akf (add-zero-right k)) (Refl _ _))
      (let-match erased acts (ARNil _ _ _ _)
        (absurd (ARCons _ _ _ _ _ _ ax _)
          (let-match erased ax (MkAct _ _ _ _ b _ j _ _ _ nb _ lkj))
          (lt-asym j k (nth-lt-length _ pts j k b nb len) lkj)))
      (let-match erased lab (LbNil _))
      (values (Nil _) (TrDone (Succ k)) (done-end pts k len (Nil _) es lv))))
  (let ((erased p) (erased np)) (nth-exists _ pts n k len (add-pos-lt k (Succ f1) n akf (LtZ f1))))
  (let-match erased (allr-mem _ _ _ es p pts vs (nth-mem _ pts k p np)) (MkVert _ _ mp qv ep))
  (let ((erased hr)) (MkHere es pts k p dr sp np mp qv ep))
  (let ((erased pp) (erased r) (erased q) (erased pr) (erased a1) (erased a2) (erased abs) (erased ats) (erased uns))
    (split-a es pts k p l hr pw acts))
  (let ((erased nw) (erased pwn) (erased actsn) (erased stn) (erased _) (erased ncn))
    (scan-new es pts k p hr (Nil _) es (Zero) (LAppNil _ es) (LengthNil _) prs))
  (let ((erased pn) (erased b1)) (lapp-make _ pp nw))
  (let ((erased l2) (erased b2)) (lapp-make _ pn q))
  (let ((erased pwpr) (erased pwq) (erased crprq)) (pw-split _ _ pr q l a2 pw))
  (let ((erased pwp) (erased pwr) (erased _)) (pw-split _ _ pp r pr a1 pwpr))
  (let ((erased crpq) (erased _)) (cross-split _ _ pp r q pr crprq a1))
  (let ((erased actspr) (erased actsq)) (allr-split _ _ _ _ pr q l a2 acts))
  (let ((erased actsp) (erased _)) (allr-split _ _ _ _ pp r pr a1 actspr))
  (let ((erased pwpn)) (pw-join _ _ pp nw pn b1 pwp pwn (cross-pn es dr pts k p pp nw abs actsp stn actsn)))
  (let ((erased pw2)) (pw-join _ _ pn q l2 b2 pwpn pwq (cross-join _ _ pp nw q pn b1 crpq (cross-nq es dr pts k p nw q stn actsn uns actsq))))
  (let ((erased acts2))
    (allr-join _ _ _ _ pn q l2 b2 (allr-join _ _ _ _ pp nw pn b1 (acts-up-abv es pts sp k p np pp abs actsp) actsn)
      (acts-up-und es pts sp k p np q uns actsq)))
  (let ((erased lpr) (erased lq) (erased labpr) (erased labq) (erased al2)) (labels-split pts pr q l ls a2 lab))
  (let ((erased lp) (erased lr) (erased labp) (erased labr) (erased al1)) (labels-split pts pp r pr lpr a1 labpr))
  (let ((erased ln) (erased labn)) (labels-act es pts (Succ k) nw actsn))
  (let ((erased c) (erased rp)) (labels-fan pts sp p k np nw ln stn labn))
  (let ((erased lpn) (erased labpn) (erased al3)) (labels-join pts pp nw pn lp ln b1 labp labn))
  (let ((erased ls2) (erased lab2) (erased al4)) (labels-join pts pn q l2 lpn lq b2 labpn labq))
  (let ((erased lv2)) (live-step pts sp k p np l pp r q pr nw pn l2 a1 a2 b1 b2 ats es lv ncn))
  (let ((erased cs1) (erased tr1) (erased dn1))
    (sweep es dr pts sp vs prs n len (Succ k) f1 (add-shift k f1 n akf) l2 ls2 lab2 pw2 acts2 lv2))
  (values (Cons _ (MkClosed (Succ k) lr) cs1)
    (TrStep (Succ k) c ls lp lr lq lpr ln lpn ls2 cs1 al1 al2 (labels-distinct pts sp p r lr pwr ats labr) rp al3 al4 tr1)
    (done-step pts sp k p np l pp r q pr a1 a2 abs uns lr labr cs1 es lv dn1)))
