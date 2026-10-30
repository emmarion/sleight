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
  (many MkCtx : (many (List (Edge)) es) (many (List (Point)) pts) (many (Nat) k) (many (List (Edge)) l) -> (Ctx)))

; The edge ab, with a before b, is crossed by the sweep between points k-1 and k.
(def-adts $ (Act : ((Ctx) c) ((Edge) e) -> Type)
  enum
  (many MkAct : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (List (Edge)) l) (erased (Point) a b)
      (erased (Nat) i j m) (erased (EdgeIn es m a b) ei) (erased (Nth (Point) pts i a) na) (erased (Nth (Point) pts j b) nb)
      (erased (Lt i k) lik) (erased (Lt k (Succ j)) lkj) -> (Act (MkCtx es pts k l) (MkEdge a b))))

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

(def-fns _ $ (erased stat-of : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p) (erased (List (Edge)) l)
    (erased (Edge) e) (erased (Here es pts k p) hr) (erased (Act (MkCtx es pts k l) e) ac) -> (erased (Side p e) s))
  (let-match erased hr (MkHere _ _ _ _ dr sp np mp q ep))
  (let-match erased ac (MkAct _ _ _ _ a b i j m ei na nb lik lkj))
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

(def-fns _ $ (erased under-tail : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p) (erased (List (Edge)) l)
    (erased (Edge) x) (erased (List (Edge)) ys) (erased (Here es pts k p) hr) (erased (Und p x) ux)
    (subterm erased (AllR (Edge) (Edge) SB x ys) sb) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k l) ys) acts) ->
    (erased (AllR (Point) (Edge) Und p ys) r))
  (let-match erased sb (ARCons _ _ _ _ y ys1 sxy sb1) ((ARNil _ _ _ _) (ARNil _ _ _ p)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ay acts1))
  (let-match erased ux (MkUnd a b _ lap lpb hu))
  (let-match erased sxy (MkSB _ _ c d bl cp))
  (let ((erased lab)) (lex-trans a p b lap lpb))
  (ARCons _ _ _ p y ys1
    (match erased (stat-of es pts k p l y hr ay) _
      (absurd (StA _ _ s) (let-match erased s (MkAbv _ _ _ lcp lpd ho))
        (sweep-under-over a b c d p bl cp lab (lex-trans c p d lcp lpd) lap lpb lcp lpd hu ho))
      (absurd (StT _ _ s) (let-match erased s (MkAtP _ _ lcp)) (sweep-end-under a b c p bl cp lcp lap lpb hu))
      ((StU _ _ s) s))
    (under-tail es pts k p l x ys1 hr ux sb1 acts1)))

(def-fns _ $ (erased at-tail : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p) (erased (List (Edge)) l)
    (erased (Edge) x) (erased (List (Edge)) ys) (erased (Here es pts k p) hr) (erased (AtP p x) tx)
    (subterm erased (AllR (Edge) (Edge) SB x ys) sb) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k l) ys) acts) ->
    (erased (AllR (Point) (Edge) TU p ys) r))
  (let-match erased sb (ARCons _ _ _ _ y ys1 sxy sb1) ((ARNil _ _ _ _) (ARNil _ _ _ p)))
  (let-match erased acts (ARCons _ _ _ _ _ _ ay acts1))
  (let-match erased tx (MkAtP a _ lap))
  (let-match erased sxy (MkSB _ _ c d bl cp))
  (ARCons _ _ _ p y ys1
    (match erased (stat-of es pts k p l y hr ay) _
      (absurd (StA _ _ s) (let-match erased s (MkAbv _ _ _ lcp lpd ho)) (sweep-end-over a p c d bl cp lap lcp lpd ho))
      ((StT _ _ s) (TUT p y s))
      ((StU _ _ s) (TUU p y s)))
    (at-tail es pts k p l x ys1 hr tx sb1 acts1)))

(def-fns _ $ (erased split-t : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p) (erased (List (Edge)) l)
    (erased (List (Edge)) xs) (erased (Here es pts k p) hr) (subterm erased (AllR (Point) (Edge) TU p xs) tus)
    (erased (PW (Edge) SB xs) pw) (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k l) xs) acts) ->
    (erased (List (Edge)) r q) (erased (LApp (Edge) r q xs) a) (erased (AllR (Point) (Edge) AtP p r) ats) (erased (AllR (Point) (Edge) Und p q) uns))
  (let-match erased tus (ARCons _ _ _ _ x xs1 tx tus1)
    ((ARNil _ _ _ _) (values (Nil _) (Nil _) (LAppNil _ (Nil _)) (ARNil _ _ _ p) (ARNil _ _ _ p))))
  (let-match erased pw (PWCons _ _ _ _ h pw1))
  (let-match erased acts (ARCons _ _ _ _ _ _ ax acts1))
  (let-match erased tx (TUT _ _ s)
    ((TUU _ _ s) (values (Nil _) xs (LAppNil _ xs) (ARNil _ _ _ p) (ARCons _ _ _ p x xs1 s (under-tail es pts k p l x xs1 hr s h acts1)))))
  (let ((erased r1) (erased q) (erased a) (erased ats) (erased uns)) (split-t es pts k p l xs1 hr tus1 pw1 acts1))
  (values (Cons _ x r1) q (LAppCons _ x r1 q xs1 a) (ARCons _ _ _ p x r1 s ats) uns))

; The active edges, bottom to top, are those p is above, then those ending at p, then those p is below.
(def-fns _ $ (erased split-a : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (Nat) k) (erased (Point) p) (erased (List (Edge)) l)
    (erased (List (Edge)) xs) (erased (Here es pts k p) hr) (subterm erased (PW (Edge) SB xs) pw)
    (erased (AllR (Ctx) (Edge) Act (MkCtx es pts k l) xs) acts) ->
    (erased (List (Edge)) pp r q pr) (erased (LApp (Edge) pp r pr) a1) (erased (LApp (Edge) pr q xs) a2)
    (erased (AllR (Point) (Edge) Abv p pp) abs) (erased (AllR (Point) (Edge) AtP p r) ats) (erased (AllR (Point) (Edge) Und p q) uns))
  (let-match erased pw (PWCons _ _ x xs1 h pw1)
    ((PWNil _ _) (values (Nil _) (Nil _) (Nil _) (Nil _) (LAppNil _ (Nil _)) (LAppNil _ (Nil _)) (ARNil _ _ _ p) (ARNil _ _ _ p) (ARNil _ _ _ p))))
  (let-match erased acts (ARCons _ _ _ _ _ _ ax acts1))
  (match erased (stat-of es pts k p l x hr ax) _
    ((StA _ _ s)
      (let ((erased p1) (erased r) (erased q) (erased pr1) (erased a1) (erased a2) (erased abs) (erased ats) (erased uns))
        (split-a es pts k p l xs1 hr pw1 acts1))
      (values (Cons _ x p1) r q (Cons _ x pr1) (LAppCons _ x p1 r pr1 a1) (LAppCons _ x pr1 q xs1 a2) (ARCons _ _ _ p x p1 s abs) ats uns))
    ((StT _ _ s)
      (let ((erased r1) (erased q) (erased a) (erased ats) (erased uns))
        (split-t es pts k p l xs1 hr (at-tail es pts k p l x xs1 hr s h acts1) pw1 acts1))
      (values (Nil _) (Cons _ x r1) q (Cons _ x r1) (LAppNil _ (Cons _ x r1)) (LAppCons _ x r1 q xs1 a) (ARNil _ _ _ p)
        (ARCons _ _ _ p x r1 s ats) uns))
    ((StU _ _ s)
      (values (Nil _) (Nil _) xs (Nil _) (LAppNil _ (Nil _)) (LAppNil _ xs) (ARNil _ _ _ p) (ARNil _ _ _ p)
        (ARCons _ _ _ p x xs1 s (under-tail es pts k p l x xs1 hr s h acts1))))))
