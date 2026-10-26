(def-adts $ (PT : -> Type)
  enum
  (many Undef : -> (PT))
  (many Def : (many (Tr) t) -> (PT)))

(def-adts
  ((PLook : ((List (PT)) p) ((Nat) q) ((Bool) b) ((PT) x) -> Type)
    enum
    (many PL0 : (erased (PT) x0 x1) (erased (List (PT)) rest) -> (PLook (Cons (PT) x0 (Cons (PT) x1 rest)) (Zero) (BFalse) x0))
    (many PL1 : (erased (PT) x0 x1) (erased (List (PT)) rest) -> (PLook (Cons (PT) x0 (Cons (PT) x1 rest)) (Zero) (BTrue) x1))
    (many PLS : (erased (PT) x0 x1) (erased (List (PT)) rest) (erased (Nat) q) (erased (Bool) b) (erased (PT) x)
       (erased (PLook rest q b x) p) -> (PLook (Cons (PT) x0 (Cons (PT) x1 rest)) (Succ q) b x))))

(def-adts
  ((Ext : ((List (PT)) p) ((List (Tr)) m) -> Type)
    enum
    (many ExNil : -> (Ext (Nil (PT)) (Nil (Tr))))
    (many ExU : (erased (Tr) t) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) e) -> (Ext (Cons (PT) (Undef) p) (Cons (Tr) t m)))
    (many ExD : (erased (Tr) t) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) e) -> (Ext (Cons (PT) (Def t) p) (Cons (Tr) t m)))))

(def-fns _ $ (erased ext-look : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t)
    (erased (Ext p m) e) (subterm erased (PLook p q b (Def t)) pl) -> (erased (Look m q b t) lk))
  (match erased pl _
    ((PL0 _ x1 rest)
      (let-match erased e (ExD _ _ m1 e1))
      (let-match erased e1 (ExU t1 _ rest2 _) ((ExD t1 _ rest2 _) (Look0 t t1 rest2)))
      (Look0 t t1 rest2))
    ((PL1 x0 _ rest)
      (let-match erased e (ExU t0 _ m1 e1) ((ExD t0 _ m1 e1) (let-match erased e1 (ExD _ _ rest2 _)) (Look1 t0 t rest2)))
      (let-match erased e1 (ExD _ _ rest2 _))
      (Look1 t0 t rest2))
    ((PLS x0 x1 rest q1 _ _ pl1)
      (let-match erased e (ExU t0 _ m1 e1) ((ExD t0 _ m1 e1)
        (let-match erased e1 (ExU t1 _ m2 e2) ((ExD t1 _ m2 e2) (LookS t0 t1 m2 q1 b t (ext-look rest m2 q1 b t e2 pl1))))
        (LookS t0 t1 m2 q1 b t (ext-look rest m2 q1 b t e2 pl1))))
      (let-match erased e1 (ExU t1 _ m2 e2) ((ExD t1 _ m2 e2) (LookS t0 t1 m2 q1 b t (ext-look rest m2 q1 b t e2 pl1))))
      (LookS t0 t1 m2 q1 b t (ext-look rest m2 q1 b t e2 pl1)))))

(def-fns _ $ (erased nth-fn : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A x y)
    (subterm erased (Nth A xs i x) p) (erased (Nth A xs i y) p2) -> (erased (Eq A x y) e))
  (match erased p _
    ((NthHere _ _ _) (let-match erased p2 (NthHere _ _ _)) (Refl A x))
    ((NthThere _ _ rest i1 _ p1) (let-match erased p2 (NthThere _ _ _ _ _ p21)) (nth-fn A rest i1 x y p1 p21))))

(def-adts $ (Edge : -> Type)
  enum
  (many MkE : (many (Nat) s) (many (Nat) c) (many (Nat) s2) -> (Edge)))

(def-adts $ (ACN : -> Type)
  enum
  (many MkACN : (many (Nat) q) (many (Nat) sl) (many (Nat) sh) (many (Nat) sr) -> (ACN)))

(def-adts
  ((GSN : ((List (Bool)) sy) ((List (Edge)) es) ((List (Nat)) acc) ((Nat) s) ((List (Bool)) xs) -> Type)
    enum
    (many GAcc : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) s)
       (erased (Mem (Nat) s acc) ma) -> (GSN sy es acc s (Nil (Bool))))
    (many GEd : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) s c s2) (erased (Bool) b)
       (erased (List (Bool)) xs) (erased (Mem (Edge) (MkE s c s2) es) me) (erased (Nth (Bool) sy c b) nb) (erased (GSN sy es acc s2 xs) g)
       -> (GSN sy es acc s (Cons (Bool) b xs)))))

(def-adts
  ((AccAll : ((List (Bool)) sy) ((List (Edge)) es) ((List (Nat)) acc) ((List (Nat)) as) -> Type)
    enum
    (many AANil : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) -> (AccAll sy es acc (Nil (Nat))))
    (many AACons : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc as) (erased (Nat) a c a2)
       (erased (Mem (Edge) (MkE a c a2) es) me) (erased (Nth (Bool) sy c (BFalse)) nb) (erased (Mem (Nat) a2 acc) ma)
       (erased (AccAll sy es acc as) rest) -> (AccAll sy es acc (Cons (Nat) a as)))))

(def-fns _ $ (erased acc-get : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc as) (erased (Nat) a)
    (erased (AccAll sy es acc as) aa) (subterm erased (Mem (Nat) a as) ma) ->
    (erased (Nat) c a2) (erased (Mem (Edge) (MkE a c a2) es) me) (erased (Nth (Bool) sy c (BFalse)) nb) (erased (Mem (Nat) a2 acc) ma2))
  (match erased ma _
    ((MemHere _ _ _) (let-match erased aa (AACons _ _ _ _ _ c a2 me nb ma2 _)) (values c a2 me nb ma2))
    ((MemThere _ _ _ rest ma1) (let-match erased aa (AACons _ _ _ _ _ _ _ _ _ _ aa1)) (acc-get sy es acc rest a aa1 ma1))))

(def-fns _ $ (erased gsn-pop : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) s)
    (erased (List (Bool)) xs ys) (erased (Bool) b) (erased (AccAll sy es acc acc) aa) (erased (GSN sy es acc s xs) g) (erased (Pop xs b ys) pp) ->
    (erased (Nat) c s2) (erased (Mem (Edge) (MkE s c s2) es) me) (erased (Nth (Bool) sy c b) nb) (erased (GSN sy es acc s2 ys) g2))
  (match erased g _
    ((GAcc _ _ _ _ ma)
      (let-match erased pp (PopNil))
      (let ((erased c) (erased a2) (erased me) (erased nb) (erased ma2)) (acc-get sy es acc acc s aa ma))
      (values c a2 me nb (GAcc sy es acc a2 ma2)))
    ((GEd _ _ _ _ c s2 _ _ me nb g1) (let-match erased pp (PopCons _ _)) (values c s2 me nb g1))))

(def-adts
  ((GCN : ((List (Bool)) sy) ((List (Edge)) es) ((List (Nat)) acc) ((ACN) a) ((Cfg) cf) -> Type)
    enum
    (many MkGCN : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) q sl sh sr)
       (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (GSN sy es acc sl l) gl) (erased (GSN sy es acc sr r) gr) (erased (Nth (Bool) sy sh h) nh)
       -> (GCN sy es acc (MkACN q sl sh sr) (MkCfg q l h r)))))

(def-adts
  ((PlaceN : ((Dir) d) ((Nat) q) ((Nat) p) ((Nat) c) ((Nat) o) ((ACN) a) -> Type)
    enum
    (many PNL : (erased (Nat) q p c o) -> (PlaceN (DL) q p c o (MkACN q p c o)))
    (many PNR : (erased (Nat) q p c o) -> (PlaceN (DR) q p c o (MkACN q o c p)))))

(def-adts
  ((AllFrom : ((List (ACN)) S) ((Dir) d) ((Nat) q) ((Nat) o) ((List (Edge)) es) ((Nat) s) -> Type)
    enum
    (many AFNil : (erased (List (ACN)) S) (erased (Dir) d) (erased (Nat) q o s) -> (AllFrom S d q o (Nil (Edge)) s))
    (many AFHit : (erased (List (ACN)) S) (erased (Dir) d) (erased (Nat) q o s c s2) (erased (List (Edge)) rest) (erased (ACN) a)
       (erased (PlaceN d q s2 c o a) pl) (erased (Mem (ACN) a S) ma) (erased (AllFrom S d q o rest s) af)
       -> (AllFrom S d q o (Cons (Edge) (MkE s c s2) rest) s))
    (many AFSkip : (erased (List (ACN)) S) (erased (Dir) d) (erased (Nat) q o s s1 c s2) (erased (List (Edge)) rest)
       (erased (Apart (Nat) Lt s1 s) ap) (erased (AllFrom S d q o rest s) af)
       -> (AllFrom S d q o (Cons (Edge) (MkE s1 c s2) rest) s))))

(def-fns _ $ (erased allfrom-get : (erased (List (ACN)) S) (erased (Dir) d) (erased (Nat) q o s c s2) (erased (List (Edge)) es)
    (erased (AllFrom S d q o es s) af) (subterm erased (Mem (Edge) (MkE s c s2) es) me) ->
    (erased (ACN) a) (erased (PlaceN d q s2 c o a) pl) (erased (Mem (ACN) a S) ma))
  (match erased me _
    ((MemHere _ _ rest)
      (match erased af _
        ((AFHit _ _ _ _ _ _ _ _ a pl ma _) (values a pl ma))
        (absurd (AFSkip _ _ _ _ _ _ _ _ _ ap _) (apart-irrefl s ap))))
    ((MemThere _ _ _ rest me1)
      (match erased af _
        ((AFHit _ _ _ _ _ _ _ _ _ _ _ af1) (allfrom-get S d q o s c s2 rest af1 me1))
        ((AFSkip _ _ _ _ _ _ _ _ _ _ af1) (allfrom-get S d q o s c s2 rest af1 me1))))))

(def-adts
  ((AOKN : ((List (PT)) p) ((List (Bool)) sy) ((List (Edge)) es) ((List (ACN)) S) ((ACN) a) -> Type)
    enum
    (many AKL : (erased (List (PT)) p) (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (ACN)) S)
       (erased (Nat) q sl sh sr q2 cn o2) (erased (Bool) h w)
       (erased (PLook p q h (Def (Go w (DL) q2))) pl) (erased (Nth (Bool) sy sh h) nh) (erased (Nth (Bool) sy cn w) nw)
       (erased (Mem (Edge) (MkE o2 cn sr) es) me) (erased (AllFrom S (DL) q2 o2 es sl) af)
       -> (AOKN p sy es S (MkACN q sl sh sr)))
    (many AKR : (erased (List (PT)) p) (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (ACN)) S)
       (erased (Nat) q sl sh sr q2 cn o2) (erased (Bool) h w)
       (erased (PLook p q h (Def (Go w (DR) q2))) pl) (erased (Nth (Bool) sy sh h) nh) (erased (Nth (Bool) sy cn w) nw)
       (erased (Mem (Edge) (MkE o2 cn sl) es) me) (erased (AllFrom S (DR) q2 o2 es sr) af)
       -> (AOKN p sy es S (MkACN q sl sh sr)))))

(def-adts
  ((ClosedN : ((List (PT)) p) ((List (Bool)) sy) ((List (Edge)) es) ((List (ACN)) S) ((List (ACN)) T) -> Type)
    enum
    (many CNNil : (erased (List (PT)) p) (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (ACN)) S)
       -> (ClosedN p sy es S (Nil (ACN))))
    (many CNCons : (erased (List (PT)) p) (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (ACN)) S T) (erased (ACN) a)
       (erased (AOKN p sy es S a) ok) (erased (ClosedN p sy es S T) rest) -> (ClosedN p sy es S (Cons (ACN) a T)))))

(def-fns _ $ (erased closedn-get : (erased (List (PT)) p) (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (ACN)) S T) (erased (ACN) a)
    (erased (ClosedN p sy es S T) cl) (subterm erased (Mem (ACN) a T) ma) -> (erased (AOKN p sy es S a) ok))
  (match erased ma _
    ((MemHere _ _ _) (let-match erased cl (CNCons _ _ _ _ _ _ ok _)) ok)
    ((MemThere _ _ _ rest ma1) (let-match erased cl (CNCons _ _ _ _ _ _ _ cl1)) (closedn-get p sy es S rest a cl1 ma1))))

(def-fns _ $ (erased never-n : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex)
    (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (List (ACN)) S)
    (erased (ClosedN p sy es S S) cl) (erased (AccAll sy es acc acc) aa)
    (erased (ACN) a) (erased (Mem (ACN) a S) ma) (erased (Cfg) c) (erased (GCN sy es acc a c) g)
    (erased (Nat) s) (subterm erased (HaltsIn m c s) hs) -> (erased (False) f))
  (let-match erased g (MkGCN _ _ _ q sl sh sr l r h gl gr nh))
  (let ((erased ok)) (closedn-get p sy es S S a cl ma))
  (match erased hs _
    ((HStop _ _ _ _ _ lk)
      (match erased ok _
        (absurd (AKL _ _ _ _ _ _ _ _ _ _ _ h2 _ pl nh2 _ _ _)
          (let-match erased (nth-fn _ sy sh h h2 nh nh2) (Refl _ _))
          (look-fn m q h _ _ lk (ext-look p m q h _ ex pl)))
        (absurd (AKR _ _ _ _ _ _ _ _ _ _ _ h2 _ pl nh2 _ _ _)
          (let-match erased (nth-fn _ sy sh h h2 nh nh2) (Refl _ _))
          (look-fn m q h _ _ lk (ext-look p m q h _ ex pl)))))
    ((HMove _ _ d s1 st hs1)
      (match erased ok _
        ((AKL _ _ _ _ _ _ _ _ q2 cn o2 h2 w pl nh2 nw me af)
          (let-match erased (nth-fn _ sy sh h h2 nh nh2) (Refl _ _))
          (let ((erased lk2)) (ext-look p m q h _ ex pl))
          (match erased st _
            ((StepL _ _ _ _ _ l2 _ _ hh lk pp)
              (let-match erased (look-fn m q h _ _ lk lk2) (Refl _ _))
              (let ((erased c1) (erased s2) (erased me1) (erased nb1) (erased gl2)) (gsn-pop sy es acc sl l l2 hh aa gl pp))
              (let ((erased a2) (erased pl2) (erased ma2)) (allfrom-get S (DL) q2 o2 sl c1 s2 es af me1))
              (let-match erased pl2 (PNL _ _ _ _))
              (never-n p m ex sy es acc S cl aa a2 ma2 d
                (MkGCN sy es acc q2 s2 c1 o2 l2 (Cons (Bool) w r) hh gl2 (GEd sy es acc o2 cn sr w r me nw gr) nb1) s1 hs1))
            (absurd (StepR _ _ _ _ _ _ _ _ _ lk _) (look-fn m q h _ _ lk lk2))))
        ((AKR _ _ _ _ _ _ _ _ q2 cn o2 h2 w pl nh2 nw me af)
          (let-match erased (nth-fn _ sy sh h h2 nh nh2) (Refl _ _))
          (let ((erased lk2)) (ext-look p m q h _ ex pl))
          (match erased st _
            (absurd (StepL _ _ _ _ _ _ _ _ _ lk _) (look-fn m q h _ _ lk lk2))
            ((StepR _ _ _ _ _ r2 _ _ hh lk pp)
              (let-match erased (look-fn m q h _ _ lk lk2) (Refl _ _))
              (let ((erased c1) (erased s2) (erased me1) (erased nb1) (erased gr2)) (gsn-pop sy es acc sr r r2 hh aa gr pp))
              (let ((erased a2) (erased pl2) (erased ma2)) (allfrom-get S (DR) q2 o2 sr c1 s2 es af me1))
              (let-match erased pl2 (PNR _ _ _ _))
              (never-n p m ex sy es acc S cl aa a2 ma2 d
                (MkGCN sy es acc q2 o2 c1 s2 (Cons (Bool) w l) r2 hh (GEd sy es acc o2 cn sl w l me nw gl) gr2 nb1) s1 hs1))))))))
