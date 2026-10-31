; pcs, the chunks of chunks.sl cut into pieces of roughly equal checking time, one native-compute thunk each, and the
; regrouping of AllRedC over the pieces into AllRedC over the chunks (allredc-glue). Load after chunks.sl.

(def-adts $ (CfApp : ((List (Config)) a b c) -> Type)
  enum
  (many CANil : (erased (List (Config)) b) -> (CfApp (Nil (Config)) b b))
  (many CACons : (erased (Config) x) (erased (List (Config)) a b c) (erased (CfApp a b c) p)
      -> (CfApp (Cons (Config) x a) b (Cons (Config) x c))))

(def-adts $ (Glue : ((List (List (Config))) pcs kss) -> Type)
  enum
  (many GlNil : -> (Glue (Nil (List (Config))) (Nil (List (Config)))))
  (many GlNew : (erased (List (Config)) p) (erased (List (List (Config))) pcs kss) (erased (Glue pcs kss) g)
      -> (Glue (Cons (List (Config)) p pcs) (Cons (List (Config)) p kss)))
  (many GlPre : (erased (List (Config)) a b c) (erased (List (List (Config))) pcs kss) (erased (Glue pcs (Cons (List (Config)) b kss)) g)
      (erased (CfApp a b c) q) -> (Glue (Cons (List (Config)) a pcs) (Cons (List (Config)) c kss))))

(def-fns _ $ (erased allred-app : (erased (Level) X) (erased (List (Config)) a b c) (subterm erased (CfApp a b c) q) (erased (AllRed X a) ra)
    (erased (AllRed X b) rb) -> (erased (AllRed X c) r))
  (let-match erased q (CACons x a1 _ c1 q1) ((CANil _) rb))
  (let-match erased ra (ARCons _ _ _ p ra1))
  (ARCons X x c1 p (allred-app X a1 b c1 q1 ra1 rb)))

(def-fns _ $ (erased allredc-glue : (erased (Level) X) (erased (List (List (Config))) pcs kss) (subterm erased (Glue pcs kss) g)
    (erased (AllRedC X pcs) ev) -> (erased (AllRedC X kss) r))
  (match erased g _
    ((GlNil) (ARCNil X))
    ((GlNew p pcs1 kss1 g1)
      (let-match erased ev (ARCCons _ _ _ ap ev1))
      (ARCCons X p kss1 ap (allredc-glue X pcs1 kss1 g1 ev1)))
    ((GlPre a b c pcs1 kss1 g1 q)
      (let-match erased ev (ARCCons _ _ _ ap ev1))
      (let-match erased (allredc-glue X pcs1 (Cons _ b kss1) g1 ev1) (ARCCons _ _ _ bp r1))
      (ARCCons X c kss1 (allred-app X a b c q ap bp) r1))))

(def-fns _ $ (many cf-take : (subterm many (Nat) n) (many (List (Config)) cs) -> (many (List (Config)) a b) (erased (CfApp a b cs) q))
  (let-match many n (Succ n1) ((Zero) (values (Nil _) cs (CANil cs))))
  (let-match many cs (Cons _ x rest) ((Nil _) (values (Nil _) cs (CANil cs))))
  (let ((many a) (many b) (erased q)) (notail $ cf-take n1 rest))
  (values (Cons _ x a) b (CACons x a b rest q)))

(def-fns _ $ (many cut-chunk : (subterm many (List (Nat)) ns) (many (List (Config)) cs) (many (List (List (Config))) pcs)
    (erased (List (List (Config))) kss) (erased (Glue pcs kss) g)
    -> (many (List (List (Config))) pcs2) (erased (Glue pcs2 (Cons (List (Config)) cs kss)) g2))
  (let-match many ns (Cons _ n rest) ((Nil _) (values (Cons _ cs pcs) (GlNew cs pcs kss g))))
  (let ((many a) (many b) (erased q)) (cf-take n cs))
  (let ((many pcs1) (erased g1)) (notail $ cut-chunk rest b pcs kss g))
  (values (Cons _ a pcs1) (GlPre a b cs pcs1 kss g1 q)))

(def-fns _ $ (many cut-all : (many (List (List (Nat))) plan) (subterm many (List (List (Config))) kss)
    -> (many (List (List (Config))) pcs) (erased (Glue pcs kss) g))
  (let-match many kss (Cons _ cs rest) ((Nil _) (values (Nil _) (GlNil))))
  (let ((many ns) (many plan1)) (match many plan (((List (Nat)) x) ((List (List (Nat))) y)) ((Cons _ x y) (values x y)) ((Nil _) (values (Nil _) (Nil _)))))
  (let ((many pcs1) (erased g1)) (notail $ cut-all plan1 rest))
  (cut-chunk ns cs pcs1 rest g1))
