; pcs, the configurations of chunks.sl's css cut afresh into pieces of roughly equal checking time, one native-compute thunk
; each, and AllRedC over the pieces turned into AllRedC over css (allredc-pieces). Load after chunks.sl.

(def-adts $ (CfApp : ((List (Config)) a b c) -> Type)
  enum
  (many CANil : (erased (List (Config)) b) -> (CfApp (Nil (Config)) b b))
  (many CACons : (erased (Config) x) (erased (List (Config)) a b c) (erased (CfApp a b c) p)
      -> (CfApp (Cons (Config) x a) b (Cons (Config) x c))))

(def-adts $ (CfCat : ((List (List (Config))) kss) ((List (Config)) cfs) -> Type)
  enum
  (many FNil : -> (CfCat (Nil (List (Config))) (Nil (Config))))
  (many FSkip : (erased (List (List (Config))) kss) (erased (List (Config)) cfs) (erased (CfCat kss cfs) p)
      -> (CfCat (Cons (List (Config)) (Nil (Config)) kss) cfs))
  (many FCons : (erased (Config) cf) (erased (List (Config)) cs cfs) (erased (List (List (Config))) kss)
      (erased (CfCat (Cons (List (Config)) cs kss) cfs) p) -> (CfCat (Cons (List (Config)) (Cons (Config) cf cs) kss) (Cons (Config) cf cfs))))

(def-fns _ $ (erased allred-cat : (erased (Level) X) (erased (List (List (Config))) kss) (erased (List (Config)) cfs) (subterm erased (CfCat kss cfs) q)
    (erased (AllRedC X kss) ev) -> (erased (AllRed X cfs) r))
  (match erased q _
    ((FNil) (ARNil X))
    ((FSkip kss1 _ q1) (let-match erased ev (ARCCons _ _ _ _ ev1)) (allred-cat X kss1 cfs q1 ev1))
    ((FCons cf cs cfs1 kss1 q1)
      (let-match erased ev (ARCCons _ _ _ a ev1))
      (let-match erased a (ARCons _ _ _ p a1))
      (ARCons X cf cfs1 p (allred-cat X (Cons _ cs kss1) cfs1 q1 (ARCCons X cs kss1 a1 ev1))))))

(def-fns _ $ (erased allredc-uncat : (erased (Level) X) (erased (List (List (Config))) kss) (erased (List (Config)) cfs) (subterm erased (CfCat kss cfs) q)
    (erased (AllRed X cfs) ev) -> (erased (AllRedC X kss) r))
  (let-match erased q (FCons cf cs cfs1 kss1 q1)
    ((FNil) (ARCNil X))
    ((FSkip kss1 _ q1) (ARCCons X (Nil _) kss1 (ARNil X) (allredc-uncat X kss1 cfs q1 ev))))
  (let-match erased ev (ARCons _ _ _ p ev1))
  (let-match erased (allredc-uncat X (Cons _ cs kss1) cfs1 q1 ev1) (ARCCons _ _ _ a r1))
  (ARCCons X (Cons _ cf cs) kss1 (ARCons X cf cs p a) r1))

(def-fns _ $ (erased cat-front : (erased (List (Config)) a b c) (subterm erased (CfApp a b c) q) (erased (List (List (Config))) kss)
    (erased (CfCat kss b) p) -> (erased (CfCat (Cons (List (Config)) a kss) c) r))
  (let-match erased q (CACons x a1 _ c1 q1) ((CANil _) (FSkip kss b p)))
  (FCons x a1 c1 kss (cat-front a1 b c1 q1 kss p)))

(def-fns _ $ (erased app-nil : (subterm erased (List (Config)) a) -> (erased (CfApp a (Nil (Config)) a) q))
  (let-match erased a (Cons _ x a1) ((Nil _) (CANil (Nil _))))
  (CACons x a1 (Nil _) a1 (app-nil a1)))

(def-fns _ $ (many cf-append : (subterm many (List (Config)) a) (many (List (Config)) b) -> (many (List (Config)) c) (erased (CfApp a b c) q))
  (let-match many a (Cons _ x a1) ((Nil _) (values b (CANil b))))
  (let ((many c) (erased q)) (notail $ cf-append a1 b))
  (values (Cons _ x c) (CACons x a1 b c q)))

(def-fns _ $ (many cf-concat : (subterm many (List (List (Config))) kss) -> (many (List (Config)) cfs) (erased (CfCat kss cfs) q))
  (let-match many kss (Cons _ cs rest) ((Nil _) (values (Nil _) (FNil))))
  (let ((many b) (erased p)) (notail $ cf-concat rest))
  (let ((many c) (erased q)) (cf-append cs b))
  (values c (cat-front cs b c q rest p)))

(def-fns _ $ (many cf-take : (subterm many (Nat) n) (many (List (Config)) cs) -> (many (List (Config)) a b) (erased (CfApp a b cs) q))
  (let-match many n (Succ n1) ((Zero) (values (Nil _) cs (CANil cs))))
  (let-match many cs (Cons _ x rest) ((Nil _) (values (Nil _) cs (CANil cs))))
  (let ((many a) (many b) (erased q)) (notail $ cf-take n1 rest))
  (values (Cons _ x a) b (CACons x a b rest q)))

(def-fns _ $ (many cf-cut : (subterm many (List (Nat)) ns) (many (List (Config)) cfs) -> (many (List (List (Config))) pcs) (erased (CfCat pcs cfs) q))
  (let-match many ns (Cons _ n rest)
    ((Nil _) (values (Cons _ cfs (Nil _)) (cat-front cfs (Nil _) cfs (app-nil cfs) (Nil _) (FNil)))))
  (let ((many a) (many b) (erased q)) (cf-take n cfs))
  (let ((many pcs) (erased p)) (notail $ cf-cut rest b))
  (values (Cons _ a pcs) (cat-front a b cfs q pcs p)))

(def-fns _ $ (erased allredc-pieces : (erased (Level) X) (erased (List (List (Config))) pcs kss) (erased (List (Config)) cfs) (erased (CfCat pcs cfs) qp)
    (erased (CfCat kss cfs) qk) (erased (AllRedC X pcs) ev) -> (erased (AllRedC X kss) r))
  (allredc-uncat X kss cfs qk (allred-cat X pcs cfs qp ev)))
