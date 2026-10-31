(def-adts $ (Col : -> Type)
  enum
  (many C0 : -> (Col))
  (many C1 : -> (Col))
  (many C2 : -> (Col))
  (many C3 : -> (Col)))

(def-adts $ (Perm : -> Type)
  enum
  (many MkPerm : (many (Col) p1 p2 p3) -> (Perm)))

(def-adts $ (Step : -> Type)
  enum
  (many SR : (many (Nat) n) -> (Step))
  (many SRr : -> (Step))
  (many SY : -> (Step))
  (many SH : -> (Step))
  (many SU : -> (Step))
  (many SK : -> (Step))
  (many SA : -> (Step)))

(def-adts $ (Config : -> Type)
  enum
  (many MkConfig : (many (Bool) sym) (many (List (Nat)) contract) (many (List (Step)) prog) -> (Config)))

(def-adts $ (Ctree : -> Type)
  enum
  (many CNode : (many (Ctree) t1 t2 t3) -> (Ctree))
  (many CLeaf : (many (Ctree) lf) -> (Ctree))
  (many CEmpty : -> (Ctree)))

(def-adts $ (Gsym : -> Type)
  enum
  (many GPush : -> (Gsym))
  (many GSkip : -> (Gsym))
  (many GPop0 : -> (Gsym))
  (many GPop1 : -> (Gsym)))

(def-adts $ (Gtree : -> Type)
  enum
  (many GNode : (many (Gtree) t0 t1 t2 t3) -> (Gtree))
  (many GL0 : -> (Gtree))
  (many GL1 : -> (Gtree))
  (many GL2 : -> (Gtree))
  (many GL3 : -> (Gtree))
  (many GL01 : -> (Gtree))
  (many GL12 : -> (Gtree))
  (many GL13 : -> (Gtree))
  (many GL23 : -> (Gtree))
  (many GEmpty : -> (Gtree)))

(def-adts $ (Bstack : -> Type)
  enum
  (many BS0 : -> (Bstack))
  (many BP0 : (many (Bstack) bs) -> (Bstack))
  (many BP1 : (many (Bstack) bs) -> (Bstack)))

(def-adts $ (Rx : (Type T) -> Type)
  enum
  (many MkRx : (erased Type T) (many (Bstack) bs) (many T t) -> (Rx T)))

; xs is the list of restrictions that the cells hold.
(def-adts $ (RxL : (Type T) ((List (Rx T)) xs) -> Type)
  enum
  (many RxNil : (erased Type T) -> (RxL T (Nil (Rx T))))
  (many RxCons : (erased Type T) (many (Bstack) bs) (many T t) (erased (List (Rx T)) rest) (many (RxL T rest) tl)
      -> (RxL T (Cons (Rx T) (MkRx T bs t) rest))))

(def-fns _ $ (many bif : (erased Type A) (many (Bool) b) (many A x y) -> (many A r))
  (match many b _ ((BTrue) x) ((BFalse) y)))

(def-fns _ $ (many orb : (many (Bool) a b) -> (many (Bool) c))
  (bif _ a (BTrue) b))

(def-fns _ $ (many andb : (many (Bool) a b) -> (many (Bool) c))
  (bif _ a b (BFalse)))

(def-fns _ $ (many negb : (many (Bool) a) -> (many (Bool) c))
  (bif _ a (BFalse) (BTrue)))

(def-fns _ $ (many nat-eqb : (many (Nat) a b) -> (many (Bool) c))
  (match many (nat-eq a b) _ ((Equal _ _ _) (BTrue)) ((Unequal _ _ _ _ _) (BFalse))))

(def-fns _ $ (many nat-ltb : (many (Nat) a b) -> (many (Bool) c))
  (match many (nat-cmp a b) _ ((CLt _ _ _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many monus : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (let-match many b (Succ b1) ((Zero) a))
  (let-match many a (Succ a1) ((Zero) 0))
  (tail $ monus a1 b1))

(def-fns _ $ (many mem-nat : (many (Nat) x) (subterm many (List (Nat)) xs) -> (many (Bool) b))
  (let-match many xs (Cons _ y rest) ((Nil _) (BFalse)))
  (match many (nat-eqb x y) _ ((BTrue) (BTrue)) ((BFalse) (tail $ mem-nat x rest))))

(def-fns _ $ (many nilp : (erased Type A) (many (List A) xs) -> (many (Bool) b))
  (match many xs _ ((Nil _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many size : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (let-match many xs (Cons _ _ rest) ((Nil _) 0))
  (Succ $ notail $ size _ rest))

(def-fns _ $ (many cat : (erased Type A) (subterm many (List A) xs) (many (List A) ys) -> (many (List A) zs))
  (let-match many xs (Cons _ x rest) ((Nil _) ys))
  (Cons _ x $ notail $ cat _ rest ys))

(def-fns _ $ (many rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) zs))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (tail $ rev-onto _ rest (Cons _ x acc)))

(def-fns _ $ (many take : (erased Type A) (subterm many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (let-match many n (Succ n1) ((Zero) (Nil _)))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ x $ notail $ take _ n1 rest))

(def-fns _ $ (many drop : (erased Type A) (subterm many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (let-match many n (Succ n1) ((Zero) xs))
  (let-match many xs (Cons _ _ rest) ((Nil _) (Nil _)))
  (tail $ drop _ n1 rest))

(def-fns _ $ (many rot : (erased Type A) (many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (cat _ (drop _ n xs) (take _ n xs)))

(def-fns _ $ (many rotr : (erased Type A) (many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (rot _ (monus (size _ xs) n) xs))

(def-fns _ $ (many nseq : (erased Type A) (subterm many (Nat) n) (many A x) -> (many (List A) ys))
  (let-match many n (Succ n1) ((Zero) (Nil _)))
  (Cons _ x $ notail $ nseq _ n1 x))

(def-fns _ $ (many count-b : (many (Bool) b) (subterm many (List (Bool)) bs) -> (many (Nat) n))
  (let-match many bs (Cons _ x rest) ((Nil _) 0))
  (let ((many k)) (notail $ count-b b rest))
  (bif _ (orb (andb b x) (negb (orb b x))) (Succ k) k))

(let ((many p123)) (MkPerm (C1) (C2) (C3)))
(let ((many p132)) (MkPerm (C1) (C3) (C2)))
(let ((many p231)) (MkPerm (C2) (C3) (C1)))
(let ((many p312)) (MkPerm (C3) (C1) (C2)))

(def-fns _ $ (many cc : (many (Col) c) (many (List (Col)) et) -> (many (List (Col)) r))
  (Cons _ c $ Cons _ c et))

(let ((many simple-leaf)) (CLeaf (CEmpty)))

(def-fns _ $ (many cprsize : (subterm many (List (Step)) cp) -> (many (Nat) n))
  (let-match many cp (Cons _ s rest) ((Nil _) 2))
  (let ((many k)) (notail $ cprsize rest))
  (match many s _
    ((SY) (Succ k))
    ((SU) (Succ $ Succ k))
    ((SK) (Succ $ monus k 2))
    ((SA) (bif _ (nat-ltb 2 k) (monus k 2) k))
    (else k)))

(def-fns _ $ (many cpksize : (subterm many (List (Step)) cp) -> (many (Nat) n))
  (let-match many cp (Cons _ s rest) ((Nil _) 0))
  (let ((many k)) (notail $ cpksize rest))
  (match many s _ ((SH) (Succ k)) (else k)))

(def-fns _ $ (many ctrmask : (many (List (Nat)) cci) (many (Nat) i) (subterm many (Nat) n) -> (many (List (Bool)) m))
  (let-match many n (Succ n1) ((Zero) (Nil _)))
  (Cons _ (mem-nat i cci) $ notail $ ctrmask cci (Succ i) n1))

(def-fns _ $ (many cpadj : (many (List (Bool)) mr mk) (subterm many (List (Step)) cp) -> (many (List (Bool)) mr2 mk2))
  (let-match many cp (Cons _ s rest)
    ((Nil _)
      (let-match many mr (Cons _ b0 r1) ((Nil _) (values mr mk)))
      (let-match many r1 (Cons _ b1 r2) ((Nil _) (values mr mk)))
      (let-match many r2 (Nil _) (else (values mr mk)))
      (let-match many mk (Nil _) (else (values mr mk)))
      (values (Cons _ b1 $ Cons _ b0 $ Nil _) (Nil _))))
  (match many s _
    ((SR n)
      (let ((many a) (many b)) (notail $ cpadj (rotr _ n mr) mk rest))
      (values (rot _ n a) b))
    ((SY)
      (let-match many mr (Cons _ b0 r1) ((Nil _) (values mr mk)))
      (let-match many r1 (Cons _ b1 r2) ((Nil _) (values mr mk)))
      (let-match many r2 (Cons _ b2 r3) ((Nil _) (values mr mk)))
      (let ((many a) (many mk1)) (notail $ cpadj (Cons _ b0 $ Cons _ b2 r3) mk rest))
      (let-match many a (Cons _ a0 s1) ((Nil _) (values mr mk)))
      (let-match many s1 (Cons _ a2 s2) ((Nil _) (values mr mk)))
      (values (Cons _ (orb a0 b1) $ Cons _ (orb b0 b2) $ Cons _ (orb a2 b1) s2) mk1))
    ((SH)
      (let-match many mr (Cons _ b0 r1) ((Nil _) (values mr mk)))
      (let-match many r1 (Cons _ b1 r2) ((Nil _) (values mr mk)))
      (let-match many mk (Cons _ c1 k1) ((Nil _) (values mr mk)))
      (let ((many a) (many mk1)) (notail $ cpadj (Cons _ b0 $ Cons _ c1 r2) k1 rest))
      (let-match many a (Cons _ a0 s1) ((Nil _) (values mr mk)))
      (let-match many s1 (Cons _ a1 s2) ((Nil _) (values mr mk)))
      (let ((many (Bool) hd)) (match many r2 _ ((Cons _ x _) x) ((Nil _) b0)))
      (let ((many (List (Bool)) tl)) (match many s2 _ ((Cons _ a2 s3) (Cons _ (orb a2 b1) s3)) ((Nil _) s2)))
      (values (Cons _ (orb a0 b1) $ Cons _ (orb b0 $ orb c1 hd) tl) (Cons _ (orb a1 b1) mk1)))
    (else (values mr mk))))
