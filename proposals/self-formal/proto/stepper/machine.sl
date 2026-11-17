; A fuel-free certified stepper for spec.sl: a total step over a stack of commands and a memory, an erased
; trace of the steps taken, and a run whose final memory comes with an erased Runs derivation. Needs
; std/list.sl and spec.sl earlier on the command line. An overnight agent's spike; nothing here is settled.

(def-adts $ (RunsAll : ((Mem) m) ((List (Cmd)) k) ((Mem) m2) -> Type)
  enum
  (many RANil : (erased (Mem) m) -> (RunsAll m (Nil (Cmd)) m))
  (many RACons : (erased (Mem) m m1 m2) (erased (Cmd) c) (erased (List (Cmd)) k)
     (erased (Runs m c m1) d) (erased (RunsAll m1 k m2) ds) -> (RunsAll m (Cons (Cmd) c k) m2)))

(def-adts $ (Step : ((List (Cmd)) k) ((Mem) m) ((List (Cmd)) k2) ((Mem) m2) -> Type)
  enum
  (many SSkip : (erased (List (Cmd)) k) (erased (Mem) m) -> (Step (Cons (Cmd) (CSkip) k) m k m))
  (many SOp : (erased (List (Cmd)) k) (erased (Mem) m m2) (erased (Op) o) (erased (RunOp m o m2) r)
     -> (Step (Cons (Cmd) (COp o) k) m k m2))
  (many SSeq : (erased (List (Cmd)) k) (erased (Mem) m) (erased (Cmd) c1 c2)
     -> (Step (Cons (Cmd) (CSeq c1 c2) k) m (Cons (Cmd) c1 (Cons (Cmd) c2 k)) m))
  (many SIf : (erased (List (Cmd)) k) (erased (Mem) m) (erased (Nat) x) (erased (Cmd) c1 c2 c) (erased (Pick m x c1 c2 c) p)
     -> (Step (Cons (Cmd) (CIf x c1 c2) k) m (Cons (Cmd) c k) m))
  (many SWhile : (erased (List (Cmd)) k) (erased (Mem) m) (erased (Nat) x) (erased (Cmd) b)
     -> (Step (Cons (Cmd) (CWhile x b) k) m (Cons (Cmd) (CIf x (CSkip) (CSeq b (CWhile x b))) k) m)))

; Trace k0 m0 k m: the machine went from (k0, m0) to (k, m), newest step outermost.
(def-adts $ (Trace : ((List (Cmd)) k0) ((Mem) m0) ((List (Cmd)) k) ((Mem) m) -> Type)
  enum
  (many TNil : (erased (List (Cmd)) k0) (erased (Mem) m0) -> (Trace k0 m0 k0 m0))
  (many TSnoc : (erased (List (Cmd)) k0 k k2) (erased (Mem) m0 m m2) (erased (Trace k0 m0 k m) t) (erased (Step k m k2 m2) s)
     -> (Trace k0 m0 k2 m2)))

(def-fns _ $ (erased step-back : (erased (List (Cmd)) k k2) (erased (Mem) m m2 mf) (erased (Step k m k2 m2) s)
    (erased (RunsAll m2 k2 mf) a) -> (erased (RunsAll m k mf) r))
  (match erased s _
    ((SSkip _ _) (RACons m m mf (CSkip) k2 (ExSkip m) a))
    ((SOp _ _ _ o r) (RACons m m2 mf _ k2 (ExOp m m2 o r) a))
    ((SSeq k1 _ c1 c2)
      (let-match erased a (RACons _ ma _ _ _ d1 a1))
      (let-match erased a1 (RACons _ mb _ _ _ d2 a2))
      (RACons m mb mf _ k1 (ExSeq m ma mb c1 c2 d1 d2) a2))
    ((SIf k1 _ x c1 c2 c p)
      (let-match erased a (RACons _ ma _ _ _ d a1))
      (RACons m ma mf _ k1 (ExIf m ma x c1 c2 c p d) a1))
    ((SWhile k1 _ x b)
      (let-match erased a (RACons _ ma _ _ _ d a1))
      (RACons m ma mf _ k1 (ExWhile m ma x b d) a1))))

(def-fns _ $ (erased trace-back : (erased (List (Cmd)) k0 k) (erased (Mem) m0 m mf) (subterm erased (Trace k0 m0 k m) t)
    (erased (RunsAll m k mf) a) -> (erased (RunsAll m0 k0 mf) r))
  (match erased t _
    ((TNil _ _) a)
    ((TSnoc _ k1 _ _ m1 _ t1 s) (trace-back k0 k1 m0 m1 mf t1 (step-back k1 k m1 m mf s a)))))

(def-adts $ (NthOut : (Type A) ((List A) xs) ((Nat) i) -> Type)
  enum
  (many NthOk : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (NthOut A xs i))
  (many NthNo : (erased Type A) (erased (List A) xs) (erased (Nat) i) -> (NthOut A xs i)))

(def-adts $ (SetOut : (Type A) ((List A) xs) ((Nat) i) (A y) -> Type)
  enum
  (many SetOk : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A y) (many (List A) ys) (erased (SetNth A xs i y ys) p)
     -> (SetOut A xs i y))
  (many SetNo : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A y) -> (SetOut A xs i y)))

(def-fns _ $ (many nth-p : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (NthOut A xs i) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (NthNo _ _ _)))
  (let-match many i (Succ j) ((Zero) (NthOk _ _ _ x (NthHere _ x rest))))
  (let-match many (notail $ nth-p _ rest j) (NthOk _ _ _ y p) ((NthNo _ _ _) (NthNo _ _ _)))
  (NthOk _ _ _ y (NthThere _ x rest j y p)))

(def-fns _ $ (many set-p : (erased Type A) (subterm many (List A) xs) (many (Nat) i) (many A y) -> (many (SetOut A xs i y) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (SetNo _ _ _ _)))
  (let-match many i (Succ j) ((Zero) (SetOk _ _ _ _ (Cons _ y rest) (SetHere _ x y rest))))
  (let-match many (notail $ set-p _ rest j y) (SetOk _ _ _ _ rest2 p) ((SetNo _ _ _ _) (SetNo _ _ _ _)))
  (SetOk _ _ _ _ (Cons _ x rest2) (SetThere _ x rest j y rest2 p)))

(def-fns _ $ (many repeat-p : (erased Type A) (subterm many (Nat) n) (many A x) -> (many (List A) xs) (erased (Repeat A n x xs) p))
  (let-match many n (Succ j) ((Zero) (values (Nil _) (RepeatNil _ x))))
  (let ((many xs) (erased p)) (notail $ repeat-p _ j x))
  (values (Cons _ x xs) (RepeatCons _ j x xs p)))

(def-fns _ $ (many alloc-p : (erased Type A) (subterm many (List A) xs) (many A y) ->
    (many (Nat) a) (many (List A) ys) (erased (Alloc A xs y a ys) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Zero) (Cons _ y (Nil _)) (AllocNil _ y))))
  (let ((many a) (many ys) (erased p)) (notail $ alloc-p _ rest y))
  (values (Succ a) (Cons _ x ys) (AllocCons _ x rest y a ys p)))

(def-adts $ (OpOut : ((Mem) m) ((Op) o) -> Type)
  enum
  (many OpOk : (erased (Mem) m) (erased (Op) o) (many (Mem) m2) (erased (RunOp m o m2) r) -> (OpOut m o))
  (many OpNo : (erased (Mem) m) (erased (Op) o) -> (OpOut m o)))

(def-fns _ $ (many run-op : (many (Mem) m) (many (Op) o) -> (many (OpOut m o) r))
  (let-match many m (MkMem e h))
  (match many o _
    ((OSet x n)
      (let-match many (set-p _ e x (VNum n)) (SetOk _ _ _ _ e2 s) ((SetNo _ _ _ _) (OpNo _ _)))
      (OpOk _ _ (MkMem e2 h) (RSet e e2 h x n s)))
    ((OMov x y)
      (let-match many (nth-p _ e y) (NthOk _ _ _ v g) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many (set-p _ e x v) (SetOk _ _ _ _ e2 s) ((SetNo _ _ _ _) (OpNo _ _)))
      (OpOk _ _ (MkMem e2 h) (RMov e e2 h x y v g s)))
    ((OPred x y)
      (let-match many (nth-p _ e y) (NthOk _ _ _ v g) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many v (VNum k) ((VPtr _) (OpNo _ _)))
      (let-match many k (Succ n) ((Zero) (OpNo _ _)))
      (let-match many (set-p _ e x (VNum n)) (SetOk _ _ _ _ e2 s) ((SetNo _ _ _ _) (OpNo _ _)))
      (OpOk _ _ (MkMem e2 h) (RPred e e2 h x y n g s)))
    ((OAdd x y z)
      (let-match many (nth-p _ e y) (NthOk _ _ _ v1 g1) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many v1 (VNum a) ((VPtr _) (OpNo _ _)))
      (let-match many (nth-p _ e z) (NthOk _ _ _ v2 g2) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many v2 (VNum b) ((VPtr _) (OpNo _ _)))
      (let ((many c) (erased ad)) (add a b))
      (let-match many (set-p _ e x (VNum c)) (SetOk _ _ _ _ e2 s) ((SetNo _ _ _ _) (OpNo _ _)))
      (OpOk _ _ (MkMem e2 h) (RAdd e e2 h x y z a b c g1 g2 ad s)))
    ((OAlloc x n)
      (let ((many blk) (erased r)) (repeat-p _ n (VNum (Zero))))
      (let ((many a) (many h2) (erased al)) (alloc-p _ h blk))
      (let-match many (set-p _ e x (VPtr a)) (SetOk _ _ _ _ e2 s) ((SetNo _ _ _ _) (OpNo _ _)))
      (OpOk _ _ (MkMem e2 h2) (RAlloc e e2 h h2 x n a blk r al s)))
    ((ORead x pr i)
      (let-match many (nth-p _ e pr) (NthOk _ _ _ pv g1) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many pv (VPtr a) ((VNum _) (OpNo _ _)))
      (let-match many (nth-p _ h a) (NthOk _ _ _ blk g2) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many (nth-p _ blk i) (NthOk _ _ _ v g3) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many (set-p _ e x v) (SetOk _ _ _ _ e2 s) ((SetNo _ _ _ _) (OpNo _ _)))
      (OpOk _ _ (MkMem e2 h) (RRead e e2 h x pr i a blk v g1 g2 g3 s)))
    ((OWrite pr i y)
      (let-match many (nth-p _ e pr) (NthOk _ _ _ pv g1) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many pv (VPtr a) ((VNum _) (OpNo _ _)))
      (let-match many (nth-p _ e y) (NthOk _ _ _ v g2) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many (nth-p _ h a) (NthOk _ _ _ blk g3) ((NthNo _ _ _) (OpNo _ _)))
      (let-match many (set-p _ blk i v) (SetOk _ _ _ _ blk2 s1) ((SetNo _ _ _ _) (OpNo _ _)))
      (let-match many (set-p _ h a blk2) (SetOk _ _ _ _ h2 s2) ((SetNo _ _ _ _) (OpNo _ _)))
      (OpOk _ _ (MkMem e h2) (RWrite e h h2 pr i y a v blk blk2 g1 g2 g3 s1 s2)))))

(def-adts $ (PickOut : ((Mem) m) ((Nat) x) ((Cmd) c1) ((Cmd) c2) -> Type)
  enum
  (many Picked : (erased (Mem) m) (erased (Nat) x) (erased (Cmd) c1 c2) (many (Cmd) c) (erased (Pick m x c1 c2 c) p)
     -> (PickOut m x c1 c2))
  (many PickNo : (erased (Mem) m) (erased (Nat) x) (erased (Cmd) c1 c2) -> (PickOut m x c1 c2)))

(def-fns _ $ (many pick : (many (Mem) m) (many (Nat) x) (many (Cmd) c1 c2) -> (many (PickOut m x c1 c2) r))
  (let-match many m (MkMem e h))
  (let-match many (nth-p _ e x) (NthOk _ _ _ v g) ((NthNo _ _ _) (PickNo _ _ _ _)))
  (let-match many v (VNum k) ((VPtr _) (PickNo _ _ _ _)))
  (match many k _
    ((Zero) (Picked _ _ _ _ c1 (PickZ e h x c1 c2 g)))
    ((Succ n) (Picked _ _ _ _ c2 (PickS e h x n c1 c2 g)))))

(def-adts $ (StepOut : ((List (Cmd)) k) ((Mem) m) -> Type)
  enum
  (many SNext : (erased (List (Cmd)) k) (erased (Mem) m) (many (List (Cmd)) k2) (many (Mem) m2) (erased (Step k m k2 m2) s)
     -> (StepOut k m))
  (many SHalt : (erased (Mem) m) -> (StepOut (Nil (Cmd)) m))
  (many SStuck : (erased (List (Cmd)) k) (erased (Mem) m) -> (StepOut k m)))

(def-fns _ $ (many step : (many (List (Cmd)) k) (many (Mem) m) -> (many (StepOut k m) r))
  (let-match many k (Cons _ c rest) ((Nil _) (SHalt m)))
  (match many c _
    ((CSkip) (SNext _ _ rest m (SSkip rest m)))
    ((COp o)
      (let-match many (run-op m o) (OpOk _ _ m2 r) ((OpNo _ _) (SStuck _ _)))
      (SNext _ _ rest m2 (SOp rest m m2 o r)))
    ((CSeq c1 c2) (SNext _ _ (Cons _ c1 (Cons _ c2 rest)) m (SSeq rest m c1 c2)))
    ((CIf x c1 c2)
      (let-match many (pick m x c1 c2) (Picked _ _ _ _ c3 p) ((PickNo _ _ _ _) (SStuck _ _)))
      (SNext _ _ (Cons _ c3 rest) m (SIf rest m x c1 c2 c3 p)))
    ((CWhile x b) (SNext _ _ (Cons _ (CIf x (CSkip) (CSeq b (CWhile x b))) rest) m (SWhile rest m x b)))))

(def-adts $ (Outcome : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many Halted : (erased (Cmd) c0) (erased (Mem) m0) (many (Mem) mf) (erased (Runs m0 c0 mf) d) -> (Outcome c0 m0))
  (many Stuck : (erased (Cmd) c0) (erased (Mem) m0) -> (Outcome c0 m0)))

(def-adts $ (Advance : ((Cmd) c0) ((Mem) m0) ((List (Cmd)) k) ((Mem) m) -> Type)
  enum
  (many Running : (erased (Cmd) c0) (erased (Mem) m0) (erased (List (Cmd)) k) (erased (Mem) m) (many (List (Cmd)) k2) (many (Mem) m2)
     (erased (Trace (Cons (Cmd) c0 (Nil (Cmd))) m0 k2 m2) t) (erased (Step k m k2 m2) s) -> (Advance c0 m0 k m))
  (many Ended : (erased (Cmd) c0) (erased (Mem) m0) (erased (List (Cmd)) k) (erased (Mem) m) (many (Outcome c0 m0) o)
     -> (Advance c0 m0 k m)))

(def-fns _ $ (many advance : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m)
    (erased (Trace (Cons (Cmd) c0 (Nil (Cmd))) m0 k m) t) -> (many (Advance c0 m0 k m) r))
  (let-match many (step k m) (SHalt _)
    ((SNext _ _ k2 m2 s) (Running _ _ _ _ k2 m2 (TSnoc _ k k2 m0 m m2 t s) s))
    ((SStuck _ _) (Ended _ _ _ _ (Stuck _ _))))
  (let-match erased (trace-back _ _ m0 m m t (RANil m)) (RACons _ m1 _ _ _ d a))
  (let-match erased a (RANil _))
  (Ended _ _ _ _ (Halted _ _ m d)))
