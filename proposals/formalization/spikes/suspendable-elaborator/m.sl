(def-adts $ (Walked : ((Tree) t) ((Nat) g) -> Type)
  enum
  (many MkWalked : (erased (Tree) t) (erased (Nat) g) (many (Nat) v g2) (erased (Elab t g v g2) p) -> (Walked t g)))

(def-lvl W)
(def-lvl K)

(def-adts $ (ElabM : (Type A) -> Type)
  enum
  (many Ret : (erased Type A) (many A a) -> (ElabM A))
  (many Ask : (erased Type A) (many (Nat) s) (many (Fn K (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM A) next)) k) -> (ElabM A))
  (many Bind : (erased Type A X) (many (ElabM X) m) (many (Fn K (many X x) -> (many (ElabM A) next)) f) -> (ElabM A)))

(def-fns W $ (many walk : (subterm many (Tree) t) (many (Nat) g) -> (many (ElabM (Walked t g)) m))
  (match many t _
    ((TLeaf n) (Ret _ (MkWalked _ _ n g (ELeaf n g))))
    ((TGen) (Ret _ (MkWalked _ _ g (Succ g) (EGen g))))
    ((TNode l r)
      (def-fns K $ (many after-l : (many (Walked l g) wl) -> (many (ElabM (Walked t g)) next))
        (let-match many wl (MkWalked _ _ a g1 pa))
        (def-fns K $ (many after-r : (many (Walked r g1) wr) -> (many (ElabM (Walked t g)) next))
          (let-match many wr (MkWalked _ _ b g2 pb))
          (let ((many c) (erased pc)) (add a b))
          (Ret _ (MkWalked _ _ c g2 (ENode l r g a g1 b g2 c pa pb pc))))
        (Bind _ _ (walk r g1) after-r))
      (Bind _ _ (notail $ walk l g) after-l))
    ((TRun s)
      (def-fns K $ (many answered : (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM (Walked t g)) next))
        (Ret _ (MkWalked _ _ a g (ERun s a g p))))
      (Ask _ s answered))
    ((TIf c th el)
      (def-fns K $ (many after-c : (many (Walked c g) wc) -> (many (ElabM (Walked t g)) next))
        (let-match many wc (MkWalked _ _ v g1 pc))
        (match many (nat-zero-dec v) _
          ((IsZero)
            (def-fns K $ (many after-th : (many (Walked th g1) wt) -> (many (ElabM (Walked t g)) next))
              (let-match many wt (MkWalked _ _ b g2 pt))
              (Ret _ (MkWalked _ _ b g2 (EIfZero c th el g g1 b g2 pc pt))))
            (Bind _ _ (walk th g1) after-th))
          ((IsSucc m)
            (def-fns K $ (many after-el : (many (Walked el g1) we) -> (many (ElabM (Walked t g)) next))
              (let-match many we (MkWalked _ _ b g2 pe))
              (Ret _ (MkWalked _ _ b g2 (EIfSucc c th el g m g1 b g2 pc pe))))
            (Bind _ _ (walk el g1) after-el))))
      (Bind _ _ (notail $ walk c g) after-c))))

(def-adts $ (Stack : (Type X) (Type A) -> Type)
  enum
  (many KNil : (erased Type A) -> (Stack A A))
  (many KCons : (erased Type X Y A) (many (Fn K (many X x) -> (many (ElabM Y) next)) f) (many (Stack Y A) rest) -> (Stack X A)))

(def-adts $ (MState : (Type A) -> Type)
  enum
  (many Stepping : (erased Type X A) (many (ElabM X) m) (many (Stack X A) stack) -> (MState A))
  (many Running : (erased Type X A) (many (Nat) s n k) (erased (Reach s n k) r)
     (many (Fn K (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM X) next)) cont) (many (Stack X A) stack) -> (MState A)))

(def-adts $ (MTurn : (Type A) -> Type)
  enum
  (many MGo : (erased Type A) (many (MState A) st) (many (Nat) asks) -> (MTurn A))
  (many MFinished : (erased Type A) (many A a) -> (MTurn A))
  (many MCrashed : (erased Type A) -> (MTurn A)))

(def-fns _ $ (many mturn : (erased Type A) (many (MState A) st) -> (many (MTurn A) r))
  (match many st _
    ((Stepping X _ m stack)
      (let-match many m (Ret _ x)
        ((Ask _ s k) (MGo _ (Running X A s s (Zero) (ReachRefl s) k stack) 1))
        ((Bind _ X1 m1 f) (MGo _ (Stepping X1 A m1 (KCons X1 X A f stack)) 0)))
      (match many stack _
        ((KNil _) (MFinished _ x))
        ((KCons _ Y _ f rest) (MGo _ (Stepping Y A (f x) rest) 0))))
    ((Running X _ s n k r cont stack)
      (match many (step n) _
        ((Halted) (MGo _ (Stepping X A (cont k (reach-runs s n k (Zero) k r (RunsHalt) (add-zero-right k))) stack) 0))
        ((Stuck) (MCrashed _))
        ((Next _ n2 st1) (MGo _ (Running X A s n2 (Succ k) (ReachStep s n n2 k r st1) cont stack) 0))))))

(def-lvl drive-lvl)
(def-lvl P)

(def-fns drive-lvl $ (many drive : (unique (World) w at vacant-slot) (many (Tree) t) (many (MState (Walked t (Zero))) st) (many (Nat) asks steps) -> (unique (World) w2 at w) (unique (Program P) p))
  (match many (mturn _ st) _
    ((MGo _ st2 c)
      (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
        (drive v t st2 (nat-add asks c) (Succ steps)))
      (values w (Continue P again)))
    ((MFinished _ wd)
      (let-match many wd (MkWalked _ _ v g2 p))
      (let ((unique w1) (many _)) (world-do _ w (WriteOut (report t v g2 "asks" asks (Succ steps) p))))
      (values w1 (Exit P code0)))
    ((MCrashed _)
      (let ((unique w1) (many _)) (world-do _ w (WriteErr "machine stuck\n")))
      (values w1 (Exit P code2)))))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many t)) (tree-of-args args))
  (drive w1 t (Stepping _ _ (walk t (Zero)) (KNil _)) 0 0))

(Continue P start)
