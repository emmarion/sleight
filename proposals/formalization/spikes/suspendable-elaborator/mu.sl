(def-adts $ (Walked : ((Tree) t) ((Nat) g) -> Type)
  enum
  (many MkWalked : (erased (Tree) t) (erased (Nat) g) (many (Nat) v g2) (erased (Elab t g v g2) p) -> (Walked t g)))

(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) notes) -> (Box)))

(def-fns _ $ (many note : (unique (Box) b) -> (unique (Box) b2 at b))
  (match unique b _
    ((MkBox n cell) (cell (Succ n)))))

(def-lvl W)
(def-lvl K)

(def-adts $ (ElabM : (Type A) -> Type)
  enum
  (many Ret : (erased Type A) (many A a) -> (ElabM A))
  (many Ask : (erased Type A) (many (Nat) s)
     (many (Fn K (unique (Box) b) (many (Nat) a) (erased (Runs s a) p) -> (unique (Box) b2 at b) (many (ElabM A) next)) k) -> (ElabM A))
  (many Bind : (erased Type A X) (many (ElabM X) m)
     (many (Fn K (unique (Box) b) (many X x) -> (unique (Box) b2 at b) (many (ElabM A) next)) f) -> (ElabM A)))

(def-fns W $ (many walk : (unique (Box) b) (subterm many (Tree) t) (many (Nat) g) -> (unique (Box) b2 at b) (many (ElabM (Walked t g)) m))
  (match many t _
    ((TLeaf n) (values (note b) (Ret _ (MkWalked _ _ n g (ELeaf n g)))))
    ((TGen) (values (note b) (Ret _ (MkWalked _ _ g (Succ g) (EGen g)))))
    ((TNode l r)
      (def-fns K $ (many after-l : (unique (Box) b1) (many (Walked l g) wl) -> (unique (Box) b2 at b1) (many (ElabM (Walked t g)) next))
        (let-match many wl (MkWalked _ _ a g1 pa))
        (def-fns K $ (many after-r : (unique (Box) b3) (many (Walked r g1) wr) -> (unique (Box) b4 at b3) (many (ElabM (Walked t g)) next))
          (let-match many wr (MkWalked _ _ x g2 pb))
          (let ((many c) (erased pc)) (add a x))
          (values b3 (Ret _ (MkWalked _ _ c g2 (ENode l r g a g1 x g2 c pa pb pc)))))
        (let ((unique b5) (many mr)) (walk b1 r g1))
        (values b5 (Bind _ _ mr after-r)))
      (let ((unique b6) (many ml)) (notail $ walk b l g))
      (values b6 (Bind _ _ ml after-l)))
    ((TRun s)
      (def-fns K $ (many answered : (unique (Box) b1) (many (Nat) a) (erased (Runs s a) p) -> (unique (Box) b2 at b1) (many (ElabM (Walked t g)) next))
        (values (note b1) (Ret _ (MkWalked _ _ a g (ERun s a g p)))))
      (values b (Ask _ s answered)))
    ((TIf c th el)
      (def-fns K $ (many after-c : (unique (Box) b1) (many (Walked c g) wc) -> (unique (Box) b2 at b1) (many (ElabM (Walked t g)) next))
        (let-match many wc (MkWalked _ _ v g1 pc))
        (match many (nat-zero-dec v) _
          ((IsZero)
            (def-fns K $ (many after-th : (unique (Box) b3) (many (Walked th g1) wt) -> (unique (Box) b4 at b3) (many (ElabM (Walked t g)) next))
              (let-match many wt (MkWalked _ _ x g2 pt))
              (values b3 (Ret _ (MkWalked _ _ x g2 (EIfZero c th el g g1 x g2 pc pt)))))
            (let ((unique b5) (many mt)) (walk b1 th g1))
            (values b5 (Bind _ _ mt after-th)))
          ((IsSucc m)
            (def-fns K $ (many after-el : (unique (Box) b3) (many (Walked el g1) we) -> (unique (Box) b4 at b3) (many (ElabM (Walked t g)) next))
              (let-match many we (MkWalked _ _ x g2 pe))
              (values b3 (Ret _ (MkWalked _ _ x g2 (EIfSucc c th el g m g1 x g2 pc pe)))))
            (let ((unique b5) (many me)) (walk b1 el g1))
            (values b5 (Bind _ _ me after-el)))))
      (let ((unique b6) (many mc)) (notail $ walk b c g))
      (values b6 (Bind _ _ mc after-c)))))

(def-adts $ (Stack : (Type X) (Type A) -> Type)
  enum
  (many KNil : (erased Type A) -> (Stack A A))
  (many KCons : (erased Type X Y A) (many (Fn K (unique (Box) b) (many X x) -> (unique (Box) b2 at b) (many (ElabM Y) next)) f) (many (Stack Y A) rest) -> (Stack X A)))

(def-adts $ (MState : (Type A) -> Type)
  enum
  (many Stepping : (erased Type X A) (many (ElabM X) m) (many (Stack X A) stack) -> (MState A))
  (many Running : (erased Type X A) (many (Nat) s n k) (erased (Reach s n k) r)
     (many (Fn K (unique (Box) b) (many (Nat) a) (erased (Runs s a) p) -> (unique (Box) b2 at b) (many (ElabM X) next)) cont) (many (Stack X A) stack) -> (MState A)))

(def-adts $ (MTurn : (Type A) -> Type)
  enum
  (many MGo : (erased Type A) (many (MState A) st) (many (Nat) asks) -> (MTurn A))
  (many MFinished : (erased Type A) (many A a) -> (MTurn A))
  (many MCrashed : (erased Type A) -> (MTurn A)))

(def-fns _ $ (many mturn : (unique (Box) b) (erased Type A) (many (MState A) st) -> (unique (Box) b2 at b) (many (MTurn A) r))
  (match many st _
    ((Stepping X _ m stack)
      (let-match many m (Ret _ x)
        ((Ask _ s k) (values b (MGo _ (Running X A s s (Zero) (ReachRefl s) k stack) 1)))
        ((Bind _ X1 m1 f) (values b (MGo _ (Stepping X1 A m1 (KCons X1 X A f stack)) 0))))
      (let-match many stack (KCons _ Y _ f rest) ((KNil _) (values b (MFinished _ x))))
      (let ((unique b1) (many m2)) (f b x))
      (values b1 (MGo _ (Stepping Y A m2 rest) 0)))
    ((Running X _ s n k r cont stack)
      (let-match many (step n) (Halted)
        ((Stuck) (values b (MCrashed _)))
        ((Next _ n2 st1) (values b (MGo _ (Running X A s n2 (Succ k) (ReachStep s n n2 k r st1) cont stack) 0))))
      (let ((unique b1) (many m2)) (cont b k (reach-runs s n k (Zero) k r (RunsHalt) (add-zero-right k))))
      (values b1 (MGo _ (Stepping X A m2 stack) 0)))))

(def-lvl drive-lvl)
(def-lvl P)

(def-fns drive-lvl $ (many drive : (unique (World) w at vacant-slot) (unique (Box) b) (many (Tree) t) (many (MState (Walked t (Zero))) st) (many (Nat) asks steps) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique b1) (many turned)) (mturn b _ st))
  (match many turned _
    ((MGo _ st2 c)
      (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
        (drive v b1 t st2 (nat-add asks c) (Succ steps)))
      (values w (Continue P again)))
    ((MFinished _ wd)
      (let-match many wd (MkWalked _ _ v g2 p))
      (let-match many (share b1) (MkBox notes))
      (let ((unique w1) (many _)) (world-do _ w (WriteOut (str-append "notes " $ str-append (nat-str notes) $ str-append " " $ report t v g2 "asks" asks (Succ steps) p))))
      (values w1 (Exit P code0)))
    ((MCrashed _)
      (let ((unique w1) (many _)) (world-do _ w (WriteErr "machine stuck\n")))
      (values w1 (Exit P code2)))))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many t)) (tree-of-args args))
  (let ((unique b) (many m)) (walk (MkBox 0) t (Zero)))
  (drive w1 b t (Stepping _ _ m (KNil _)) 0 0))

(Continue P start)
