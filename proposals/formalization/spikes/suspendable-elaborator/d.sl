(def-adts $ (Frames : ((Tree) t) ((Nat) g) ((Tree) top) -> Type)
  enum
  (many FTop : (erased (Tree) top) -> (Frames top (Zero) top))
  (many FNodeL : (erased (Tree) l top) (erased (Nat) g) (many (Tree) r) (many (Frames (TNode l r) g top) up) -> (Frames l g top))
  (many FNodeR : (erased (Tree) l r top) (erased (Nat) g g1) (many (Nat) a) (erased (Elab l g a g1) pa) (many (Frames (TNode l r) g top) up) -> (Frames r g1 top))
  (many FIfC : (erased (Tree) c top) (erased (Nat) g) (many (Tree) th el) (many (Frames (TIf c th el) g top) up) -> (Frames c g top))
  (many FIfZero : (erased (Tree) c th el top) (erased (Nat) g g1) (erased (Elab c g (Zero) g1) pc) (many (Frames (TIf c th el) g top) up) -> (Frames th g1 top))
  (many FIfSucc : (erased (Tree) c th el top) (erased (Nat) g m g1) (erased (Elab c g (Succ m) g1) pc) (many (Frames (TIf c th el) g top) up) -> (Frames el g1 top)))

(def-adts $ (DState : ((Tree) top) -> Type)
  enum
  (many Down : (erased (Tree) top) (many (Tree) t) (many (Nat) g) (many (Frames t g top) fs) -> (DState top))
  (many Up : (erased (Tree) t top) (erased (Nat) g) (many (Nat) v g2) (erased (Elab t g v g2) p) (many (Frames t g top) fs) -> (DState top))
  (many Running : (erased (Tree) top) (many (Nat) s n k g) (erased (Reach s n k) r) (many (Frames (TRun s) g top) fs) -> (DState top)))

(def-adts $ (DTurn : ((Tree) top) -> Type)
  enum
  (many DGo : (erased (Tree) top) (many (DState top) st) (many (Nat) asks) -> (DTurn top))
  (many DFinished : (erased (Tree) top) (many (Nat) v g2) (erased (Elab top (Zero) v g2) p) -> (DTurn top))
  (many DCrashed : (erased (Tree) top) -> (DTurn top)))

(def-fns _ $ (many dturn : (erased (Tree) top) (many (DState top) st) -> (many (DTurn top) r))
  (match many st _
    ((Down _ t g fs)
      (match many t _
        ((TLeaf n) (DGo _ (Up _ _ _ n g (ELeaf n g) fs) 0))
        ((TGen) (DGo _ (Up _ _ _ g (Succ g) (EGen g) fs) 0))
        ((TNode l r) (DGo _ (Down _ l g (FNodeL _ _ _ r fs)) 0))
        ((TRun s) (DGo _ (Running _ s s (Zero) g (ReachRefl s) fs) 1))
        ((TIf c th el) (DGo _ (Down _ c g (FIfC _ _ _ th el fs)) 0))))
    ((Up _ _ g v g2 p fs)
      (match many fs _
        ((FTop _) (DFinished _ v g2 p))
        ((FNodeL _ _ _ r up) (DGo _ (Down _ r g2 (FNodeR _ _ _ _ _ v p up)) 0))
        ((FNodeR l r _ g0 _ a pa up)
          (let ((many c) (erased pc)) (add a v))
          (DGo _ (Up _ _ _ c g2 (ENode l r g0 a g v g2 c pa p pc) up) 0))
        ((FIfC _ _ _ th el up)
          (match many (nat-zero-dec v) _
            ((IsZero) (DGo _ (Down _ th g2 (FIfZero _ _ _ _ _ _ p up)) 0))
            ((IsSucc _) (DGo _ (Down _ el g2 (FIfSucc _ _ _ _ _ _ _ p up)) 0))))
        ((FIfZero c th el _ g0 _ pc up) (DGo _ (Up _ _ _ v g2 (EIfZero c th el g0 g v g2 pc p) up) 0))
        ((FIfSucc c th el _ g0 m _ pc up) (DGo _ (Up _ _ _ v g2 (EIfSucc c th el g0 m g v g2 pc p) up) 0))))
    ((Running _ s n k g r fs)
      (match many (step n) _
        ((Halted) (DGo _ (Up _ _ _ k g (ERun s k g (reach-runs s n k (Zero) k r (RunsHalt) (add-zero-right k))) fs) 0))
        ((Stuck) (DCrashed _))
        ((Next _ n2 st1) (DGo _ (Running _ s n2 (Succ k) g (ReachStep s n n2 k r st1) fs) 0))))))

(def-lvl drive-lvl)
(def-lvl P)

(def-fns drive-lvl $ (many drive : (unique (World) w at vacant-slot) (many (Tree) t) (many (DState t) st) (many (Nat) asks steps) -> (unique (World) w2 at w) (unique (Program P) p))
  (match many (dturn _ st) _
    ((DGo _ st2 c)
      (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
        (drive v t st2 (nat-add asks c) (Succ steps)))
      (values w (Continue P again)))
    ((DFinished _ v g2 p)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut (report t v g2 "asks" asks (Succ steps) p))))
      (values w1 (Exit P code0)))
    ((DCrashed _)
      (let ((unique w1) (many _)) (world-do _ w (WriteErr "machine stuck\n")))
      (values w1 (Exit P code2)))))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many t)) (tree-of-args args))
  (drive w1 t (Down _ t (Zero) (FTop _)) 0 0))

(Continue P start)
