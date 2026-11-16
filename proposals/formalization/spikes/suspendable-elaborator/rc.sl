(def-adts $ (Spine : ((Tree) t) ((Nat) g) ((Tree) top) -> Type)
  enum
  (many SpTop : (erased (Tree) top) -> (Spine top (Zero) top))
  (many SpLeft : (erased (Tree) l top) (erased (Nat) g) (many (Tree) r) (many (Spine (TNode l r) g top) up) -> (Spine l g top))
  (many SpRight : (erased (Tree) l r top) (erased (Nat) g g1) (many (Nat) a) (erased (Elab l g a g1) pa) (many (Spine (TNode l r) g top) up) -> (Spine r g1 top)))

(def-adts $ (CState : ((Tree) top) -> Type)
  enum
  (many Sequencing : (erased (Tree) top) (many (Tree) t) (many (Nat) g) (many (Spine t g top) sp) -> (CState top))
  (many Elaborating : (erased (Tree) top) (many (Tree) t) (many (Nat) g) (many (List (Entry)) rev-log) (many (Spine t g top) sp) -> (CState top))
  (many Running : (erased (Tree) top) (many (Tree) t) (many (Nat) g) (many (List (Entry)) used) (many (Nat) s n k) (erased (Reach s n k) r) (many (Spine t g top) sp) -> (CState top))
  (many Committing : (erased (Tree) t top) (erased (Nat) g) (many (Nat) v g2) (erased (Elab t g v g2) p) (many (Spine t g top) sp) -> (CState top)))

(def-adts $ (CTurn : ((Tree) top) -> Type)
  enum
  (many CGo : (erased (Tree) top) (many (CState top) st) (many (Nat) calls) -> (CTurn top))
  (many CFinished : (erased (Tree) top) (many (Nat) v g2) (erased (Elab top (Zero) v g2) p) -> (CTurn top))
  (many CCrashed : (erased (Tree) top) -> (CTurn top)))

(def-fns _ $ (many cturn : (erased (Tree) top) (many (CState top) st) -> (many (CTurn top) r))
  (match many st _
    ((Sequencing _ t g sp)
      (match many t _
        ((TNode l r) (CGo _ (Elaborating _ l g (Nil _) (SpLeft _ _ _ r sp)) 0))
        (else (CGo _ (Elaborating _ t g (Nil _) sp) 0))))
    ((Elaborating _ t g rev-log sp)
      (match many (elab t g (rev-onto _ rev-log (Nil _)) (Nil _)) _
        ((Done _ _ v g2 _ _ p) (CGo _ (Committing _ _ _ v g2 p sp) 1))
        ((Need _ _ s used) (CGo _ (Running _ t g used s s (Zero) (ReachRefl s) sp) 1))))
    ((Running _ t g used s n k r sp)
      (match many (step n) _
        ((Halted) (CGo _ (Elaborating _ t g (Cons _ (MkEntry s k (reach-runs s n k (Zero) k r (RunsHalt) (add-zero-right k))) used) sp) 0))
        ((Stuck) (CCrashed _))
        ((Next _ n2 st1) (CGo _ (Running _ t g used s n2 (Succ k) (ReachStep s n n2 k r st1) sp) 0))))
    ((Committing _ _ g v g2 p sp)
      (let-match many sp (SpRight l r _ g0 _ a pa up)
        ((SpTop _) (CFinished _ v g2 p))
        ((SpLeft _ _ _ r2 up2) (CGo _ (Sequencing _ r2 g2 (SpRight _ _ _ _ _ v p up2)) 0)))
      (let ((many c) (erased pc)) (add a v))
      (CGo _ (Committing _ _ _ c g2 (ENode l r g0 a g v g2 c pa p pc) up) 0))))

(def-lvl drive-lvl)
(def-lvl P)

(def-fns drive-lvl $ (many drive : (unique (World) w at vacant-slot) (many (Tree) t) (many (CState t) st) (many (Nat) calls steps) -> (unique (World) w2 at w) (unique (Program P) p))
  (match many (cturn _ st) _
    ((CGo _ st2 c)
      (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
        (drive v t st2 (nat-add calls c) (Succ steps)))
      (values w (Continue P again)))
    ((CFinished _ v g2 p)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut (report t v g2 "elab-calls" calls (Succ steps) p))))
      (values w1 (Exit P code0)))
    ((CCrashed _)
      (let ((unique w1) (many _)) (world-do _ w (WriteErr "machine stuck\n")))
      (values w1 (Exit P code2)))))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many t)) (tree-of-args args))
  (drive w1 t (Sequencing _ t (Zero) (SpTop _)) 0 0))

(Continue P start)
