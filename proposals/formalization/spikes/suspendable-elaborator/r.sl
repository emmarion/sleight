(def-adts $ (RState : -> Type)
  enum
  (many Elaborating : (many (List (Entry)) rev-log) -> (RState))
  (many Running : (many (List (Entry)) used) (many (Nat) s n k) (erased (Reach s n k) r) -> (RState)))

(def-adts $ (Turn : ((Tree) t) -> Type)
  enum
  (many Go : (erased (Tree) t) (many (RState) st) (many (Nat) calls) -> (Turn t))
  (many Finished : (erased (Tree) t) (many (Nat) v g2) (erased (Elab t (Zero) v g2) p) -> (Turn t))
  (many Crashed : (erased (Tree) t) -> (Turn t)))

(def-fns _ $ (many turn : (many (Tree) t) (many (RState) st) -> (many (Turn t) r))
  (match many st _
    ((Elaborating rev-log)
      (match many (elab t (Zero) (rev-onto _ rev-log (Nil _)) (Nil _)) _
        ((Done _ _ v g2 _ _ p) (Finished _ v g2 p))
        ((Need _ _ s used) (Go _ (Running used s s (Zero) (ReachRefl s)) 1))))
    ((Running used s n k r)
      (match many (step n) _
        ((Halted) (Go _ (Elaborating (Cons _ (MkEntry s k (reach-runs s n k (Zero) k r (RunsHalt) (add-zero-right k))) used)) 0))
        ((Stuck) (Crashed _))
        ((Next _ n2 st1) (Go _ (Running used s n2 (Succ k) (ReachStep s n n2 k r st1)) 0))))))

(def-lvl drive-lvl)
(def-lvl P)

(def-fns drive-lvl $ (many drive : (unique (World) w at vacant-slot) (many (Tree) t) (many (RState) st) (many (Nat) calls steps) -> (unique (World) w2 at w) (unique (Program P) p))
  (match many (turn t st) _
    ((Go _ st2 c)
      (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
        (drive v t st2 (nat-add calls c) (Succ steps)))
      (values w (Continue P again)))
    ((Finished _ v g2 p)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut (report t v g2 "elab-calls" (Succ calls) (Succ steps) p))))
      (values w1 (Exit P code0)))
    ((Crashed _)
      (let ((unique w1) (many _)) (world-do _ w (WriteErr "machine stuck\n")))
      (values w1 (Exit P code2)))))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (drive w1 (tree-of-args args) (Elaborating (Nil _)) 0 0))

(Continue P start)
