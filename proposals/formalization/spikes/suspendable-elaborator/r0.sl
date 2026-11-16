(def-adts $ (Outcome0 : -> Type)
  enum
  (many Done0 : (many (Nat) v g2) (many (List (Nat)) rest) -> (Outcome0))
  (many Need0 : (many (Nat) s) -> (Outcome0)))

(def-fns _ $ (many elab0 : (subterm many (Tree) t) (many (Nat) g) (many (List (Nat)) log) -> (many (Outcome0) r))
  (match many t _
    ((TLeaf n) (Done0 n g log))
    ((TGen) (Done0 g (Succ g) log))
    ((TNode l r)
      (let-match many (notail $ elab0 l g log) (Done0 a g1 log1) (else o o))
      (let-match many (notail $ elab0 r g1 log1) (Done0 b g2 log2) (else o o))
      (Done0 (nat-add a b) g2 log2))
    ((TRun s)
      (let-match many log (Cons _ a rest) ((Nil _) (Need0 s)))
      (Done0 a g rest))
    ((TIf c th el)
      (let-match many (notail $ elab0 c g log) (Done0 v g1 log1) (else o o))
      (match many (nat-zero-dec v) _
        ((IsZero) (tail $ elab0 th g1 log1))
        ((IsSucc _) (tail $ elab0 el g1 log1))))))

(def-fns _ $ (many rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) r))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (tail $ rev-onto A rest (Cons A x acc)))

(def-adts $ (RState0 : -> Type)
  enum
  (many Elaborating0 : (many (List (Nat)) rev-log) -> (RState0))
  (many Running0 : (many (List (Nat)) rev-log) (many (Nat) n k) -> (RState0)))

(def-adts $ (Turn0 : -> Type)
  enum
  (many Go0 : (many (RState0) st) (many (Nat) calls) -> (Turn0))
  (many Finished0 : (many (Nat) v g2) -> (Turn0))
  (many Crashed0 : -> (Turn0)))

(def-fns _ $ (many turn0 : (many (Tree) t) (many (RState0) st) -> (many (Turn0) r))
  (match many st _
    ((Elaborating0 rev-log)
      (match many (elab0 t (Zero) (rev-onto _ rev-log (Nil _))) _
        ((Done0 v g2 _) (Finished0 v g2))
        ((Need0 s) (Go0 (Running0 rev-log s (Zero)) 1))))
    ((Running0 rev-log n k)
      (match many (step n) _
        ((Halted) (Go0 (Elaborating0 (Cons _ k rev-log)) 0))
        ((Stuck) (Crashed0))
        ((Next _ n2 _) (Go0 (Running0 rev-log n2 (Succ k)) 0))))))

(def-lvl drive-lvl)
(def-lvl P)

(def-fns drive-lvl $ (many drive : (unique (World) w at vacant-slot) (many (Tree) t) (many (RState0) st) (many (Nat) calls steps) -> (unique (World) w2 at w) (unique (Program P) p))
  (match many (turn0 t st) _
    ((Go0 st2 c)
      (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
        (drive v t st2 (nat-add calls c) (Succ steps)))
      (values w (Continue P again)))
    ((Finished0 v g2)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut (report0 v g2 "elab-calls" (Succ calls) (Succ steps)))))
      (values w1 (Exit P code0)))
    ((Crashed0)
      (let ((unique w1) (many _)) (world-do _ w (WriteErr "machine stuck\n")))
      (values w1 (Exit P code2)))))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (drive w1 (tree-of-args args) (Elaborating0 (Nil _)) 0 0))

(Continue P start)
