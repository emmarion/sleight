(def-lvl O)

(def-adts $ (Asked : (Type S) (Type F) ((Nat) s) -> Type)
  enum
  (many Answer : (erased Type S F) (erased (Nat) s) (many S st) (many (Nat) a) (erased (Runs s a) p) -> (Asked S F s))
  (many Unanswered : (erased Type S F) (erased (Nat) s) (many F f) -> (Asked S F s)))

(def-adts $ (Outcome : (Type S) (Type F) ((Tree) t) ((Nat) g) -> Type)
  enum
  (many Done : (erased Type S F) (erased (Tree) t) (erased (Nat) g) (many (Nat) v g2) (many S st) (erased (Elab t g v g2) p) -> (Outcome S F t g))
  (many Need : (erased Type S F) (erased (Tree) t) (erased (Nat) g) (many F f) -> (Outcome S F t g)))

(def-fns _ $ (many elab : (erased Type S F) (many (Fn O (many S st) (many (Nat) s) -> (many (Asked S F s) r)) ask)
    (subterm many (Tree) t) (many (Nat) g) (many S st) -> (many (Outcome S F t g) r))
  (match many t _
    ((TLeaf n) (Done _ _ _ _ n g st (ELeaf n g)))
    ((TGen) (Done _ _ _ _ g (Succ g) st (EGen g)))
    ((TNode l r)
      (let-match many (notail $ elab _ _ ask l g st) (Done _ _ _ _ a g1 st1 pa) ((Need _ _ _ _ f) (Need _ _ _ _ f)))
      (let-match many (notail $ elab _ _ ask r g1 st1) (Done _ _ _ _ b g2 st2 pb) ((Need _ _ _ _ f) (Need _ _ _ _ f)))
      (let ((many c) (erased pc)) (add a b))
      (Done _ _ _ _ c g2 st2 (ENode l r g a g1 b g2 c pa pb pc)))
    ((TRun s)
      (match many (ask st s) _
        ((Answer _ _ _ st1 a p) (Done _ _ _ _ a g st1 (ERun s a g p)))
        ((Unanswered _ _ _ f) (Need _ _ _ _ f))))
    ((TIf c th el)
      (let-match many (notail $ elab _ _ ask c g st) (Done _ _ _ _ v g1 st1 pc) ((Need _ _ _ _ f) (Need _ _ _ _ f)))
      (match many (nat-zero-dec v) _
        ((IsZero)
          (let-match many (notail $ elab _ _ ask th g1 st1) (Done _ _ _ _ b g2 st2 pt) ((Need _ _ _ _ f) (Need _ _ _ _ f)))
          (Done _ _ _ _ b g2 st2 (EIfZero c th el g g1 b g2 pc pt)))
        ((IsSucc m)
          (let-match many (notail $ elab _ _ ask el g1 st1) (Done _ _ _ _ b g2 st2 pe) ((Need _ _ _ _ f) (Need _ _ _ _ f)))
          (Done _ _ _ _ b g2 st2 (EIfSucc c th el g m g1 b g2 pc pe)))))))

(def-fns _ $ (erased total-under-h : (many (Fn O (many (Unit) u) (many (Nat) s) -> (many (Asked (Unit) (False) s) r)) h) (many (Tree) t) (many (Nat) g) ->
    (erased (Nat) v g2) (erased (Elab t g v g2) p))
  (match erased (elab _ _ h t g (MkUnit)) _
    ((Done _ _ _ _ v g2 _ p) (values v g2 p))
    (absurd (Need _ _ _ _ f) f)))

(def-adts $ (Entry : -> Type)
  enum
  (many MkEntry : (many (Nat) s a) (erased (Runs s a) p) -> (Entry)))

(def-adts $ (Cursor : -> Type)
  enum
  (many MkCursor : (many (Nat) quantum) (many (List (Entry)) rest used) -> (Cursor)))

(def-adts $ (Pending : -> Type)
  enum
  (many Paused : (many (List (Entry)) used) (many (Nat) s n k) (erased (Reach s n k) r) -> (Pending))
  (many Crash : -> (Pending)))

(def-fns _ $ (many try-run : (subterm many (Nat) quantum) (many (Cursor) c) (many (List (Entry)) used) (many (Nat) s n k) (erased (Reach s n k) r) ->
    (many (Asked (Cursor) (Pending) s) a))
  (let-match many quantum (Succ q) ((Zero) (Unanswered _ _ _ (Paused used s n k r))))
  (match many (step n) _
    ((Halted) (Answer _ _ _ c k (reach-runs s n k (Zero) k r (RunsHalt) (add-zero-right k))))
    ((Stuck) (Unanswered _ _ _ (Crash)))
    ((Next _ n2 st1) (tail $ try-run q c used s n2 (Succ k) (ReachStep s n n2 k r st1)))))

(def-fns O $ (many from-log : (many (Cursor) c) (many (Nat) s) -> (many (Asked (Cursor) (Pending) s) r))
  (let-match many c (MkCursor quantum log used))
  (let-match many log (Cons _ e rest) ((Nil _) (try-run quantum c used s s (Zero) (ReachRefl s))))
  (let-match many e (MkEntry s2 a p))
  (let-match many (nat-eq s2 s) (Equal _ _ _) ((Unequal _ _ _ _ _) (try-run quantum c used s s (Zero) (ReachRefl s))))
  (Answer _ _ _ (MkCursor quantum rest (Cons _ e used)) a p))

(MkUnit)
