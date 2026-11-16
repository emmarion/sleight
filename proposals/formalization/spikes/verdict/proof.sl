(def-fns _ $ (many decide : (many (Nat) d) (subterm many (List (Tok)) ts) -> (many (Verdict d ts) v))
  (let-match many ts (Cons _ t rest)
    ((Nil _)
      (match many d _
        ((Zero) (Accepted _ _ (AccEnd)))
        ((Succ k) (Rejected _ _ (FailUnclosed k))))))
  (let-match many t (Close)
    ((Open)
      (match many (notail $ decide (Succ d) rest) _
        ((Accepted _ _ p) (Accepted _ _ (AccOpen d rest p)))
        ((Rejected _ _ p) (Rejected _ _ (FailOpen d rest p))))))
  (let-match many d (Succ k) ((Zero) (Rejected _ _ (FailExtraClose rest))))
  (match many (notail $ decide k rest) _
    ((Accepted _ _ p) (Accepted _ _ (AccClose k rest p)))
    ((Rejected _ _ p) (Rejected _ _ (FailClose k rest p)))))

(def-fns _ $ (erased exclusive : (erased (Nat) d) (erased (List (Tok)) ts) (subterm erased (Accepts d ts) p) (erased (Fails d ts) q) -> (erased (False) f))
  (match erased p _
    ((AccEnd) (match erased q _))
    ((AccOpen d2 rest p2) (match erased q _ ((FailOpen _ _ q2) (exclusive (Succ d2) rest p2 q2))))
    ((AccClose d2 rest p2) (match erased q _ ((FailClose _ _ q2) (exclusive d2 rest p2 q2))))))
