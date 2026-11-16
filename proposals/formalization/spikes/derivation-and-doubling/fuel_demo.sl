(def-fns _ $ (many plus : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) s) (erased (Plus a b s) p))
  (let-match many a (Succ a2) ((Zero) (values b (PlusZ b))))
  (let ((many s2) (erased p2)) (notail $ plus a2 b))
  (values (Succ s2) (PlusS a2 b s2 p2)))

(def-fns _ $ (many rerun-with-more : (many (Nat) n) (many (Nat) k) (many (Env) env) (many (Core) c) -> (many (Maybe (List (Val))) r))
  (let-match many (run n env c) (Done _ _ _ vs d) ((Failed _ _ _ _ _) (None _)))
  (let ((many m) (erased pl)) (plus k n))
  (Some _ (fuel-is-unobservable k n m env c vs pl d (run m env c))))

(MkPair _ _ (rerun-with-more 16 1000 (ENil) program) (rerun-with-more 8 1000 (ENil) program))
