; error: has no `Matchable` open
(def-adts $ (U : -> Type) union
  (many A : (many (Nat) n) -> (U))
  (many B : (many (Nat) n) (erased (False) p) -> (U)))
(def-fns _ $ (many hide : (many (U) u) ->
    (erased (TyCtor -> Type) T) (many (ValCtor (many (Nat) n) (erased (False) p) -> (T)) C) (many (T) x))
  (values U B u))
(goal erased (False))
(let ((erased T) (many C) (many x)) (hide (A 1)))
(comptime-match many x (C n p))
(qed p)
