(let ((erased m)) (matchable-of Nat))
(def-fns _ $ (many k : (erased (Eq (Matchable enum extern Nat (many Zero) (many Succ)) (matchable-of Nat) m) e) ->
    (many (Nat) r))
  (Zero))
(k (Refl _ _))
