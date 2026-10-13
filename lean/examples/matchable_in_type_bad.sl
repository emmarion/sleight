(def-adts $ (Two : -> Type)
  enum
  (many A : -> (Two))
  (many B : -> (Two)))
(let ((erased m)) (matchable-of Nat))
(def-fns _ $ (many k : (erased (Eq (Matchable enum extern Nat (many Zero) (many Succ)) (matchable-of Nat) m) e) ->
    (many (Nat) r))
  (Zero))
(let ((erased m2)) (matchable-of Two))
(k (Refl _ m2))
