(def-lvl L)
(def-fns L $ (many apply : (erased Type A) (many (ValCtor (erased Type B) (many B h) (many (List B) t) -> (List B)) c) (many A x) (many (List A) xs) -> (many (List A) r))
  (c A x xs))
(apply (Nat) Nil (Zero) (Nil (Nat)))
