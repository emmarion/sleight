; expect: 0
; The `else` binder under an erased scrutinee (section 23) is at the scrutinee.
(def-fns _ $ (erased f : (many (List (Nat)) xs) -> (many (List (Nat)) r at xs))
  (match erased xs (((List (Nat)) r at xs)) ((Nil _) xs) (else y y)))
0
