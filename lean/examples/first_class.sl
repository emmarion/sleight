; DESIGN.md section 24: type and value constructors as values
(def-adts
  ((Eq : (Type A) (A x) (A y) -> Type)
    enum
    (many Refl : (erased Type A) (many A x) -> (Eq A x x))))
(def-lvl L)
(def-fns L $ (many twice : (erased Type A) (many (ValCtor (erased Type B) (many B h) (many (List B) t) -> (List B)) c) (many A x) (many (List A) xs) -> (many (List A) r))
  (c A x (c A x xs)))
(def-fns L $ (many wrap : (erased (TyCtor (Type A) -> Type) F) (erased Type A) (many (F A) x) -> (many (F A) y))
  x)
(def-fns L $ (many never : (many (ValCtor (many (Nat) n) -> (Nat)) c) (many (Eq (Nat) (c (Zero)) (Zero)) e) -> (many (Nat) r))
  (match many e (((Nat) r))))
(let ((many s)) Succ)
(Cons (List (Nat)) (twice (Nat) Cons (Zero) (Nil (Nat))) (Cons (List (Nat)) (wrap List (Nat) (Cons (Nat) (s (Zero)) (Nil (Nat)))) (Nil (List (Nat)))))
