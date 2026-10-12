; def-adts signatures mentioning top-level entries: a level, a function, a typed let and a let of a term
(def-adts
  ((Eq : (Type A) (A x) (A y) -> Type)
    enum
    (many Refl : (erased Type A) (many A x) -> (Eq A x x))))
(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(let ((many (Nat) two)) (Succ (Succ (Zero))))
(let ((erased N)) (Nat))
(def-adts
  ((Box : -> Type)
    enum
    (many MkBox : (many (Fn L (many N n) -> (many N m)) f) (many (Eq N two two) e) -> (Box))))
(def-lvl M)
(let ((erased p)) (prove-predates L M))
(def-fns M $ (many apply : (many (Box) b) (many N x) -> (many N y))
  (match many b ((N y))
    ((MkBox f e) (f (predates p) x))))
(apply (MkBox inc (Refl N two)) two)
