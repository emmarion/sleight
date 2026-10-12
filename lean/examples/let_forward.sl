(def-adts
  ((Vec : (Type A) ((Nat) n) -> Type)
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (many (Nat) n) (many A x) (many (Vec A n) xs) -> (Vec A (Succ n)))))
(let ((erased N)) (Nat))
(def-lvl L)
(let ((erased K)) L)
(def-fns K $ (many pred : (many N n) -> (many N r))
  (let ((many m)) (Succ n))
  (match many m ((N r))
    ((Succ k) k)))
(let ((many two)) (Succ (Succ (Zero))))
(let ((many also)) two)
(let ((many v)) (VCons N (Zero) (pred also) (VNil N)))
v
