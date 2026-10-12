; DESIGN.md section 21's else branch
(def-adts
  ((Color : -> Type)
    enum
    (many Red : -> (Color))
    (many Green : -> (Color))
    (many Blue : -> (Color))))
(def-lvl L)
(def-fns L $ (many isRed : (many (Color) c) -> (many (Nat) r))
  (match many c (((Nat) r))
    ((Red) (Succ (Zero)))
    (else (Zero))))
(def-fns L $ (many pred : (many (Nat) n) -> (many (Nat) r))
  (let ((many m)) (Succ n))
  (match many m (((Nat) r))
    (else n)))
(Cons (Nat) (isRed (Red)) (Cons (Nat) (isRed (Blue)) (Cons (Nat) (pred (Zero)) (Nil (Nat)))))
