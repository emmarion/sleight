; error: type mismatch: expected `(Eq (Nat) k k)`, got `(Eq (Nat) 3 3)`
; An atom a literal stands for is shown by the literal, ahead of any name bound to it.

(def-fns _ $ (erased g : (many (Nat) k) -> (erased (Eq (Nat) k k) r))
  (let ((erased n)) 3)
  (Refl (Nat) n))
(Zero)
