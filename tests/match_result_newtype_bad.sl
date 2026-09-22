; error: type mismatch

(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box))
  (many Other : -> (Box)))

(let ((erased w))
  (match erased (Zero) (((Matchable enum newtype Box (many MkBox)) w))
    (else (matchable-of Box))))

(let ((many one)) (Succ (Zero)))
(let ((many n)) (coerce (MkBox one) (coercible-sym (coercible-wrap (Shared) MkBox one))))
n
