; expect: 0
; A mark written twice in a Matchable type counts once (section 24).

(def-adts $ (Box : -> Type) enum newtype
  (many MkBox : (many (Nat) n) -> (Box)))
(let ((many (Matchable enum newtype newtype Box (many MkBox)) m))
  (matchable-of Box))
0
