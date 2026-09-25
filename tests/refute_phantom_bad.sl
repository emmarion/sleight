; error: `g` : `(Ghost)` is not refuted: it may be headed by `G`

(def-adts $ (Ghost : -> Type)
  enum
  (erased G : -> (Ghost)))

(def-lvl X)

(def-fns X $ (many absurd boo : (many (Ghost) g) -> (many (Nat) x))
  g)
