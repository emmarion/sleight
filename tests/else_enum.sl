; needs: list
; expect: (Cons (Succ (Zero)) (Cons (Zero) (Cons (Zero) (Cons (Succ (Succ (Zero))) (Nil)))))
; An else branch on a tagged enum: it covers every constructor not listed, binds nothing, and dispatches on the tag.

(def-adts $ Color : -> Type
  enum
  (many Red : -> (Color))
  (many Green : -> (Color))
  (many Blue : (many (Nat) shade) -> (Color)))

(def-lvl X)

(def-fns X $ many is-red : (many (Color) c) -> (many (Nat) n)
  (match many c (((Nat) r))
    ((Red) (Succ (Zero)))
    (else (Zero))))

(def-fns X $ many shade : (many (Color) c) -> (many (Nat) n)
  (match many c (((Nat) r))
    ((Blue s) s)
    (else (Zero))))

(Cons (Nat) (is-red (Red)) $ Cons (Nat) (is-red (Green)) $ Cons (Nat) (is-red (Blue (Succ (Succ (Zero)))))
  $ Cons (Nat) (shade (Blue (Succ (Succ (Zero))))) $ Nil (Nat))
