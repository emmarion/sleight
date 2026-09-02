; error: branch MkFoo is refuted
; Two def-lvl levels are distinct, so a type index naming one refutes a constructor whose return names another;
; before levels were born rigid the branch was accepted with Q aliased to P, and a Q-level body inside it could
; call a newer level (ASSUMPTIONS.md).

(def-lvl Q)
(def-lvl R)
(def-lvl P)
(let (erased rp) (prove-predates R P))
(def-fns R $ many at-r : (many (Nat) n) -> (many (Nat) m) (Succ n))
(def-adts (Foo : ((Level) L) -> Type enum (many MkFoo : -> (Foo P))))
(def-fns Q $ many at-q : (many (Foo Q) x) (many (Nat) n) -> (many (Nat) m)
  (match many x _
    ((MkFoo) (at-r (predates rp) n))))
(Zero)
