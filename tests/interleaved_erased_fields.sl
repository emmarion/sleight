; needs: list
; expect: (Succ (Succ (Zero)))
; A constructor with an erased field between two many fields: match and comptime-match
; project the many fields by position, skipping the erased one.

(def-adts $ Tri : -> Type enum
  (many T3 : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (Tri)))

(let (many v) (T3 (Zero) (Succ (Zero)) (Succ (Succ (Zero)))))
(comptime-match v (T3 a b c))

(def-lvl X)
(def-fns X $ many third : (many (Tri) t) -> (many (Nat) r)
  (match many t (((Nat) x)) ((T3 a b c) c)))
(third v)
