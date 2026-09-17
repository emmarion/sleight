; needs: list
; expect: 0
; An erased let may mention erased names; it compiles to nothing.

(def-lvl X)
(def-fns X $ many f : (erased (Nat) n) -> (many (Nat) m)
  (let (erased k) (Succ n))
  (Zero))
(f (Zero))
