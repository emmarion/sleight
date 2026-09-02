; needs: list
; expect: (Succ (Zero))
; A special form renamed inside a function body still dispatches (section 9's inheritance into bodies).

(def-lvl X)
(def-fns X $ many f : (many (Nat) n) -> (many (Nat) m)
  (let (many define) let)
  (define (many k) (Succ n))
  k)
(f (Zero))
