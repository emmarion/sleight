; needs: list
; expect: (SSucc _ (SZero))
; A return telescope whose second entry depends on the first.

(def-adts
  (Sing : ((Nat) n) -> Type
    enum
    (many SZero : -> (Sing (Zero)))
    (many SSucc : (erased (Nat) m) (many (Sing m) s) -> (Sing (Succ m)))))

(def-lvl X)
(def-fns X $ many one-sing : -> (erased (Nat) n) (many (Sing n) s)
  (values (Succ (Zero)) (SSucc (Zero) (SZero))))

(let (erased n) (many s) (one-sing))
(let (many (Sing n) s2) s)
s2
