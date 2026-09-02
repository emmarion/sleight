; needs: list
; error: value mismatch

(def-adts
  (Sing : ((Nat) n) -> Type
    enum
    (many SZero : -> (Sing (Zero)))
    (many SSucc : (erased (Nat) m) (many (Sing m) s) -> (Sing (Succ m)))))

(def-lvl X)

(def-fns X $ many reify : (erased (Nat) n) (many (Sing n) s) -> (many n is m)
  (match many s ((n is m))
    ((SZero) (Succ (Zero)))
    ((SSucc k t) (Zero))))
