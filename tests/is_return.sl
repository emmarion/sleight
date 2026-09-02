; needs: list
; expect: (Succ (Zero))
; Reifying an erased index through an is return (section 14).

(def-adts
  (Sing : ((Nat) n) -> Type
    enum
    (many SZero : -> (Sing (Zero)))
    (many SSucc : (erased (Nat) m) (many (Sing m) s) -> (Sing (Succ m)))))

(def-lvl X)

(def-fns X $ many reify : (erased (Nat) n) (subterm many (Sing n) s) -> (many n is m)
  (match many s ((n is m))
    ((SZero) (Zero))
    ((SSucc k t)
      (let (erased p) (prove-subterm t s))
      (Succ (reify k (subterm p) t)))))

(reify (Succ (Zero)) (SSucc (Zero) (SZero)))
