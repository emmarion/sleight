; needs: list
; expect: 2
; Subterm recursion through an erased argument (section 12).

(def-adts
  (Sing : ((Nat) n) -> Type
    enum
    (many SZero : -> (Sing (Zero)))
    (many SSucc : (erased (Nat) m) (many (Sing m) s) -> (Sing (Succ m)))))

(def-lvl X)
(def-fns X $ many double : (subterm erased (Nat) n) (many (Sing n) s) -> (many (Nat) r)
  (match many s (((Nat) r))
    ((SZero) (Zero))
    ((SSucc k t)
      (let (erased p) (prove-subterm k n))
      (Succ (Succ (double (subterm p) k t))))))

(double (Succ (Zero)) (SSucc (Zero) (SZero)))
