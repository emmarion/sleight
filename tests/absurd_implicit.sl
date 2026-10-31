; needs: list
; expect: (Cons _ 0 $ Cons _ 1 $ Nil _)
; A refuted constructor may be left unlisted, under a many or an erased scrutinee; (absurd C) remains optional.

(def-adts
  ((ZeroProof : ((Nat) n) -> Type)
    enum
    (many ItIsZero : -> (ZeroProof (Zero)))
    (many IsTwo : (erased (Nat) k) -> (ZeroProof (Succ (Succ k))))
    (many IsThree : (erased (Nat) k) -> (ZeroProof (Succ (Succ (Succ k)))))))

(def-lvl X)

(def-fns X $ (many g : (many (ZeroProof (Zero)) p) -> (many (Nat) m))
  (match many p (((Nat) r))
    ((ItIsZero) (Zero))))

(def-fns X $ (many h : (erased (ZeroProof (Zero)) p) -> (many (Nat) m))
  (match erased p (((Nat) r))
    ((ItIsZero) (Succ (Zero)))
    (absurd IsTwo)))

(Cons (Nat) (g (ItIsZero)) $ Cons (Nat) (h (ItIsZero)) $ Nil (Nat))
