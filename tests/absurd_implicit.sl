; needs: list
; expect: (Cons _ 0 $ Cons _ 1 $ Nil _)
; A refuted constructor may be left unlisted, under a many or an erased scrutinee; (absurd C) remains optional.

(def-adts
  ((IsZero : ((Nat) n) -> Type)
    enum
    (many ItIsZero : -> (IsZero (Zero)))
    (many IsTwo : (erased (Nat) k) -> (IsZero (Succ (Succ k))))
    (many IsThree : (erased (Nat) k) -> (IsZero (Succ (Succ (Succ k)))))))

(def-lvl X)

(def-fns X $ (many g : (many (IsZero (Zero)) p) -> (many (Nat) m))
  (match many p (((Nat) r))
    ((ItIsZero) (Zero))))

(def-fns X $ (many h : (erased (IsZero (Zero)) p) -> (many (Nat) m))
  (match erased p (((Nat) r))
    ((ItIsZero) (Succ (Zero)))
    (absurd IsTwo)))

(Cons (Nat) (g (ItIsZero)) $ Cons (Nat) (h (ItIsZero)) $ Nil (Nat))
