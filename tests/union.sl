; needs: list
; expect: 1
; A union indexed by a Bool: matching in a non-erased position needs one real branch.

(def-adts
  ((Either : ((Bool) tag) -> Type)
    union
    (many L : (many (Nat) n) -> (Either (BTrue)))
    (many R : (many (Bool) b) -> (Either (BFalse)))))

(def-lvl union-lvl)

(def-fns union-lvl $ (many get-left : (many (Either (BTrue)) e) -> (many (Nat) n))
  (match many e (((Nat) r))
    ((L n) n)
    (absurd R)))

(get-left (L (Succ (Zero))))
