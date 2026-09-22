; needs: list
; expect: 1
; A union indexed by a Bool: matching in a non-erased position needs one real branch.

(def-adts $ (Bool : -> Type)
  enum
  (many True : -> (Bool))
  (many False : -> (Bool)))

(def-adts
  ((Either : ((Bool) tag) -> Type)
    union
    (many L : (many (Nat) n) -> (Either (True)))
    (many R : (many (Bool) b) -> (Either (False)))))

(def-lvl X)

(def-fns X $ (many get-left : (many (Either (True)) e) -> (many (Nat) n))
  (match many e (((Nat) r))
    ((L n) n)
    (absurd R)))

(get-left (L (Succ (Zero))))
