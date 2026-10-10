; needs: list
; expect: _
; A Nat whose discriminant is erased: each constructor is told from the others by the index alone, and
; USucc wraps its predecessor at no cost, so a UNat is UZero's slot however large the index, and that is
; all a printer can show of it. Generating the printer must skip the constructors the index refutes.

(def-adts
  ((UNat : ((Nat) n) -> Type)
    union newtype
    (many UZero : (many (Slot) s) -> (UNat (Zero)))
    (many USucc : (erased (Nat) m) (many (UNat m) pred) -> (UNat (Succ m)))))

(def-lvl L)
(def-fns L $ (many two : -> (many (UNat (Succ (Succ (Zero)))) r))
  (USucc (Succ (Zero)) (USucc (Zero) (UZero vacant-slot))))

two
