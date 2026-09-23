; expect: 3
; The same quotient by structural recursion on the dividend alone, counting the divisor down beside it,
; so no proof is returned or composed. (struct-div n m) divides n by (Succ m).

(def-lvl D)
(def-fns D $ (many div-helper : (many (Nat) k) (many (Nat) m) (subterm many (Nat) n) (many (Nat) j) -> (many (Nat) q))
  (match many n _
    ((Zero) k)
    ((Succ n1)
      (match many j _
        ((Zero) (tail $ div-helper (Succ k) m (subterm _) n1 m))
        ((Succ j1) (tail $ div-helper k m (subterm _) n1 j1))))))

(def-lvl E)
(let ((erased de)) (prove-predates D E))
(def-fns E $ (many struct-div : (many (Nat) n) (many (Nat) m) -> (many (Nat) q))
  (div-helper (predates de) (Zero) m n m))

(struct-div 7 1)
