; needs: list vec
; expect: 0
; Reasoning through the Numeral relation by hand: numeral-succ over a BinSucc witness gives an Eq the let-match
; carries outward, and numeral-inj's Eq between two differing spellings refutes a branch vacuously.

(let-match erased
  (numeral-succ (B2 (B1 (BZ))) (B1 (B2 (BZ))) 4 5
    (BS2 (B1 (BZ)) (B2 (BZ)) (BS1 (BZ)))
    (numeral-of 4) (numeral-of 5))
  (Refl nt nr))

(def-lvl X)
(def-fns X $ (many first : (erased Type A) (many (Vec A 5) v) -> (many A x))
  (match many v ((A r))
    (absurd VNil)
    ((VCons _ _ x _) x)))

(def-adts ((Tag : ((Nat) n) -> Type) enum (many TA : -> (Tag 0)) (many TB : -> (Tag 1))))

(def-fns X $ (many only-a : (many (Tag 0) t) -> (many (Nat) r))
  (match many t (((Nat) r))
    ((TA) (Zero))
    (absurd (TB)
      (match erased (numeral-inj (predates _) (BZ) (B1 (BZ)) 0 (numeral-of 0) (numeral-of 1))
        (((False) f))
        (absurd Refl)))))

(only-a (TA))
; warns: tests/numeral_lemmas.sl:24:34: warning: unnecessary `(predates _)`; drop it
