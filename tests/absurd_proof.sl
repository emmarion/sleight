; needs: list absurd
; expect: 0
; An absurd-by-proof branch produces a False from a refuting function.

(def-adts
  ((IsZero : ((Nat) n) -> Type)
    enum
    (many ItIsZero : -> (IsZero (Zero)))))

(def-lvl Y)

(def-fns Y $ (many absurd succ-not-zero : (erased (Nat) k) (many (IsZero (Succ k)) p) -> (many (False) f))
  p)

(def-lvl Z)
(let ((erased pz)) (prove-predates Y Z))

(def-fns Z $ (many get : (many (Nat) n) (erased (IsZero n) p) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) (Zero))
    (absurd (Succ k) (succ-not-zero (predates pz) k p))))

(get (Zero) (ItIsZero))
; warns: tests/absurd_proof.sl:21:37: warning: unnecessary `(predates _)`; drop it
