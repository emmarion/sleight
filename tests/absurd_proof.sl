; needs: list absurd
; expect: (Zero)
; An absurd-by-proof branch produces a False from a refuting function.

(def-adts
  (IsZero : ((Nat) n) -> Type
    enum
    (many ItIsZero : -> (IsZero (Zero)))))

(def-lvl Y)

(def-fns Y $ many succ-not-zero : (erased (Nat) k) (many (IsZero (Succ k)) p) -> (many (False) f)
  (match many p (((False) f))
    (absurd ItIsZero)))

(def-lvl Z)
(let (erased pz) (prove-predates Y Z))

(def-fns Z $ many get : (many (Nat) n) (erased (IsZero n) p) -> (many (Nat) m)
  (match many n (((Nat) r))
    ((Zero) (Zero))
    (absurd (Succ k) (succ-not-zero (predates pz) k p))))

(get (Zero) (ItIsZero))
