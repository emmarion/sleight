; needs: list union
; expect: (Succ (Zero))
; An indexed union marked newtype: its other non-phantom constructors have only erased fields (section 38).
; MkA wraps a Nat at no cost, and a NoB value is the null.

(def-adts
  (Tagged : ((Bool) k) -> Type
    union newtype
    (many MkA : (many (Nat) n) -> (Tagged (True)))
    (many NoB : -> (Tagged (False)))))

(def-lvl X)
(def-fns X $ many get : (many (Tagged (True)) t) -> (many (Nat) n)
  (match many t (((Nat) r))
    ((MkA n) n)
    (absurd NoB)))

(let (many one) (Succ (Zero)))
(let (many (Tagged (True)) a) (coerce one (coercible-wrap MkA one)))
(let (many nb) (NoB))
(get a)
