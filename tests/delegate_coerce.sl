; needs: list
; expect: (Succ (Zero))
; A delegate whose argument and result pass through coerces: both erase to renamings (section 9).

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl L)
(def-fns L $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))
(def-lvl M)
(let (erased p) (prove-predates L M))

(def-fns M $ many inc-meters : (many (Meters) x) -> (many (Meters) r)
  (match erased x (((Meters) r))
    ((MkMeters n)
      (let (many k) (coerce x (coercible-sym (coercible-wrap MkMeters n))))
      (let (many j) (delegate (inc (predates p) k)))
      (coerce j (coercible-wrap MkMeters j)))))

(let (erased ig) (coercible-of inc-meters))
(let (many (Fn L (many (Nat) a) -> (many (Nat) b)) g) (coerce inc-meters ig))
(g (Zero))
