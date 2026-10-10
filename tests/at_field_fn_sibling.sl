; expect: (MySucc $ MyZero)
; A field's function type written `at` the sibling slot field (section 36's nested rule), built from a
; closure, destructured, the slot made its own by `slot-self`, called, and the result returned `at` the original.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-lvl K)
(def-adts $ (Holder : ((Slot) s) -> Type) enum
  (many MkHolder : (many (Slot) s) (many (Fn K (many (Nat) y) -> (many (MyNat) r at s)) f) -> (Holder s)))
(def-fns _ $ (many go : (many (MyNat) n) -> (many (MyNat) r at n))
  (def-fns K $ (many get : (many (Nat) y) -> (many (MyNat) r at n)) n)
  (let ((unique h)) (MkHolder (slot-of n) get))
  (let-match unique h (MkHolder s f))
  (slot-self s)
  (f 0))
(go (MySucc (MyZero)))
