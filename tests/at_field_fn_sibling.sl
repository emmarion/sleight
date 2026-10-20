; expect: (MySucc $ MyZero)
; A field's function type that returns the sibling slot field and promises its result `at` that return,
; built from a closure, destructured, called, the returned slot made its own by `slot-self`, and the result
; returned `at` the original.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-lvl K)
(def-adts $ (Holder : ((Slot) s) -> Type) enum
  (many MkHolder : (many (Slot) s) (many (Fn K (many (Nat) y) -> (many s is q) (many (MyNat) r at q)) f) -> (Holder s)))
(def-fns _ $ (many go : (many (MyNat) n) -> (many (MyNat) r at n))
  (def-fns K $ (many get : (many (Nat) _y) -> (many (slot-of n) is q) (many (MyNat) r at q)) (values (slot-of n) n))
  (let ((unique h)) (MkHolder (slot-of n) get))
  (let-match unique h (MkHolder _ f))
  (let ((erased q) (many r)) (f 0))
  (slot-self q)
  r)
(go (MySucc (MyZero)))
