; A tainted function stays tainted as a first-class value: bound, passed to a function that calls it, or stored
; in data. Taking the stored one back out with a `let-match` taints the rest of the unit.
(def-lvl F)
(def-lvl G)
(def-fns F $ (many worse : (many (Nat) _n) -> (many (Nat) m))
  (sorry _))
(def-fns F $ (many twice : (many (Nat) n) -> (many (Nat) m))
  (Succ (Succ n)))
(def-fns G $ (many call-with : (many (Fn F (many (Nat) x) -> (many (Nat) y)) f) (many (Nat) n) -> (many (Nat) m))
  (f n))
(let ((many h)) worse)
(let ((many h2)) twice)
(MkPair (Nat) (Nat) (call-with twice 1) (h2 1))
;! file "sorry/bound.sl"
(h 1)
;! file "sorry/passed.sl"
(call-with worse 1)
;! file "sorry/stored.sl"
(let ((many box)) (MkPair (Fn F (many (Nat) x) -> (many (Nat) y)) (Nat) worse 3))
(let-match many box (MkPair _ _ _g k))
(MkPair (Nat) (Nat) k k)
; expect: (MkPair _ _ 3 3)
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_first_class.sl:6:3: warning: this unit uses `sorry` once, here; nothing that depends on it runs
