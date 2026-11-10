; A `delegate` call that is tainted leaves no call behind; the function is tainted rather than refused, and so
; is what fetches its `Delegate` proof. It is at its callee's slot, where an `at` result is not read from it.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-lvl V)
(def-fns V $ (many inc2 at inc : (many (Nat) _n) -> (many (Nat) m))
  (delegate (inc (sorry _))))
(def-fns _ $ (many through : (many (Nat) n) -> (many (Nat) m))
  (let ((many g)) (coerce inc2 (coercible-of (delegate-of inc2))))
  (g n))
(def-fns _ $ (many same : (many (Slot) s) (many (Fn (level-of inc) (many (Nat) n) -> (many (Nat) m)) a at s) ->
    (many (Fn (level-of inc) (many (Nat) n) -> (many (Nat) m)) r at s))
  a)
(let ((many h)) (same (slot-of inc) inc))
(h 4)
;! file "sorry/delegate.sl"
(MkPair (Nat) (Nat) (inc 1) (inc2 3))
;! file "sorry/delegate-of.sl"
(through 3)
; expect: 5
; expect: sorry
; expect: sorry
; warns: tests/sorry_delegate.sl:7:18: warning: this unit uses `sorry` once, here; nothing that depends on it runs
