; A `delegate` body is checked as it would be with a value in place of the `sorry`: one that delegates to a
; tainted function is tainted, and so is what fetches its `Delegate` proof; a call of an untainted one is
; tainted by its arguments alone.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many worse : (many (Nat) n) -> (many (Nat) m))
  (nat-add n (sorry _)))
(def-lvl V)
(def-fns V $ (many worse2 at worse : (many (Nat) n) -> (many (Nat) m))
  (delegate (worse n)))
(def-fns V $ (many inc2 at inc : (many (Nat) n) (erased (Nat) _k) -> (many (Nat) m))
  (delegate (inc n)))
(def-fns _ $ (many through : (many (Nat) n) -> (many (Nat) m))
  (let ((many g)) (coerce worse2 (coercible-of (delegate-of worse2))))
  (g n))
(inc2 4 (sorry _))
;! file "sorry/delegate.sl"
(MkPair (Nat) (Nat) (inc2 1 0) (worse2 3))
;! file "sorry/delegate-of.sl"
(through 3)
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_delegate.sl:7:14: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
