; A tainted position leaves no code, as an erased one leaves none: a partly tainted `match`, `values` or `let`
; runs for its untainted results alone, in a body and at run position, and a wholly tainted one does not run.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many strip : (many (Nat) n) -> (many (Nat) m))
  (let ((many junk) (many kept)) (match many n (((Nat) a) ((Nat) b))
    ((Zero) (values (sorry (((Nat) x))) (inc n)))
    ((Succ p) (values p (inc p)))))
  (let ((many _j2) (many k2) (many _j3)) (values (sorry (((Nat) x))) (inc kept) (inc junk)))
  (let ((many t)) (sorry (((Nat) x))))
  (let ((many _u)) (inc t))
  (let ((many w)) (match many k2 (((Nat) r))
    ((Zero) 0)
    ((Succ q) (let ((many _d)) (inc t)) (inc q))))
  w)
(def-fns _ $ (many main : -> (many (Pair (Nat) (Nat)) r))
  (MkPair _ _ (strip 0) (strip 4)))
main
;! file "sorry/strip-run.sl"
(let ((many junk) (many kept)) (match many 3 (((Nat) a) ((Nat) b))
    ((Zero) (values (sorry (((Nat) x))) 7))
    ((Succ p) (values p (inc p)))))
(let ((many _j2) (many k2) (many _j3)) (values (sorry (((Nat) x))) (inc kept) (inc junk)))
(let ((many _w)) (match many junk (((Nat) r)) ((Zero) 0) ((Succ q) q)))
(MkPair _ _ kept k2)
;! file "sorry/strip-junk.sl"
junk
; expect: (MkPair _ _ 2 5)
; expect: (MkPair _ _ 3 4)
; expect: sorry
; warns: tests/sorry_strip.sl:7:21: warning: this unit uses `sorry` 5 times, first here; nothing that depends on it runs
