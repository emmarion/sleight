; `values`, `let` and `match` are tainted result by result: an untainted result still runs, a tainted one is
; never computed, whether at run position or in a body.
(let ((many a) (many b)) (values (sorry (((Nat) x))) 3))
(let ((many l) (many r)) (match many 5 (((Nat) l) ((Nat) r))
    ((Zero) (values (sorry (((Nat) x))) 7))
    ((Succ p) (values p 8))))
(def-fns _ $ (many keep-second : (many (Nat) n) -> (many (Nat) m))
  (let ((many _junk) (many kept)) (values (sorry (((Nat) x))) n))
  (Succ kept))
(MkPair (Nat) (Nat) b r)
;! file "sorry/values-body.sl"
(keep-second 4)
;! file "sorry/values-a.sl"
a
;! file "sorry/match-l.sl"
l
; expect: (MkPair _ _ 3 8)
; expect: 5
; expect: sorry
; expect: sorry
; warns: tests/sorry_values.sl:3:34: warning: this unit uses `sorry` 3 times, first here; nothing that depends on it runs
